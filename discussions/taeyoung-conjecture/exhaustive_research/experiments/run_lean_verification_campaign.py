"""Run a long Lean verification campaign without failing fast.

Each module in the prepared campaign is built in a fresh Lake invocation.  A
failure or timeout is recorded and the next module is attempted.  State is
written after every module, so invoking this script again resumes the same
campaign and skips successes from the same preparation fingerprint.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import platform
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / "experiments" / "s4_lean_campaign.json"
DEFAULT_RUN_DIR = ROOT / "lean" / "verification_runs" / "s4_long_campaign"


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def atomic_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(path)


def load_json(path: Path, default: Any) -> Any:
    if not path.exists():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def replay_events(path: Path, results: dict[str, Any]) -> None:
    """Recover the latest durable result for every target from JSONL."""
    if not path.exists():
        return
    with path.open("r", encoding="utf-8", errors="replace") as handle:
        for line in handle:
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                # A power loss can truncate only the last append. The previous
                # complete events remain authoritative.
                continue
            key = event.pop("key", None)
            if isinstance(key, str):
                results[key] = event


def target_key(campaign_id: str, item: dict[str, Any]) -> str:
    identity = "\0".join(
        (campaign_id, str(item["stage"]), str(item["tag"]), str(item["target"]))
    )
    return hashlib.sha256(identity.encode("utf-8")).hexdigest()


def safe_log_name(index: int, key: str, item: dict[str, Any]) -> str:
    target = str(item["target"]).split(".")[-1]
    cleaned = "".join(character if character.isalnum() else "_" for character in target)
    return f"{index:06d}_{key[:12]}_{cleaned[:80]}.log"


def lake_target(module: str) -> str:
    if module.startswith("+"):
        return module if ":" in module else f"{module}:olean"
    return f"+{module}:olean"


def resolve_lake(explicit: str | None, lean_dir: Path) -> str:
    if explicit:
        return explicit
    toolchain_file = lean_dir / "lean-toolchain"
    if toolchain_file.exists():
        toolchain = toolchain_file.read_text(encoding="utf-8").strip()
        directory = toolchain.replace("/", "--").replace(":", "---")
        executable = "lake.exe" if os.name == "nt" else "lake"
        direct = Path.home() / ".elan" / "toolchains" / directory / "bin" / executable
        if direct.exists():
            return str(direct)
    return "lake"


def kill_process_tree(process: subprocess.Popen[Any]) -> None:
    if process.poll() is not None:
        return
    if os.name == "nt":
        subprocess.run(
            ["taskkill", "/PID", str(process.pid), "/T", "/F"],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
    else:
        try:
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass


def render_reports(
    run_dir: Path,
    manifest: dict[str, Any],
    selected: list[dict[str, Any]],
    results: dict[str, Any],
) -> None:
    campaign_id = str(manifest["campaign_id"])
    rows: list[dict[str, Any]] = []
    for item in selected:
        key = target_key(campaign_id, item)
        result = results.get(key, {})
        rows.append(
            {
                "stage": item["stage"],
                "tag": item["tag"],
                "target": item["target"],
                "status": result.get("status", "pending"),
                "exit_code": result.get("exit_code", ""),
                "elapsed_seconds": result.get("elapsed_seconds", ""),
                "finished_at": result.get("finished_at", ""),
                "log": result.get("log", ""),
            }
        )

    counts: dict[str, int] = {}
    for row in rows:
        status = str(row["status"])
        counts[status] = counts.get(status, 0) + 1
    summary = {
        "campaign_id": campaign_id,
        "updated_at": utc_now(),
        "selected_targets": len(rows),
        "counts": counts,
        "rows": rows,
    }
    atomic_json(run_dir / "summary.json", summary)

    csv_path = run_dir / "summary.csv"
    temporary_csv = csv_path.with_suffix(".csv.tmp")
    with temporary_csv.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]) if rows else ["status"])
        writer.writeheader()
        writer.writerows(rows)
    temporary_csv.replace(csv_path)

    lines = [
        "S4 Lean verification campaign",
        f"campaign: {campaign_id}",
        f"updated: {summary['updated_at']}",
        f"selected targets: {len(rows)}",
        "",
        "status counts:",
    ]
    for status in sorted(counts):
        lines.append(f"  {status}: {counts[status]}")
    failures = [row for row in rows if row["status"] in {"failed", "timeout", "launch_error"}]
    if failures:
        lines.extend(("", "failed or timed-out targets:"))
        for row in failures:
            lines.append(
                f"  [{row['status']}] {row['target']}  log={row['log']}"
            )
    summary_text = run_dir / "SUMMARY.txt"
    temporary_text = summary_text.with_suffix(".txt.tmp")
    temporary_text.write_text("\n".join(lines) + "\n", encoding="utf-8")
    temporary_text.replace(summary_text)


def render_progress(
    run_dir: Path,
    campaign_id: str,
    selected_count: int,
    counts: dict[str, int],
    failures: dict[str, dict[str, Any]],
    last_result: dict[str, Any] | None,
) -> None:
    visible_failures = list(failures.values())[-200:]
    progress = {
        "campaign_id": campaign_id,
        "updated_at": utc_now(),
        "selected_targets": selected_count,
        "counts": counts,
        "failure_count": len(failures),
        "recent_failures": visible_failures,
        "last_result": last_result,
    }
    atomic_json(run_dir / "progress.json", progress)
    lines = [
        "S4 Lean verification campaign",
        f"campaign: {campaign_id}",
        f"updated: {progress['updated_at']}",
        f"selected targets: {selected_count}",
        "",
        "status counts:",
    ]
    for status in sorted(counts):
        lines.append(f"  {status}: {counts[status]}")
    if last_result:
        lines.extend((
            "",
            "last completed target:",
            f"  [{last_result['status']}] {last_result['target']}",
            f"  log={last_result['log']}",
        ))
    if failures:
        lines.extend(("", f"failures/timeouts: {len(failures)} (showing latest 200)"))
        for result in visible_failures:
            lines.append(f"  [{result['status']}] {result['target']}  log={result['log']}")
    path = run_dir / "SUMMARY.txt"
    temporary = path.with_suffix(".txt.tmp")
    temporary.write_text("\n".join(lines) + "\n", encoding="utf-8")
    temporary.replace(path)


def run_target(
    *,
    item: dict[str, Any],
    index: int,
    total: int,
    key: str,
    run_dir: Path,
    lean_dir: Path,
    lake: str,
    threads: int,
    timeout_seconds: float,
) -> dict[str, Any]:
    logs = run_dir / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    log_path = logs / safe_log_name(index, key, item)
    command = [lake, "build", lake_target(str(item["target"]))]
    started_at = utc_now()
    started = time.monotonic()
    print(
        f"[{index}/{total}] START {item['stage']} {item['tag']} {item['target']}",
        flush=True,
    )
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = str(threads)
    creation: dict[str, Any] = {}
    if os.name == "nt":
        creation["creationflags"] = subprocess.CREATE_NEW_PROCESS_GROUP
    else:
        creation["start_new_session"] = True

    status = "launch_error"
    exit_code: int | None = None
    interrupted = False
    with log_path.open("w", encoding="utf-8", errors="replace") as log:
        log.write(f"started_at: {started_at}\n")
        log.write(f"stage: {item['stage']}\n")
        log.write(f"tag: {item['tag']}\n")
        log.write(f"target: {item['target']}\n")
        log.write(f"command: {' '.join(command)}\n")
        log.write(f"LEAN_NUM_THREADS: {threads}\n")
        log.write(f"timeout_seconds: {timeout_seconds:g}\n\n")
        log.flush()
        try:
            process = subprocess.Popen(
                command,
                cwd=lean_dir,
                env=env,
                stdout=log,
                stderr=subprocess.STDOUT,
                text=True,
                **creation,
            )
            try:
                exit_code = process.wait(timeout=timeout_seconds)
                status = "success" if exit_code == 0 else "failed"
            except subprocess.TimeoutExpired:
                status = "timeout"
                kill_process_tree(process)
                exit_code = process.poll()
                log.write("\nCAMPAIGN: target timed out; process tree terminated.\n")
            except KeyboardInterrupt:
                interrupted = True
                status = "interrupted"
                kill_process_tree(process)
                exit_code = process.poll()
                log.write("\nCAMPAIGN: interrupted; process tree terminated.\n")
        except OSError as error:
            log.write(f"\nCAMPAIGN: could not launch Lake: {error!r}\n")

    elapsed = round(time.monotonic() - started, 3)
    result = {
        "status": status,
        "stage": item["stage"],
        "tag": item["tag"],
        "target": item["target"],
        "exit_code": exit_code,
        "started_at": started_at,
        "finished_at": utc_now(),
        "elapsed_seconds": elapsed,
        "log": str(log_path.relative_to(run_dir)),
        "interrupted": interrupted,
    }
    print(
        f"[{index}/{total}] {status.upper()} {item['target']} ({elapsed:.1f}s)",
        flush=True,
    )
    return result


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Run every prepared Lean module independently and resume safely."
    )
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--run-dir", type=Path, default=DEFAULT_RUN_DIR)
    parser.add_argument(
        "--lake",
        help="Lake executable; defaults to the pinned direct Elan toolchain when present.",
    )
    parser.add_argument("--threads", type=int, default=1)
    parser.add_argument("--timeout-hours", type=float, default=2.0)
    parser.add_argument("--stage", action="append", help="Run only this stage; repeatable")
    parser.add_argument("--tag", action="append", help="Run only this certificate tag; repeatable")
    parser.add_argument("--max-targets", type=int)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument(
        "--full-report-every",
        type=int,
        default=10000,
        help="Checkpoint the full CSV/JSON report every N attempts (0 disables checkpoints).",
    )
    parser.add_argument(
        "--skip-previous-failures",
        action="store_true",
        help="On resume, skip failures as well as successes.",
    )
    parser.add_argument(
        "--fail-exit-code",
        action="store_true",
        help="Return nonzero after the full pass if any selected target failed.",
    )
    args = parser.parse_args()
    if args.threads < 1:
        parser.error("--threads must be positive")
    if args.timeout_hours <= 0:
        parser.error("--timeout-hours must be positive")
    if args.full_report_every < 0:
        parser.error("--full-report-every must be nonnegative")

    manifest_path = args.manifest.resolve()
    run_dir = args.run_dir.resolve()
    manifest = load_json(manifest_path, None)
    if not isinstance(manifest, dict) or "campaign_id" not in manifest:
        parser.error(f"invalid or missing campaign manifest: {manifest_path}")
    selected = [
        item for item in manifest.get("targets", [])
        if (not args.stage or item["stage"] in args.stage)
        and (not args.tag or item["tag"] in args.tag)
    ]
    if args.max_targets is not None:
        selected = selected[: args.max_targets]
    if args.dry_run:
        print(f"campaign={manifest['campaign_id']} targets={len(selected)}")
        for index, item in enumerate(selected, 1):
            print(f"{index:6d} {item['stage']:28s} {item['tag']:20s} {item['target']}")
        return 0

    lean_dir = ROOT / "lean"
    lake = resolve_lake(args.lake, lean_dir)
    print(f"Lake executable: {lake}", flush=True)
    run_dir.mkdir(parents=True, exist_ok=True)
    state_path = run_dir / "state.json"
    events_path = run_dir / "events.jsonl"
    state = load_json(
        state_path,
        {
            "schema_version": 1,
            "created_at": utc_now(),
            "host": platform.node(),
            "platform": platform.platform(),
        },
    )
    results = dict(state.pop("results", {}))  # compatibility with early runner snapshots
    replay_events(events_path, results)
    state["last_campaign_id"] = manifest["campaign_id"]
    state["manifest"] = str(manifest_path)

    campaign_id = str(manifest["campaign_id"])
    selected_keys = {target_key(campaign_id, item) for item in selected}
    counts: dict[str, int] = {"pending": len(selected)}
    failure_results: dict[str, dict[str, Any]] = {}
    for key in selected_keys:
        result = results.get(key)
        if not result:
            continue
        counts["pending"] -= 1
        status = str(result.get("status", "pending"))
        counts[status] = counts.get(status, 0) + 1
        if status in {"failed", "timeout", "launch_error"}:
            failure_results[key] = result
    state["counts"] = counts
    state["updated_at"] = utc_now()
    atomic_json(state_path, state)
    render_progress(
        run_dir, campaign_id, len(selected), counts, failure_results, None
    )

    timeout_seconds = args.timeout_hours * 3600
    attempted = 0
    failures = 0
    interrupted = False
    with events_path.open("a", encoding="utf-8") as events:
        for ordinal, item in enumerate(selected, 1):
            key = target_key(campaign_id, item)
            previous = results.get(key)
            if previous and (
                previous.get("status") == "success"
                or args.skip_previous_failures
                and previous.get("status") in {"failed", "timeout", "launch_error"}
            ):
                print(
                    f"[{ordinal}/{len(selected)}] SKIP {previous['status']} {item['target']}",
                    flush=True,
                )
                continue
            result = run_target(
                item=item,
                index=ordinal,
                total=len(selected),
                key=key,
                run_dir=run_dir,
                lean_dir=lean_dir,
                lake=lake,
                threads=args.threads,
                timeout_seconds=timeout_seconds,
            )
            attempted += 1
            events.write(json.dumps({"key": key, **result}, sort_keys=True) + "\n")
            events.flush()
            os.fsync(events.fileno())
            old_status = str(previous.get("status")) if previous else "pending"
            counts[old_status] = max(0, counts.get(old_status, 0) - 1)
            counts[result["status"]] = counts.get(result["status"], 0) + 1
            results[key] = result
            if result["status"] in {"failed", "timeout", "launch_error"}:
                failure_results[key] = result
            else:
                failure_results.pop(key, None)
            state["counts"] = counts
            state["updated_at"] = utc_now()
            state["last_result"] = result
            atomic_json(state_path, state)
            render_progress(
                run_dir, campaign_id, len(selected), counts, failure_results, result
            )
            if args.full_report_every and attempted % args.full_report_every == 0:
                render_reports(run_dir, manifest, selected, results)
            if result["status"] != "success":
                failures += 1
            if result["status"] == "interrupted":
                interrupted = True
                break

    render_reports(run_dir, manifest, selected, results)
    print(
        f"Campaign pass finished: attempted={attempted} failures={failures}. "
        f"See {run_dir / 'SUMMARY.txt'}",
        flush=True,
    )
    if interrupted:
        return 130
    current_failures = sum(
        counts.get(status, 0) for status in ("failed", "timeout", "launch_error")
    )
    if args.fail_exit_code and current_failures:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
