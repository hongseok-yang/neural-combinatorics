"""Generate every S4 Lean witness and a fair, resumable campaign manifest."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
EXPERIMENTS = ROOT / "experiments"
LEAN_ROOT = ROOT / "lean" / "Taeyoung" / "Methods" / "RootedSOS"
PREFIX = "Taeyoung.Methods.RootedSOS"
CERTIFICATE_RE = re.compile(
    r"atlas(?P<atlas>\d+)_exact(?:_(?P<variant>lower|upper|middle|upper34))?"
    r"_interval_sos\.json"
)
GENERATOR_FILES = (
    "export_s4_lean_certificate.py",
    "export_s4_lean_common.py",
    "export_s4_lean_classification.py",
    "generate_s4_lean_data_modules.py",
    "generate_s4_lean_common_checks.py",
    "generate_s4_lean_exact_common.py",
    "generate_s4_lean_exceptional_checks.py",
    "generate_s4_lean_group_checks.py",
    "generate_s4_lean_exceptional_group_checks.py",
    "generate_s4_lean_coefficient_checks.py",
    "generate_s4_lean_certificate_bundle.py",
    "generate_s4_lean_classification_checks.py",
    "generate_s4_lean_young_checks.py",
)


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def atomic_json(path: Path, value: object) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(path)


def write_if_changed(path: Path, contents: str) -> None:
    if path.exists() and path.read_text(encoding="utf-8") == contents:
        return
    path.write_text(contents, encoding="utf-8")


def certificate_specs(selected_tags: set[str] | None) -> list[dict[str, Any]]:
    specs = []
    for path in sorted(EXPERIMENTS.glob("atlas*_exact*interval_sos.json")):
        match = CERTIFICATE_RE.fullmatch(path.name)
        if match is None:
            continue
        atlas = int(match.group("atlas"))
        variant = match.group("variant")
        suffix = "" if variant is None else variant.capitalize()
        if variant == "upper34":
            suffix = "Upper34"
        tag = f"Atlas{atlas}{suffix}"
        if selected_tags and tag not in selected_tags:
            continue
        output_stem = f"atlas{atlas}"
        if variant:
            output_stem += f"_{variant}"
        output_stem += "_lean_certificate"
        specs.append(
            {
                "atlas": atlas,
                "variant": variant or "full",
                "tag": tag,
                "source": path,
                "output": EXPERIMENTS / f"{output_stem}.json",
                "stem": output_stem,
            }
        )
    return specs


def run_step(
    name: str,
    command: list[str],
    log_handle: Any,
) -> dict[str, Any]:
    started = utc_now()
    line = " ".join(command)
    print(f"PREP START {name}", flush=True)
    log_handle.write(f"\n[{started}] START {name}\n{line}\n")
    log_handle.flush()
    completed = subprocess.run(
        command,
        cwd=ROOT,
        stdout=log_handle,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )
    status = "success" if completed.returncode == 0 else "failed"
    finished = utc_now()
    log_handle.write(f"[{finished}] {status.upper()} {name} exit={completed.returncode}\n")
    log_handle.flush()
    print(f"PREP {status.upper()} {name}", flush=True)
    return {
        "name": name,
        "status": status,
        "exit_code": completed.returncode,
        "started_at": started,
        "finished_at": finished,
        "command": command,
    }


def read_targets(path: Path) -> list[str]:
    if not path.exists():
        return []
    result = []
    seen = set()
    for raw in path.read_text(encoding="utf-8").splitlines():
        target = raw.strip()
        if target and target not in seen:
            seen.add(target)
            result.append(target)
    return result


def interleave(tagged: list[tuple[str, list[str]]]) -> list[tuple[str, str]]:
    result: list[tuple[str, str]] = []
    maximum = max((len(targets) for _, targets in tagged), default=0)
    for index in range(maximum):
        for tag, targets in tagged:
            if index < len(targets):
                result.append((tag, targets[index]))
    return result


def add_targets(
    output: list[dict[str, str]],
    stage: str,
    tagged_targets: list[tuple[str, str]],
    seen: set[str],
) -> None:
    for tag, target in tagged_targets:
        # A module is compiled once per campaign even if a generator places it
        # in more than one target list.
        if target in seen:
            continue
        seen.add(target)
        output.append({"stage": stage, "tag": tag, "target": target})


def choose_smoke(targets: list[str], pattern: str) -> str | None:
    expression = re.compile(pattern)
    for target in targets:
        if expression.search(target):
            return target
    return targets[0] if targets else None


def content_fingerprint(paths: list[Path], targets: list[dict[str, str]]) -> str:
    digest = hashlib.sha256()
    for path in sorted(set(path.resolve() for path in paths)):
        digest.update(str(path.relative_to(ROOT)).replace("\\", "/").encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    digest.update(json.dumps(targets, sort_keys=True, separators=(",", ":")).encode("utf-8"))
    return digest.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Prepare all exact S4 certificates and the long-build queue."
    )
    parser.add_argument("--tag", action="append", help="Prepare only this Lean tag")
    parser.add_argument(
        "--manifest-only",
        action="store_true",
        help="Do not regenerate witnesses; rebuild the campaign from existing target lists.",
    )
    parser.add_argument(
        "--campaign", type=Path, default=EXPERIMENTS / "s4_lean_campaign.json"
    )
    parser.add_argument(
        "--report", type=Path, default=EXPERIMENTS / "s4_lean_preparation_report.json"
    )
    parser.add_argument(
        "--log", type=Path, default=EXPERIMENTS / "s4_lean_preparation.log"
    )
    args = parser.parse_args()

    specs = certificate_specs(set(args.tag) if args.tag else None)
    if not specs:
        parser.error("no matching S4 interval certificates")

    steps: list[dict[str, Any]] = []
    args.log.parent.mkdir(parents=True, exist_ok=True)
    with args.log.open("a", encoding="utf-8") as log:
        if not args.manifest_only:
            shared_commands = (
                (
                    "shared common witness",
                    [sys.executable, "experiments/export_s4_lean_common.py"],
                ),
                (
                    "shared classification witness",
                    [sys.executable, "experiments/export_s4_lean_classification.py"],
                ),
                (
                    "shared classification modules",
                    [
                        sys.executable,
                        "experiments/generate_s4_lean_classification_checks.py",
                        "experiments/s4_lean_classification_manifest.json",
                    ],
                ),
                (
                    "shared Young pullback modules",
                    [sys.executable, "experiments/generate_s4_lean_young_checks.py"],
                ),
            )
            for name, command in shared_commands:
                steps.append(run_step(name, command, log))

            for spec in specs:
                tag = spec["tag"]
                output = spec["output"]
                manifest = EXPERIMENTS / f"{spec['stem']}_manifest.json"
                data_targets = EXPERIMENTS / f"{spec['stem']}_data_targets.txt"
                common_targets = EXPERIMENTS / f"{spec['stem']}_common_targets.txt"
                commands = (
                    (
                        f"{tag}: export compact witness",
                        [
                            sys.executable,
                            "experiments/export_s4_lean_certificate.py",
                            str(spec["source"].relative_to(ROOT)),
                            str(output.relative_to(ROOT)),
                        ],
                    ),
                    (
                        f"{tag}: data modules",
                        [
                            sys.executable,
                            "experiments/generate_s4_lean_data_modules.py",
                            str(manifest.relative_to(ROOT)),
                            "--tag",
                            tag,
                            "--target-list",
                            str(data_targets.relative_to(ROOT)),
                        ],
                    ),
                    (
                        f"{tag}: bounded common checks",
                        [
                            sys.executable,
                            "experiments/generate_s4_lean_common_checks.py",
                            str(manifest.relative_to(ROOT)),
                            "--tag",
                            tag,
                            "--target-list",
                            str(common_targets.relative_to(ROOT)),
                        ],
                    ),
                    (
                        f"{tag}: exact common theorem layer",
                        [
                            sys.executable,
                            "experiments/generate_s4_lean_exact_common.py",
                            str(manifest.relative_to(ROOT)),
                            "--tag",
                            tag,
                        ],
                    ),
                    (
                        f"{tag}: exceptional PSD checks",
                        [
                            sys.executable,
                            "experiments/generate_s4_lean_exceptional_checks.py",
                            str(manifest.relative_to(ROOT)),
                            "--tag",
                            tag,
                        ],
                    ),
                    (
                        f"{tag}: common group totals",
                        [
                            sys.executable,
                            "experiments/generate_s4_lean_group_checks.py",
                            str(manifest.relative_to(ROOT)),
                            "--tag",
                            tag,
                        ],
                    ),
                    (
                        f"{tag}: target coefficient equations",
                        [
                            sys.executable,
                            "experiments/generate_s4_lean_coefficient_checks.py",
                            str(manifest.relative_to(ROOT)),
                            "--tag",
                            tag,
                        ],
                    ),
                    (
                        f"{tag}: exceptional group totals",
                        [
                            sys.executable,
                            "experiments/generate_s4_lean_exceptional_group_checks.py",
                            str(manifest.relative_to(ROOT)),
                            "--tag",
                            tag,
                        ],
                    ),
                    (
                        f"{tag}: algebraic certificate bundle",
                        [
                            sys.executable,
                            "experiments/generate_s4_lean_certificate_bundle.py",
                            "--tag",
                            tag,
                        ],
                    ),
                )
                for name, command in commands:
                    result = run_step(name, command, log)
                    result["tag"] = tag
                    steps.append(result)

    shared_classification = read_targets(
        EXPERIMENTS / "s4_lean_classification_manifest_lean_targets.txt"
    )
    shared_young = read_targets(EXPERIMENTS / "s4_lean_young_targets.txt")
    lists_by_tag: dict[str, dict[str, list[str]]] = {}
    for spec in specs:
        stem = spec["stem"]
        tag = spec["tag"]
        lists_by_tag[tag] = {
            "data": read_targets(EXPERIMENTS / f"{stem}_data_targets.txt"),
            "common": read_targets(EXPERIMENTS / f"{stem}_common_targets.txt"),
            "exceptional": read_targets(
                EXPERIMENTS / f"{stem}_manifest_exceptional_check_targets.txt"
            ),
            "common_group": read_targets(
                EXPERIMENTS / f"{stem}_manifest_common_group_check_targets.txt"
            ),
            "coefficient": read_targets(
                EXPERIMENTS / f"{stem}_manifest_coefficient_check_targets.txt"
            ),
            "exceptional_group": read_targets(
                EXPERIMENTS / f"{stem}_manifest_exceptional_group_check_targets.txt"
            ),
            "exact": [
                *(f"{PREFIX}.S4{tag}Block{block:02d}Exact" for block in range(10)),
                f"{PREFIX}.S4{tag}CommonExact",
                f"{PREFIX}.S4{tag}FineData",
                f"{PREFIX}.S4{tag}AlgebraicCertificate",
            ],
        }

    targets: list[dict[str, str]] = []
    seen: set[str] = set()
    smoke: list[tuple[str, str]] = []
    for tag, lists in lists_by_tag.items():
        choices = (
            choose_smoke(lists["data"], r"FineMetaData$"),
            choose_smoke(lists["common"], r"Block09CheckRow000$"),
            choose_smoke(lists["exceptional"], r"ExceptionalBlock09CheckRow000$"),
            choose_smoke(lists["common_group"], r"CommonGroupRow000Check$"),
            choose_smoke(lists["exceptional_group"], r"ExceptionalGroupRow000Check$"),
            choose_smoke(lists["coefficient"], r"CoefficientEquation000Check$"),
        )
        smoke.extend((tag, target) for target in choices if target is not None)
    add_targets(targets, "00_certificate_smoke", smoke, seen)
    add_targets(
        targets,
        "10_certificate_data",
        interleave([(tag, lists["data"]) for tag, lists in lists_by_tag.items()]),
        seen,
    )
    add_targets(
        targets,
        "20_shared_classification",
        [("SharedS4", target) for target in shared_classification],
        seen,
    )
    add_targets(
        targets,
        "30_shared_young_pullback",
        [("SharedS4", target) for target in shared_young],
        seen,
    )
    add_targets(
        targets,
        "40_certificate_common_arithmetic",
        interleave([(tag, lists["common"]) for tag, lists in lists_by_tag.items()]),
        seen,
    )
    add_targets(
        targets,
        "50_certificate_exceptional_psd",
        interleave([(tag, lists["exceptional"]) for tag, lists in lists_by_tag.items()]),
        seen,
    )
    add_targets(
        targets,
        "55_certificate_common_group_totals",
        interleave([(tag, lists["common_group"]) for tag, lists in lists_by_tag.items()]),
        seen,
    )
    add_targets(
        targets,
        "56_certificate_target_coefficients",
        interleave([(tag, lists["coefficient"]) for tag, lists in lists_by_tag.items()]),
        seen,
    )
    add_targets(
        targets,
        "57_certificate_exceptional_group_totals",
        interleave([(tag, lists["exceptional_group"]) for tag, lists in lists_by_tag.items()]),
        seen,
    )
    add_targets(
        targets,
        "60_certificate_exact_interfaces",
        interleave([(tag, lists["exact"]) for tag, lists in lists_by_tag.items()]),
        seen,
    )

    fingerprint_paths = [spec["source"] for spec in specs]
    fingerprint_paths.extend(EXPERIMENTS / name for name in GENERATOR_FILES)
    campaign_id = content_fingerprint(fingerprint_paths, targets)
    stage_counts: dict[str, int] = {}
    tag_counts: dict[str, int] = {}
    for target in targets:
        stage_counts[target["stage"]] = stage_counts.get(target["stage"], 0) + 1
        tag_counts[target["tag"]] = tag_counts.get(target["tag"], 0) + 1
    campaign = {
        "schema_version": 1,
        "campaign_id": campaign_id,
        "prepared_at": utc_now(),
        "certificate_count": len(specs),
        "certificates": [
            {
                "atlas": spec["atlas"],
                "variant": spec["variant"],
                "tag": spec["tag"],
                "source": str(spec["source"].relative_to(ROOT)).replace("\\", "/"),
            }
            for spec in specs
        ],
        "stage_counts": stage_counts,
        "tag_counts": tag_counts,
        "targets": targets,
    }
    args.campaign.parent.mkdir(parents=True, exist_ok=True)
    atomic_json(args.campaign, campaign)

    failures = [step for step in steps if step["status"] != "success"]
    missing_lists = []
    for tag, lists in lists_by_tag.items():
        for kind in (
            "data", "common", "exceptional", "common_group", "coefficient",
            "exceptional_group",
        ):
            if not lists[kind]:
                missing_lists.append(f"{tag}:{kind}")
    missing_modules = []
    for item in targets:
        module = item["target"]
        if module.startswith("+"):
            module = module[1:]
        module = module.split(":", 1)[0]
        source_path = ROOT / "lean" / Path(*module.split(".")).with_suffix(".lean")
        if not source_path.exists():
            missing_modules.append(item["target"])
    report = {
        "prepared_at": utc_now(),
        "manifest_only": args.manifest_only,
        "certificate_count": len(specs),
        "campaign_id": campaign_id,
        "target_count": len(targets),
        "stage_counts": stage_counts,
        "tag_counts": tag_counts,
        "failed_steps": failures,
        "missing_target_lists": missing_lists,
        "missing_modules": missing_modules,
        "steps": steps,
    }
    args.report.parent.mkdir(parents=True, exist_ok=True)
    atomic_json(args.report, report)
    summary_lines = [
        "S4 Lean campaign preparation",
        f"prepared: {report['prepared_at']}",
        f"campaign: {campaign_id}",
        f"certificates: {len(specs)}",
        f"targets: {len(targets)}",
        f"failed preparation steps: {len(failures)}",
        f"missing target lists: {len(missing_lists)}",
        f"missing Lean modules: {len(missing_modules)}",
        "",
        "stages:",
    ]
    summary_lines.extend(f"  {stage}: {count}" for stage, count in stage_counts.items())
    if failures:
        summary_lines.extend(("", "failed steps:"))
        summary_lines.extend(f"  {step['name']}" for step in failures)
    if missing_lists:
        summary_lines.extend(("", "missing target lists:"))
        summary_lines.extend(f"  {value}" for value in missing_lists)
    if missing_modules:
        summary_lines.extend(("", "missing Lean modules:"))
        summary_lines.extend(f"  {value}" for value in missing_modules)
    write_if_changed(
        EXPERIMENTS / "s4_lean_campaign_summary.txt",
        "\n".join(summary_lines) + "\n",
    )
    print(
        f"PREP COMPLETE certificates={len(specs)} targets={len(targets)} "
        f"failed_steps={len(failures)} missing_lists={len(missing_lists)}",
        flush=True,
    )
    return 1 if failures or missing_lists or missing_modules else 0


if __name__ == "__main__":
    raise SystemExit(main())
