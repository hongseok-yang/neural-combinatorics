#!/usr/bin/env python3
"""Print the reproducible headline counts used in the Phase-1 directions memo."""

from __future__ import annotations

import argparse
import collections
import datetime as dt
import json
import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
KST_FORMAT = "%Y-%m-%d %H:%M:%S"


def read_json(relative: str):
    return json.loads((ROOT / relative).read_text(encoding="utf-8"))


def duration_seconds(start: str | None, end: str | None) -> float:
    if not start or not end:
        return 0.0
    return (dt.datetime.strptime(end, KST_FORMAT) - dt.datetime.strptime(start, KST_FORMAT)).total_seconds()


def catalogue_counts() -> dict:
    path = ROOT / "GRAPH_CLASSIFICATION_UP_TO_6_VERTICES.md"
    rows = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not re.match(r"^\|\s*\d+\s*\|", line):
            continue
        cells = [cell.strip() for cell in line.strip("|").split("|")]
        status = "Positive" if "Positive" in cells[6] else "Negative" if "Negative" in cells[6] else "Other"
        rows.append({"atlas": int(cells[0]), "status": status, "reason": cells[8]})

    statuses = collections.Counter(row["status"] for row in rows)
    positives = [row for row in rows if row["status"] == "Positive"]
    negatives = [row for row in rows if row["status"] == "Negative"]
    direct_certificate = [
        row
        for row in positives
        if any(
            label in row["reason"]
            for label in ("Compact four-root SOS", "Exact rooted interval-SOS", "Induced and four-root SOS")
        )
    ]
    pure_chordal = [row for row in positives if "Pure-chordal theorem" in row["reason"]]
    negative_methods = {
        "tensor": [row["atlas"] for row in negatives if "Tensor counterexample" in row["reason"]],
        "turan_local": [row["atlas"] for row in negatives if "Turan-local counterexample" in row["reason"]],
        "fractional_fibre": [
            row["atlas"] for row in negatives if "Fractional-fibre local counterexample" in row["reason"]
        ],
    }
    assert len(rows) == 117
    assert statuses == {"Positive": 94, "Negative": 23}
    assert len(direct_certificate) == 20
    assert len(pure_chordal) == 19
    assert sum(map(len, negative_methods.values())) == 23
    return {
        "rows": len(rows),
        "statuses": dict(statuses),
        "pure_chordal_positive_rows": [row["atlas"] for row in pure_chordal],
        "direct_certificate_positive_rows": [row["atlas"] for row in direct_certificate],
        "other_analytic_or_closure_positive_rows": len(positives) - len(pure_chordal) - len(direct_certificate),
        "negative_methods": negative_methods,
    }


def session_counts() -> dict:
    workstation = read_json("history/session_index.json")["sessions"]
    second = read_json("history/addendum_desktop-q0hdpqd/addendum_index.json")["sessions"]
    chatgpt = read_json("history/addendum_desktop-q0hdpqd/tools/chatgpt_sessions.json")

    ws_roles = collections.Counter((s["tool"], s["role"]) for s in workstation)
    ws_codex_workers = [s for s in workstation if s["tool"] == "Codex" and s["role"] == "worker"]
    ws_claude = [s for s in workstation if s["tool"] == "Claude Code" and s["role"] in {"worker", "subagent"}]
    ws_typed_prompts = sum(len(s.get("prompts", [])) for s in ws_codex_workers) + sum(
        len(s.get("turns", [])) for s in workstation if s["tool"] == "Claude Code" and s["role"] == "worker"
    )
    ws_review_turns = sum(len(s.get("turns", [])) for s in workstation if s["role"] == "approval-reviewer")

    primary_workers = [
        s
        for s in second
        if s.get("relevance") == "primary" and s["role"] in {"worker", "worker-fork"}
    ]
    add_roles = collections.Counter((s["tool"], s["role"], s.get("relevance")) for s in second)
    live_ultra = []
    for session in primary_workers:
        for turn in session.get("turns", []):
            model = turn.get("model") or [None, None]
            if not turn.get("replayed") and len(model) > 1 and model[1] == "ultra":
                live_ultra.append(turn)
    add_review_turns = sum(len(s.get("turns", [])) for s in second if s["role"] == "approval-reviewer")

    conversations = chatgpt["conversations"]
    return {
        "workstation": {
            "roles": {" / ".join(map(str, key)): value for key, value in sorted(ws_roles.items())},
            "typed_prompts": ws_typed_prompts,
            "goal_objectives": 10,
            "codex_worker_turns": sum(len(s.get("turns", [])) for s in ws_codex_workers),
            "codex_tokens_processed": sum(s.get("usage", {}).get("total_tokens", 0) for s in ws_codex_workers),
            "codex_cached_input_tokens": sum(
                s.get("usage", {}).get("cached_input_tokens", 0) for s in ws_codex_workers
            ),
            "codex_output_tokens": sum(s.get("usage", {}).get("output_tokens", 0) for s in ws_codex_workers),
            "codex_reasoning_output_tokens": sum(
                s.get("usage", {}).get("reasoning_output_tokens", 0) for s in ws_codex_workers
            ),
            "claude_input_including_cache": sum(
                sum(
                    s.get("usage", {}).get(key, 0)
                    for key in ("input_tokens", "cache_read_input_tokens", "cache_creation_input_tokens")
                )
                for s in ws_claude
            ),
            "claude_output_tokens": sum(s.get("usage", {}).get("output_tokens", 0) for s in ws_claude),
            "approval_reviews": ws_review_turns,
        },
        "second_device": {
            "roles": {" / ".join(map(str, key)): value for key, value in sorted(add_roles.items())},
            "primary_worker_threads": len(primary_workers),
            "primary_live_turns": sum(
                sum(not turn.get("replayed") for turn in s.get("turns", [])) for s in primary_workers
            ),
            "primary_tokens_processed": sum(s.get("usage", {}).get("total_tokens", 0) for s in primary_workers),
            "live_ultra_turns": len(live_ultra),
            "live_ultra_turn_hours": sum(
                duration_seconds(turn.get("start"), turn.get("end")) for turn in live_ultra
            )
            / 3600,
            "approval_reviews": add_review_turns,
        },
        "chatgpt_export": {
            "campaign_conversations": sum(c["role"] == "campaign" for c in conversations),
            "satellite_conversations": sum(c["role"] == "satellite" for c in conversations),
            "unique_prompt_entries_in_appendix": 32,
            "listed_prehistory_conversations": len(chatgpt["prehistory"]),
        },
    }


def verification_counts() -> dict:
    runs = []
    base = ROOT / "lean/verification_runs"
    for path in sorted(base.glob("atlas*/completed_row.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        atlas = data.get("atlas", int(path.parent.name.removeprefix("atlas")))
        runs.append(
            {
                "atlas": atlas,
                "seconds": data.get("combined_seconds", data.get("measured_check_seconds")),
                "files": data.get("row_file_count", data.get("row_specific_source_files")),
                "peak_bytes": data["peak_private_bytes"],
            }
        )
    assert len(runs) == 20
    seconds = sum(run["seconds"] for run in runs)
    examples = sorted((ROOT / "lean/Taeyoung/Examples").glob("Graph[0-9][0-9][0-9].lean"))
    example_text = [path.read_text(encoding="utf-8") for path in examples]
    assert len(examples) == 117
    return {
        "static_example_files": len(examples),
        "static_verified_metadata_files": sum("formalization := .verified" in text for text in example_text),
        "static_example_files_containing_sorry": sum(bool(re.search(r"\bsorry\b", text)) for text in example_text),
        "bounded_row_runs": len(runs),
        "atlases": sorted(run["atlas"] for run in runs),
        "total_seconds": seconds,
        "total_hours": seconds / 3600,
        "mean_seconds": seconds / len(runs),
        "peak_gib": max(run["peak_bytes"] for run in runs) / 2**30,
        "atlas43_separate_chain": {"modules": 1097, "hours": 6.0, "peak_gib": 15.4},
        "fresh_full_run_present": (base / "full-20260923-164651").is_dir(),
    }


def documentary_counts() -> dict:
    tracked = subprocess.run(
        ["git", "ls-files", "--", "notes"], cwd=ROOT, check=True, text=True, capture_output=True
    ).stdout.splitlines()
    tracked_tex = [name for name in tracked if name.endswith(".tex")]
    correspondence = []
    pattern = re.compile(r"What the Lean formalization actually proves|Correspondence with the Lean verification")
    for relative in tracked_tex:
        if pattern.search((ROOT / relative).read_text(encoding="utf-8")):
            correspondence.append(relative)
    attempts = re.findall(
        r"^##\s+(\d+)\.", (ROOT / "FAILED_PROOF_ATTEMPTS.md").read_text(encoding="utf-8"), re.MULTILINE
    )
    assert attempts and max(map(int, attempts)) == 65
    return {
        "tracked_tex_notes": len(tracked_tex),
        "notes_with_lean_correspondence_section": len(correspondence),
        "failed_attempt_entries": len(attempts),
    }


def git_counts() -> dict:
    # This cutoff is the final classification commit's logged time, not the later
    # history/verifier commits.
    raw = subprocess.run(
        [
            "git",
            "log",
            "--since=2026-08-13T00:00:00+09:00",
            "--until=2026-09-23T13:44:12+09:00",
            "--format=%H%x09%B%x1e",
            "--",
            ".",
        ],
        cwd=ROOT,
        check=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        capture_output=True,
    ).stdout
    commits = [entry for entry in raw.split("\x1e") if entry.strip()]
    return {
        "campaign_commits_through_final_classification": len(commits),
        "commits_with_claude_coauthor_trailer": sum("Co-Authored-By: Claude" in entry for entry in commits),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true", help="emit JSON rather than a readable report")
    args = parser.parse_args()
    result = {
        "definitions": {
            "campaign_commit_window": "2026-08-13 00:00:00 through 2026-09-23 13:44:12 KST",
            "direct_certificate_positive": "catalogue reason contains Compact four-root SOS, Exact rooted interval-SOS, or Induced and four-root SOS",
            "bounded_row_run": "an atlasNNN/completed_row.json record; Atlas 43 is reported separately",
            "tokens": "provider-specific processed-token counters; not prices and not summed across providers",
        },
        "catalogue": catalogue_counts(),
        "sessions": session_counts(),
        "verification": verification_counts(),
        "documents": documentary_counts(),
        "git": git_counts(),
    }
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
        return
    for section, values in result.items():
        print(f"[{section}]")
        print(json.dumps(values, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
