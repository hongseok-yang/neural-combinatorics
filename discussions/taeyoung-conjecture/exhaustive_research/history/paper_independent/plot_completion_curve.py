#!/usr/bin/env python3
"""Plot catalogue resolution and Lean-verification progress against logged effort.

The x-axis is cumulative active Codex/Claude Code turn time from surviving logs. Parallel
turns are additive. The measure excludes idle wall time, human time, ChatGPT
web conversations, retention-deleted August Claude sessions, and standalone
build time outside a logged turn. It is therefore an observable effort proxy,
not a complete labor total.
"""

from __future__ import annotations

import csv
import datetime as dt
import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent
KST_FORMAT = "%Y-%m-%d %H:%M:%S"


# "Resolved" means classified positive or negative in the campaign catalogue.
# The initial 44 rows are inherited from the four supplied theorem documents;
# they are placed at x=0 rather than credited to the first census turn.
# "Lean verified" follows the history's source-metadata count at each event.
EVENTS = [
    ("2026-08-13 10:41:47", "Inherited theorem baseline", 44, 0),
    ("2026-08-13 11:07:03", "Whiskering and self-amalgamation", 46, 0),
    ("2026-08-13 12:07:31", "Tensor--Turan witnesses", 64, 0),
    ("2026-08-13 12:33:50", "Sixteen lifting claims withdrawn", 48, 0),
    ("2026-08-13 12:50:14", "Rooted triangle--tree extensions", 51, 0),
    ("2026-08-13 13:18:44", "Cone and leaf families", 66, 0),
    ("2026-08-13 14:34:36", "Lean skeleton", 66, 1),
    ("2026-08-13 15:23:15", "Two-root triangle--leaf cones", 70, 1),
    ("2026-08-13 16:06:18", "Page-rooted triangle books", 74, 1),
    ("2026-08-13 16:59:06", "Turan-local counterexamples", 77, 1),
    ("2026-08-13 18:23:38", "Atlas 95 and 102", 79, 1),
    ("2026-08-13 20:31:42", "Atlas 97 and 100", 81, 1),
    ("2026-08-13 21:52:21", "Atlas 104 and 134", 83, 1),
    ("2026-08-13 23:12:49", "Atlas 113 and 119", 85, 1),
    ("2026-08-14 00:39:43", "Atlas 120", 86, 1),
    ("2026-08-14 01:13:26", "Atlas 123", 87, 1),
    ("2026-08-14 02:11:31", "Atlas 142", 88, 1),
    ("2026-08-14 12:40:57", "Atlas 152 counterexample", 89, 1),
    ("2026-08-18 14:10:00", "Atlas 137 and 139", 91, 1),
    ("2026-08-18 15:06:44", "Atlas 145 and 148", 93, 1),
    ("2026-08-18 19:19:51", "Atlas 160", 94, 1),
    ("2026-08-18 21:11:00", "First bulk Lean commit", 94, 94),
    ("2026-08-18 22:02:00", "Atlas 126", 95, 94),
    ("2026-08-19 03:50:52", "Atlas 178", 96, 94),
    ("2026-08-19 16:29:00", "Atlas 178 formalized", 96, 95),
    ("2026-08-20 23:40:00", "Atlas 127", 97, 95),
    ("2026-08-24 12:02:00", "Partial-bound campaign", 97, 95),
    ("2026-08-25 12:12:00", "Exact rooted-SOS campaign", 115, 95),
    ("2026-08-26 17:00:00", "Atlas 43 and 196 marked verified", 115, 97),
    ("2026-09-21 16:25:22", "Atlas 130 and 203", 117, 97),
    ("2026-09-22 12:17:00", "Fifteen compact rows marked verified", 117, 112),
    ("2026-09-23 01:06:00", "Atlas 188 marked verified", 117, 113),
    ("2026-09-23 04:22:00", "Atlas 153, 171, 174 marked verified", 117, 116),
    ("2026-09-23 13:43:00", "Atlas 127 marked verified", 117, 117),
]


def read_json(relative: str):
    return json.loads((ROOT / relative).read_text(encoding="utf-8"))


def parse_time(value: str) -> dt.datetime:
    return dt.datetime.strptime(value, KST_FORMAT)


def logged_turns() -> list[tuple[dt.datetime, dt.datetime]]:
    main = read_json("history/session_index.json")["sessions"]
    second = read_json("history/addendum_desktop-q0hdpqd/addendum_index.json")["sessions"]

    main_workers = [s for s in main if s.get("role") in {"worker", "subagent"}]
    second_workers = [
        s
        for s in second
        if s.get("relevance") == "primary" and s.get("role") in {"worker", "worker-fork"}
    ]

    result = []
    for session in [*main_workers, *second_workers]:
        for turn in session.get("turns", []):
            if turn.get("replayed") or not turn.get("start") or not turn.get("end"):
                continue
            result.append((parse_time(turn["start"]), parse_time(turn["end"])))
    return result


def cumulative_hours(when: dt.datetime, turns: list[tuple[dt.datetime, dt.datetime]]) -> float:
    seconds = 0.0
    for start, end in turns:
        if start >= when:
            continue
        stop = min(end, when)
        if stop > start:
            seconds += (stop - start).total_seconds()
    return seconds / 3600


def write_data(rows: list[dict]) -> None:
    path = OUT / "completion_vs_effort.csv"
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)


def plot(rows: list[dict]) -> None:
    x = [row["logged_agent_hours"] for row in rows]
    resolved = [row["resolved_rows"] for row in rows]
    verified = [row["lean_verified_rows"] for row in rows]

    plt.rcParams.update(
        {
            "font.size": 10.5,
            "axes.titlesize": 16,
            "axes.labelsize": 11.5,
            "legend.fontsize": 10.5,
        }
    )
    fig, ax = plt.subplots(figsize=(11.5, 6.7), constrained_layout=False)
    ax.set_facecolor("#fbfbfc")
    ax.grid(axis="both", color="#d9dde3", linewidth=0.7, alpha=0.75)

    ax.step(
        x,
        resolved,
        where="post",
        color="#2367a8",
        linewidth=2.8,
        label="Claimed resolved (positive or negative)",
        zorder=3,
    )
    ax.step(
        x,
        verified,
        where="post",
        color="#d66b18",
        linewidth=2.8,
        label="Lean-marked verified",
        zorder=4,
    )
    ax.fill_between(x, verified, resolved, step="post", color="#5f7890", alpha=0.10, zorder=1)

    ax.scatter([x[0]], [resolved[0]], color="#2367a8", s=34, zorder=5)
    ax.annotate(
        "44 inherited\nfrom supplied theorems",
        xy=(x[0], resolved[0]),
        xytext=(6, 34),
        textcoords="offset points",
        arrowprops={"arrowstyle": "-", "color": "#66717c", "lw": 0.8},
        color="#33404c",
    )

    annotations = [
        (3, "16 claims\nwithdrawn", (-5, -42)),
        (21, "First bulk Lean commit:\n1 to 94", (12, -50)),
        (27, "Rooted SOS:\n+18 resolved", (8, -52)),
        (29, "Final two\nresolved", (-18, -52)),
        (30, "Compact verification\ncampaign begins", (8, -48)),
        (33, "117 / 117", (-34, -42)),
    ]
    for index, label, offset in annotations:
        y_value = verified[index] if index in {21, 30, 33} else resolved[index]
        color = "#d66b18" if index in {21, 30, 33} else "#2367a8"
        ax.scatter([x[index]], [y_value], color=color, s=30, zorder=5)
        ax.annotate(
            label,
            xy=(x[index], y_value),
            xytext=offset,
            textcoords="offset points",
            arrowprops={"arrowstyle": "-", "color": "#66717c", "lw": 0.8},
            color="#33404c",
        )

    ax.set_title("Catalogue completion versus logged Codex/Claude Code effort", loc="left", pad=14)
    ax.set_xlabel("Cumulative active Codex/Claude Code turn hours (parallel turns additive)")
    ax.set_ylabel("Catalogue rows (out of 117)")
    ax.set_xlim(0, max(x) + 4)
    ax.set_ylim(0, 121)
    ax.set_yticks([0, 20, 40, 60, 80, 100, 117])
    ax.legend(loc="lower right", frameon=True, facecolor="white", edgecolor="#c9ced6")

    note = (
        "Effort proxy: surviving Codex and Claude Code worker/subagent turn durations; excludes human time, "
        "ChatGPT web runs, retention-deleted August Claude turns, and standalone builds.  "
        "'Verified' follows Lean source metadata, not a complete fresh-build audit."
    )
    fig.text(0.075, 0.015, note, ha="left", va="bottom", fontsize=8.6, color="#59636e", wrap=True)
    fig.subplots_adjust(left=0.075, right=0.98, top=0.90, bottom=0.18)

    svg_path = OUT / "completion_vs_effort.svg"
    fig.savefig(svg_path, format="svg")
    fig.savefig(OUT / "completion_vs_effort.png", dpi=190)
    plt.close(fig)

    # Matplotlib writes trailing spaces in multiline SVG path values.  Strip
    # them so the generated source passes Git's whitespace checks.
    svg = svg_path.read_text(encoding="utf-8")
    svg_path.write_text(
        "\n".join(line.rstrip() for line in svg.splitlines()) + "\n",
        encoding="utf-8",
    )


def main() -> None:
    turns = logged_turns()
    origin = parse_time(EVENTS[0][0])
    origin_hours = cumulative_hours(origin, turns)
    rows = []
    for timestamp, event, resolved, verified in EVENTS:
        when = parse_time(timestamp)
        rows.append(
            {
                "event_time_kst": timestamp,
                "logged_agent_hours": round(cumulative_hours(when, turns) - origin_hours, 4),
                "resolved_rows": resolved,
                "lean_verified_rows": verified,
                "event": event,
            }
        )
    write_data(rows)
    plot(rows)


if __name__ == "__main__":
    main()
