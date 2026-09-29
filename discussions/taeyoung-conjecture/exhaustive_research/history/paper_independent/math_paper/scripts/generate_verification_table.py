"""Generate the measured Lean row-build table from completed_row.json files."""

from __future__ import annotations

import json
from pathlib import Path


HERE = Path(__file__).resolve()
PROJECT = HERE.parents[4]
RUNS = PROJECT / "lean" / "verification_runs"
OUT = HERE.parent.parent / "generated"


def main() -> None:
    rows: list[dict[str, int | float | str]] = []
    for directory in sorted(RUNS.glob("atlas[0-9][0-9][0-9]")):
        path = directory / "completed_row.json"
        if not path.exists():
            continue
        source = json.loads(path.read_text(encoding="utf-8"))
        atlas = int(directory.name.removeprefix("atlas"))
        files = int(source.get("row_file_count", source.get("fresh_source_files")))
        source_bytes = source.get("row_source_bytes")
        seconds = float(source.get("combined_seconds", source.get("measured_check_seconds")))
        peak = int(source["peak_private_bytes"])
        rows.append(
            {
                "atlas": atlas,
                "files": files,
                "source_bytes": int(source_bytes) if source_bytes is not None else "--",
                "seconds": seconds,
                "peak_bytes": peak,
                "peak_gib": peak / 2**30,
            }
        )
    assert len(rows) == 20, len(rows)
    total_seconds = sum(float(row["seconds"]) for row in rows)
    summary = {
        "row_count": len(rows),
        "combined_hours": total_seconds / 3600,
        "maximum_peak_gib": max(float(row["peak_gib"]) for row in rows),
        "rows": rows,
        "atlas43_hours": 6.02,
        "atlas43_peak_gib": 15.4,
        "atlas43_modules": 1097,
    }
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "verification_measurements.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    lines = [
        r"\begin{table}[p]",
        r"\centering",
        r"\small",
        r"\caption{Measured sequential Lean builds for the twenty compact-certificate rows.  Time includes the fresh row build and the installed-source check when reported.}",
        r"\label{tab:verification-cost}",
        r"\begin{tabular}{rrrr}",
        r"\toprule Atlas & source files & time (min) & peak memory (GiB)\\ \midrule",
    ]
    for row in rows:
        lines.append(
            f"{row['atlas']} & {row['files']} & {float(row['seconds']) / 60:.1f} & "
            f"{float(row['peak_gib']):.2f}\\\\"
        )
    lines.extend(
        [
            r"\midrule",
            f"Total & -- & {total_seconds / 60:.1f} & --\\\\",
            r"\bottomrule",
            r"\end{tabular}",
            r"\end{table}",
            "",
        ]
    )
    (OUT / "verification_table.tex").write_text("\n".join(lines), encoding="utf-8")
    print(
        f"rows={len(rows)} combined_hours={total_seconds / 3600:.3f} "
        f"max_peak_gib={summary['maximum_peak_gib']:.2f}"
    )


if __name__ == "__main__":
    main()
