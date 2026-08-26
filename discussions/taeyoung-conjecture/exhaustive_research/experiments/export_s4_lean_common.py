"""Export certificate-independent data for the Lean S4 checker.

The exact interval certificates all use the same 352 raw flags and the same
five integer Young-symmetrizer slice matrices.  Keeping one derived copy makes
the Lean dependency graph substantially smaller.  This script checks every
committed S4 certificate before writing that copy; the mathematical
certificates themselves remain the source of truth.
"""

from __future__ import annotations

import argparse
import glob
import json
import sys
from pathlib import Path

import numpy as np

from full_s4_interval_sos import raw_by_isolated
from full_s4_rooted_sos import rooted_basis_indices


def write_json_if_changed(path: Path, payload: object) -> None:
    contents = json.dumps(payload, separators=(",", ":")) + "\n"
    if path.exists() and path.read_text(encoding="utf-8") == contents:
        return
    path.write_text(contents, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--pattern", default="experiments/atlas*_exact_*interval_sos.json"
    )
    parser.add_argument(
        "--output", default="experiments/s4_lean_common.json"
    )
    args = parser.parse_args()

    sys.set_int_max_str_digits(0)
    paths = sorted(Path(path) for path in glob.glob(args.pattern))
    paths += sorted(
        path for path in Path("experiments").glob("atlas*_exact_interval_sos.json")
        if path not in paths
    )
    if not paths:
        raise FileNotFoundError(args.pattern)

    first = json.loads(paths[0].read_text(encoding="utf-8"))
    expected = {
        "basis_indices": first["basis_indices"],
        "names": first["names"],
        "young_bases": first["young_bases"],
    }
    audited = []
    for path in paths:
        certificate = json.loads(path.read_text(encoding="utf-8"))
        for key, value in expected.items():
            if certificate[key] != value:
                raise AssertionError(f"{path}: inconsistent common field {key}")
        audited.append(path.name)

    names = expected["names"]
    basis_indices = rooted_basis_indices(2, "all")
    if basis_indices != expected["basis_indices"]:
        raise AssertionError("reconstructed raw basis differs from certificate")
    # The exact certificates are the source of truth for the chosen primitive
    # Young slices.  Recomputing pivot columns via floating QR is not stable
    # across SciPy/LAPACK versions and can choose a different (equally valid)
    # integer basis.  Every committed certificate was checked above to carry
    # these same matrices.
    transforms = [
        np.asarray(expected["young_bases"][name], dtype=np.int64)
        for name in names
    ]
    sparse_columns = [
        [
            [
                [int(a), int(transform[a, i])]
                for a in np.nonzero(transform[:, i])[0]
            ]
            for i in range(transform.shape[1])
        ]
        for transform in transforms
    ]

    raw_groups = raw_by_isolated(basis_indices)
    raw_group_keys = sorted(raw_groups)
    pulled_groups = []
    for key in raw_group_keys:
        raw = raw_groups[key]
        blocks = []
        for transform in transforms:
            matrix = np.asarray(transform.T @ raw @ transform, dtype=np.int64)
            blocks.append([
                [int(i), int(j), int(matrix[i, j])]
                for i, j in zip(*np.nonzero(matrix))
            ])
        pulled_groups.append(blocks)

    payload = {
        **expected,
        "raw_group_keys": raw_group_keys,
        "pulled_groups": pulled_groups,
        "audited_certificates": audited,
    }
    output = Path(args.output)
    write_json_if_changed(output, payload)

    # Lean elaboration retains every decoded value until the current module is
    # finished.  Decoding this payload seven times in one module therefore has
    # a much larger peak than the half-megabyte file suggests.  Emit small,
    # independently compilable sidecars so each decoder can be kernel-checked
    # and cached in its own Lean process.
    sidecar_stem = output.with_suffix("")
    sidecars: list[Path] = []

    basis_output = Path(f"{sidecar_stem}_basis.json")
    write_json_if_changed(
        basis_output,
        {
            "basis_indices": expected["basis_indices"],
            "raw_group_keys": raw_group_keys,
        },
    )
    sidecars.append(basis_output)

    for name in names:
        young_output = Path(f"{sidecar_stem}_young_{name}.json")
        write_json_if_changed(
            young_output,
            {"data": expected["young_bases"][name]},
        )
        sidecars.append(young_output)

    for name, columns in zip(names, sparse_columns):
        sparse_output = Path(f"{sidecar_stem}_young_sparse_{name}.json")
        write_json_if_changed(
            sparse_output,
            {"columns": columns},
        )
        sidecars.append(sparse_output)

    group_chunk_size = 12
    for start in range(0, len(pulled_groups), group_chunk_size):
        stop = min(start + group_chunk_size, len(pulled_groups))
        group_output = Path(
            f"{sidecar_stem}_groups_{start:03d}_{stop - 1:03d}.json"
        )
        write_json_if_changed(
            group_output,
            {
                "start": start,
                "pulled_groups": pulled_groups[start:stop],
            },
        )
        sidecars.append(group_output)

    # The kernel check for a complete transformed-basis column can retain the
    # whole nested sum at once.  Export exact contributions from at most six
    # nonzero entries of the left Young column so Lean can check the same
    # identity in genuinely small pieces.  A second, cheap Lean check sums
    # these pieces and compares them with ``pulled_groups`` above.
    pair_group = np.full((len(basis_indices), len(basis_indices)), -1, dtype=np.int64)
    for group, key in enumerate(raw_group_keys):
        rows, columns = np.nonzero(raw_groups[key])
        pair_group[rows, columns] = group
    if np.any(pair_group < 0):
        raise AssertionError("raw graph groups do not partition all flag pairs")

    pull_part_nonzeros = 0
    pull_part_sidecars: list[Path] = []
    pull_full_sidecars: list[Path] = []
    for block_index, (name, transform, columns) in enumerate(
        zip(names, transforms, sparse_columns)
    ):
        dim = transform.shape[1]
        for column_index, left_column in enumerate(columns):
            pull_part_size = (
                6 if name in {"4", "1111"} or len(left_column) <= 6 else 4
            )
            combined: dict[tuple[int, int], int] = {}
            for part_start in range(0, len(left_column), pull_part_size):
                part_stop = min(part_start + pull_part_size, len(left_column))
                coefficients: dict[tuple[int, int], int] = {}
                for a, left_value in left_column[part_start:part_stop]:
                    for right_index, right_column in enumerate(columns):
                        for b, right_value in right_column:
                            group = int(pair_group[a, b])
                            key = (group, right_index)
                            coefficients[key] = (
                                coefficients.get(key, 0)
                                + int(left_value) * int(right_value)
                            )
                entries = [
                    [group, right_index, value]
                    for (group, right_index), value in sorted(coefficients.items())
                    if value != 0
                ]
                for group, right_index, value in entries:
                    key = (group, right_index)
                    combined[key] = combined.get(key, 0) + value

                part_output = Path(
                    f"{sidecar_stem}_young_pull_part_{name}_column_"
                    f"{column_index:03d}_entries_{part_start:02d}_{part_stop - 1:02d}.json"
                )
                write_json_if_changed(
                    part_output,
                    {
                        "part_start": part_start,
                        "part_count": part_stop - part_start,
                        "entries": entries,
                    },
                )
                sidecars.append(part_output)
                pull_part_sidecars.append(part_output)
                pull_part_nonzeros += len(entries)

            expected_column = {}
            for group, blocks in enumerate(pulled_groups):
                for row, right_index, value in blocks[block_index]:
                    if row == column_index:
                        expected_column[(group, right_index)] = value
            combined = {key: value for key, value in combined.items() if value != 0}
            if combined != expected_column:
                raise AssertionError(
                    f"partial pullback mismatch for block {name}, column {column_index}"
                )
            full_output = Path(
                f"{sidecar_stem}_young_pull_full_{name}_column_"
                f"{column_index:03d}.json"
            )
            write_json_if_changed(
                full_output,
                {
                    "entries": [
                        [group, right_index, value]
                        for (group, right_index), value in sorted(expected_column.items())
                    ]
                },
            )
            sidecars.append(full_output)
            pull_full_sidecars.append(full_output)

    print(
        f"wrote {output}: certificates={len(audited)} "
        f"basis={len(expected['basis_indices'])} groups={len(raw_group_keys)} "
        f"pulled_nonzeros={sum(len(block) for group in pulled_groups for block in group)} "
        f"pull_parts={len(pull_part_sidecars)} "
        f"pull_part_nonzeros={pull_part_nonzeros} "
        f"pull_full_columns={len(pull_full_sidecars)} "
        f"bytes={output.stat().st_size} sidecars={len(sidecars)} "
        f"max_sidecar_bytes={max(path.stat().st_size for path in sidecars)}"
    )


if __name__ == "__main__":
    main()
