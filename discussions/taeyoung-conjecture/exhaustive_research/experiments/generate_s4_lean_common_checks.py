"""Generate bounded row-local Lean checks for one split S4 certificate.

Each generated theorem asks Lean's kernel to evaluate one factor row.  Keeping
rows in separate modules prevents the large positional integers from all being
retained by one elaboration process.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


PREFIX = "Taeyoung.Methods.RootedSOS"
CHECK_CHUNK_SIZE = 96


def write_if_changed(path: Path, contents: str) -> None:
    if path.exists() and path.read_text(encoding="utf-8") == contents:
        return
    path.write_text(contents, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest")
    parser.add_argument("--tag", required=True, help="Lean-safe tag, e.g. Atlas118")
    parser.add_argument("--lean-root", default="lean/Taeyoung/Methods/RootedSOS")
    parser.add_argument("--target-list")
    args = parser.parse_args()

    if re.fullmatch(r"[A-Z][A-Za-z0-9]*", args.tag) is None:
        raise ValueError(f"invalid Lean tag: {args.tag}")

    manifest_path = Path(args.manifest)
    directory = manifest_path.parent
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    meta_file = directory / str(manifest["meta"]["file"])
    meta = json.loads(meta_file.read_text(encoding="utf-8"))
    lean_root = Path(args.lean_root)
    lean_root.mkdir(parents=True, exist_ok=True)
    tag = f"S4{args.tag}"
    targets: list[str] = []
    aggregate_modules: list[str] = []

    for block, header in enumerate(manifest["header_blocks"]):
        factor_payload = json.loads(
            (directory / str(header["factor_file"])).read_text(encoding="utf-8")
        )
        rows = len(factor_payload["data"])
        order = int(meta["orders"][block])
        denominator = int(meta["common_correction_denominator"])
        data_module = f"{tag}Block{block:02d}Data"
        check_namespace = f"{tag}Block{block:02d}Checks"
        base_module = f"{tag}Block{block:02d}CheckBase"
        base_source = f"""import {PREFIX}.EncodedGram
import {PREFIX}.{data_module}

/-! Row-local exact arithmetic for certificate block {block}. -/

open Finset
open scoped BigOperators

namespace {PREFIX}.{check_namespace}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

abbrev order : Nat := {order}
abbrev factorRows : Nat := {rows}
def commonCorrectionDenominator : Nat := {denominator}

def FInt (a : Fin factorRows) (j : Fin order) : Int :=
  {data_module}.factor a.1 j.1

def claimedCommonCScaled (i j : Fin order) : Int :=
  {data_module}.commonCorrectionScaled i.1 j.1

def claimedIntermediateScaled (a : Fin factorRows) (j : Fin order) : Int :=
  {data_module}.intermediateScaled a.1 j.1

def claimedCommonGramScaled (a b : Fin factorRows) : Int :=
  {data_module}.commonGramScaled a.1 b.1

def intermediateEntryValid (row : Fin factorRows) (col : Fin order) : Bool :=
  claimedIntermediateScaled row col ==
    expectedIntermediate commonCorrectionDenominator FInt
      claimedCommonCScaled row col

def gramEntryValid (row col : Fin factorRows) : Bool :=
  claimedCommonGramScaled row col ==
    expectedGram FInt claimedIntermediateScaled row col

end {PREFIX}.{check_namespace}
"""
        write_if_changed(lean_root / f"{base_module}.lean", base_source)
        targets.append(f"{PREFIX}.{base_module}")

        row_modules: list[str] = []
        intermediate_row_theorems: list[str] = []
        gram_row_theorems: list[str] = []
        for row in range(rows):
            chunk_modules: list[str] = []
            for kind, count, function, fin_type in (
                ("Intermediate", order, "intermediateEntryValid", "order"),
                ("Gram", rows, "gramEntryValid", "factorRows"),
            ):
                for start in range(0, count, CHECK_CHUNK_SIZE):
                    stop = min(start + CHECK_CHUNK_SIZE, count)
                    chunk_module = (
                        f"{tag}Block{block:02d}CheckRow{row:03d}{kind}"
                        f"Cols{start:03d}_{stop - 1:03d}"
                    )
                    columns = ", ".join(map(str, range(start, stop)))
                    entry_theorems = "\n\n".join(
                        f"theorem {function}_{row:03d}_{col:03d} :\n"
                        f"    {function} {row} {col} = true := by\n"
                        f"  have h := chunk_valid\n"
                        f"  simp only [chunkValid, List.all_eq_true] at h\n"
                        f"  exact h _ (by simp [columns])"
                        for col in range(start, stop)
                    )
                    chunk_source = f"""import {PREFIX}.{base_module}

namespace {PREFIX}.{check_namespace}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def columns : List (Fin {fin_type}) := [{columns}]

private def chunkValid : Bool := columns.all ({function} {row})

private theorem chunk_valid : chunkValid = true := by
  decide +kernel

{entry_theorems}

end {PREFIX}.{check_namespace}
"""
                    write_if_changed(lean_root / f"{chunk_module}.lean", chunk_source)
                    targets.append(f"{PREFIX}.{chunk_module}")
                    chunk_modules.append(chunk_module)

            intermediate_cases = "\n".join(
                f"  | {col} => by\n"
                f"      have hc : col = ({col} : Fin order) := by\n"
                f"        apply Fin.ext\n"
                f"        exact hcol\n"
                f"      simpa [hc] using intermediateEntryValid_{row:03d}_{col:03d}"
                for col in range(order)
            )
            gram_cases = "\n".join(
                f"  | {col} => by\n"
                f"      have hc : col = ({col} : Fin factorRows) := by\n"
                f"        apply Fin.ext\n"
                f"        exact hcol\n"
                f"      simpa [hc] using gramEntryValid_{row:03d}_{col:03d}"
                for col in range(rows)
            )
            intermediate_impossible = "Nat.succ (" * order + "k" + ")" * order
            gram_impossible = "Nat.succ (" * rows + "k" + ")" * rows
            intermediate_row_theorem = f"all_intermediate_row_{row:03d}_valid"
            gram_row_theorem = f"all_gram_row_{row:03d}_valid"
            row_module = f"{tag}Block{block:02d}CheckRow{row:03d}"
            chunk_imports = "\n".join(
                f"import {PREFIX}.{module}" for module in chunk_modules
            )
            row_source = f"""{chunk_imports}

namespace {PREFIX}.{check_namespace}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem {intermediate_row_theorem} (col : Fin order) :
    intermediateEntryValid {row} col = true := by
  exact match hcol : col.1 with
{intermediate_cases}
  | {intermediate_impossible} => by
      have hlt := col.isLt
      simp only [order] at hlt
      omega

theorem {gram_row_theorem} (col : Fin factorRows) :
    gramEntryValid {row} col = true := by
  exact match hcol : col.1 with
{gram_cases}
  | {gram_impossible} => by
      have hlt := col.isLt
      simp only [factorRows] at hlt
      omega

end {PREFIX}.{check_namespace}
"""
            write_if_changed(lean_root / f"{row_module}.lean", row_source)
            targets.append(f"{PREFIX}.{row_module}")
            row_modules.append(row_module)
            intermediate_row_theorems.append(intermediate_row_theorem)
            gram_row_theorems.append(gram_row_theorem)

        aggregate_module = f"{tag}Block{block:02d}Checks"
        aggregate_imports = "\n".join(
            f"import {PREFIX}.{module}" for module in row_modules
        )
        intermediate_row_cases = "\n".join(
            f"  | {row} => by\n"
            f"      have hr : row = ({row} : Fin factorRows) := by\n"
            f"        apply Fin.ext\n"
            f"        exact hrow\n"
            f"      simpa [hr] using {theorem} col"
            for row, theorem in enumerate(intermediate_row_theorems)
        )
        gram_row_cases = "\n".join(
            f"  | {row} => by\n"
            f"      have hr : row = ({row} : Fin factorRows) := by\n"
            f"        apply Fin.ext\n"
            f"        exact hrow\n"
            f"      simpa [hr] using {theorem} col"
            for row, theorem in enumerate(gram_row_theorems)
        )
        impossible_pattern = "Nat.succ (" * rows + "k" + ")" * rows
        aggregate_source = f"""{aggregate_imports}

namespace {PREFIX}.{check_namespace}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem metadata_valid : {data_module}.metadataValid = true :=
  {data_module}.metadata_valid

theorem all_intermediate_entries_valid (row : Fin factorRows) (col : Fin order) :
    intermediateEntryValid row col = true := by
  exact match hrow : row.1 with
{intermediate_row_cases}
  | {impossible_pattern} => by
      have hlt := row.isLt
      simp only [factorRows] at hlt
      omega

theorem all_gram_entries_valid (row col : Fin factorRows) :
    gramEntryValid row col = true := by
  exact match hrow : row.1 with
{gram_row_cases}
  | {impossible_pattern} => by
      have hlt := row.isLt
      simp only [factorRows] at hlt
      omega

end {PREFIX}.{check_namespace}
"""
        write_if_changed(lean_root / f"{aggregate_module}.lean", aggregate_source)
        targets.append(f"{PREFIX}.{aggregate_module}")
        aggregate_modules.append(aggregate_module)

    umbrella = f"{tag}CommonChecks"
    umbrella_source = "\n".join(
        f"import {PREFIX}.{module}" for module in aggregate_modules
    ) + f"\n\n/-! Complete row-local common-Gram audit for {args.tag}. -/\n"
    write_if_changed(lean_root / f"{umbrella}.lean", umbrella_source)
    targets.append(f"{PREFIX}.{umbrella}")

    target_list = Path(args.target_list) if args.target_list else (
        directory / f"{manifest_path.stem}_common_check_targets.txt"
    )
    write_if_changed(target_list, "\n".join(targets) + "\n")
    print(
        f"wrote {len(targets)} common-check modules, "
        f"rows={sum(len(json.loads((directory / str(item['factor_file'])).read_text(encoding='utf-8'))['data']) for item in manifest['header_blocks'])}, "
        f"umbrella={PREFIX}.{umbrella}, targets={target_list}"
    )


if __name__ == "__main__":
    main()
