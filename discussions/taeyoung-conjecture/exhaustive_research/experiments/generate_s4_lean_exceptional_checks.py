"""Generate common-denominator exceptional and DD checks for an S4 witness."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


PREFIX = "Taeyoung.Methods.RootedSOS"


def write_if_changed(path: Path, contents: str) -> None:
    if path.exists() and path.read_text(encoding="utf-8") == contents:
        return
    path.write_text(contents, encoding="utf-8")


def source_literal(filename: str) -> str:
    return 'include_str ".."/".."/".."/".."/"experiments"/' + f'"{filename}"'


def chunk_module(tag: str, block: int, start: int, stop: int) -> str:
    return (
        f"{tag}ExceptionalScaledBlock{block:02d}"
        f"Chunk{start:03d}_{stop - 1:03d}Data"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest")
    parser.add_argument("--tag", required=True)
    parser.add_argument("--lean-root", default="lean/Taeyoung/Methods/RootedSOS")
    args = parser.parse_args()
    if re.fullmatch(r"[A-Z][A-Za-z0-9]*", args.tag) is None:
        raise ValueError(f"invalid Lean tag: {args.tag}")

    manifest_path = Path(args.manifest)
    directory = manifest_path.parent
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    meta = json.loads(
        (directory / str(manifest["meta"]["file"])).read_text(encoding="utf-8")
    )
    lean_root = Path(args.lean_root)
    lean_root.mkdir(parents=True, exist_ok=True)
    tag = f"S4{args.tag}"
    common_denominator = int(meta["common_correction_denominator"])
    targets: list[str] = []
    aggregate_modules: list[str] = []

    for block, header in enumerate(manifest["header_blocks"]):
        order = int(meta["orders"][block])
        scale_file = str(header["exceptional_scale_file"])
        scale_module = f"{tag}ExceptionalScaleBlock{block:02d}Data"
        scale_source = f"""import {PREFIX}.S4JsonData

namespace {PREFIX}.{scale_module}

set_option maxRecDepth 1000000

private def source : String :=
  {source_literal(scale_file)}

def denominator : Nat :=
  eval% S4JsonData.decodeFieldFrom source "denominator"
def commonMultiplier : Nat :=
  eval% S4JsonData.decodeFieldFrom source "common_multiplier"
def ddMarginScaled : Int :=
  eval% S4JsonData.decodeFieldFrom source "dd_margin_scaled"

def shapeValid : Bool :=
  denominator == commonMultiplier * {common_denominator} &&
    decide (0 < denominator) &&
    decide (0 < ddMarginScaled)

theorem shape_valid : shapeValid = true := by decide +kernel

theorem denominator_positive : 0 < denominator := by
  have h : decide (0 < denominator) = true := by decide +kernel
  exact of_decide_eq_true h

end {PREFIX}.{scale_module}
"""
        write_if_changed(lean_root / f"{scale_module}.lean", scale_source)
        targets.append(f"{PREFIX}.{scale_module}")

        chunks = [
            descriptor for descriptor in manifest["exceptional_scaled_chunks"]
            if int(descriptor["block"]) == block
        ]
        chunk_modules: list[str] = []
        exceptional_count = 0
        for descriptor in chunks:
            start = int(descriptor["start"])
            stop = int(descriptor["stop"])
            exceptional_count += stop - start
            filename = str(descriptor["file"])
            module = chunk_module(tag, block, start, stop)
            chunk_source = f"""import {PREFIX}.S4JsonData

namespace {PREFIX}.{module}

set_option maxRecDepth 1000000

private def source : String :=
  {source_literal(filename)}

def data : Array (Array Int) :=
  eval% S4JsonData.decodeFieldFrom source "data"

def shapeValid : Bool :=
  data.size == {stop - start} && data.all (fun entry => entry.size == 3)

theorem shape_valid : shapeValid = true := by decide +kernel

end {PREFIX}.{module}
"""
            write_if_changed(lean_root / f"{module}.lean", chunk_source)
            targets.append(f"{PREFIX}.{module}")
            chunk_modules.append(module)

        dispatch = "#[]"
        for descriptor in reversed(chunks):
            start = int(descriptor["start"])
            stop = int(descriptor["stop"])
            module = chunk_module(tag, block, start, stop)
            dispatch = (
                f"if index < {stop} then\n"
                f"    ({module}.data[index - {start}]?).getD #[]\n"
                f"  else {dispatch}"
            )

        data_module = f"{tag}Block{block:02d}Data"
        base_module = f"{tag}ExceptionalBlock{block:02d}CheckBase"
        imports = [
            f"import {PREFIX}.ScaledCorrection",
            f"import {PREFIX}.{data_module}",
            f"import {PREFIX}.{scale_module}",
        ] + [f"import {PREFIX}.{module}" for module in chunk_modules]
        import_lines = "\n".join(imports)
        base_source = f"""{import_lines}

/-! Integer-scaled exceptional corrections and DD checks for block {block}. -/

namespace {PREFIX}.{tag}ExceptionalBlock{block:02d}Checks

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

abbrev order : Nat := {order}
abbrev exceptionalCount : Nat := {exceptional_count}
abbrev denominator : Nat := {scale_module}.denominator
abbrev commonMultiplier : Nat := {scale_module}.commonMultiplier
abbrev ddMarginScaled : Int := {scale_module}.ddMarginScaled

def exceptionalEntry (index : Nat) : Array Int :=
  {dispatch}

private def entryCoordinate (entry : Array Int) (coordinate : Nat) : Nat :=
  ((entry[coordinate]?).getD 0).toNat

private def entryValue (entry : Array Int) : Int :=
  (entry[2]?).getD 0

def exceptionalScaled (row col : Nat) : Int :=
  (List.range exceptionalCount).foldl (fun total index =>
    let entry := exceptionalEntry index
    let i := entryCoordinate entry 0
    let j := entryCoordinate entry 1
    if (i == row && j == col) || (i == col && j == row) then
      total + entryValue entry
    else total) 0

def correctionScaled (row col : Fin order) : Int :=
  commonMultiplier * {data_module}.commonCorrectionScaled row.1 col.1 +
    exceptionalScaled row.1 col.1

def correctionRat (row col : Fin order) : Rat :=
  scaledRatCorrection denominator correctionScaled row col

def rowCertificateValid (row : Fin order) : Bool :=
  decide (
    (((∑ col : Fin order,
        if row = col then 0 else (correctionScaled row col).natAbs : Nat) : Int) ≤
      (denominator : Int) + correctionScaled row row) ∧
    ∀ col : Fin order, correctionScaled row col = correctionScaled col row)

end {PREFIX}.{tag}ExceptionalBlock{block:02d}Checks
"""
        write_if_changed(lean_root / f"{base_module}.lean", base_source)
        targets.append(f"{PREFIX}.{base_module}")

        row_modules: list[str] = []
        theorem_names: list[str] = []
        namespace = f"{tag}ExceptionalBlock{block:02d}Checks"
        for row in range(order):
            module = f"{tag}ExceptionalBlock{block:02d}CheckRow{row:03d}"
            theorem = f"diagonal_dominance_row_{row:03d}"
            row_source = f"""import {PREFIX}.{base_module}

namespace {PREFIX}.{namespace}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem {theorem} : rowCertificateValid {row} = true := by
  decide +kernel

end {PREFIX}.{namespace}
"""
            write_if_changed(lean_root / f"{module}.lean", row_source)
            targets.append(f"{PREFIX}.{module}")
            row_modules.append(module)
            theorem_names.append(theorem)

        theorem_cases = "\n".join(
            f"  | {row} => by\n"
            f"      have hr : row = ({row} : Fin order) := by\n"
            f"        apply Fin.ext\n"
            f"        exact hrow\n"
            f"      simpa [hr] using {theorem}"
            for row, theorem in enumerate(theorem_names)
        )
        impossible_pattern = "Nat.succ (" * order + "k" + ")" * order
        aggregate_module = f"{tag}ExceptionalBlock{block:02d}Checks"
        row_import_lines = "\n".join(
            f"import {PREFIX}.{module}" for module in row_modules
        )
        aggregate_source = f"""{row_import_lines}

namespace {PREFIX}.{namespace}

theorem scale_shape_valid : {scale_module}.shapeValid = true :=
  {scale_module}.shape_valid

theorem all_diagonal_dominance_rows_valid :
    ∀ row : Fin order, rowCertificateValid row = true := by
  intro row
  exact match hrow : row.1 with
{theorem_cases}
  | {impossible_pattern} => by
      have hlt := row.isLt
      simp only [order] at hlt
      omega

theorem denominator_positive : 0 < denominator :=
  {scale_module}.denominator_positive

theorem diagonal_dominance :
    ∀ row : Fin order,
      ((∑ col : Fin order,
        if row = col then 0 else (correctionScaled row col).natAbs : Nat) : Int) ≤
          (denominator : Int) + correctionScaled row row := by
  intro row
  have h :
      (((∑ col : Fin order,
        if row = col then 0 else (correctionScaled row col).natAbs : Nat) : Int) ≤
          (denominator : Int) + correctionScaled row row) ∧
        ∀ col : Fin order, correctionScaled row col = correctionScaled col row := by
    apply of_decide_eq_true
    simpa only [rowCertificateValid] using all_diagonal_dominance_rows_valid row
  exact h.1

theorem correction_scaled_symm :
    ∀ row col : Fin order, correctionScaled row col = correctionScaled col row := by
  intro row col
  have h :
      (((∑ col : Fin order,
        if row = col then 0 else (correctionScaled row col).natAbs : Nat) : Int) ≤
          (denominator : Int) + correctionScaled row row) ∧
        ∀ col : Fin order, correctionScaled row col = correctionScaled col row := by
    apply of_decide_eq_true
    simpa only [rowCertificateValid] using all_diagonal_dominance_rows_valid row
  exact h.2 col

theorem correction_rat_symm :
    ∀ row col : Fin order, correctionRat row col = correctionRat col row :=
  scaledRatCorrection_symm denominator correctionScaled correction_scaled_symm

theorem gram_nonneg
    {{A : Type*}} [Fintype A] (F : A → Fin order → Real) (v : A → Real) :
    0 ≤ factoredRatGramForm F correctionRat v := by
  exact scaledRatGram_nonneg denominator correctionScaled denominator_positive
    correction_scaled_symm diagonal_dominance F v

end {PREFIX}.{namespace}
"""
        write_if_changed(lean_root / f"{aggregate_module}.lean", aggregate_source)
        targets.append(f"{PREFIX}.{aggregate_module}")
        aggregate_modules.append(aggregate_module)

    umbrella = f"{tag}ExceptionalChecks"
    bundle_namespace = f"{tag}ExceptionalChecks"
    fields = []
    witnesses = []
    for block in range(10):
        check = f"{tag}ExceptionalBlock{block:02d}Checks"
        fields.extend((
            f"  denominator{block:02d} : 0 < {check}.denominator",
            f"  symmetry{block:02d} : ∀ row col : Fin {check}.order,\n"
            f"    {check}.correctionScaled row col = {check}.correctionScaled col row",
            f"  dominance{block:02d} : ∀ row : Fin {check}.order,\n"
            f"    ((∑ col : Fin {check}.order, if row = col then 0 else\n"
            f"      ({check}.correctionScaled row col).natAbs : Nat) : Int) ≤\n"
            f"      ({check}.denominator : Int) + {check}.correctionScaled row row",
        ))
        witnesses.extend((
            f"  denominator{block:02d} := {check}.denominator_positive",
            f"  symmetry{block:02d} := {check}.correction_scaled_symm",
            f"  dominance{block:02d} := {check}.diagonal_dominance",
        ))
    umbrella_source = (
        "\n".join(f"import {PREFIX}.{module}" for module in aggregate_modules)
        + f"""

namespace {PREFIX}.{bundle_namespace}

open Finset
open scoped BigOperators

structure ExceptionalPSDVerified : Prop where
{chr(10).join(fields)}

theorem exceptional_psd_verified : ExceptionalPSDVerified where
{chr(10).join(witnesses)}

end {PREFIX}.{bundle_namespace}
"""
    )
    write_if_changed(
        lean_root / f"{umbrella}.lean",
        umbrella_source,
    )
    targets.append(f"{PREFIX}.{umbrella}")
    target_file = directory / f"{manifest_path.stem}_exceptional_check_targets.txt"
    write_if_changed(target_file, "\n".join(targets) + "\n")
    print(
        f"wrote {len(targets)} exceptional-check modules, "
        f"umbrella={PREFIX}.{umbrella}, targets={target_file}"
    )


if __name__ == "__main__":
    main()
