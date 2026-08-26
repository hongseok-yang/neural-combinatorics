"""Generate bounded reconstruction of the exceptional S4 group totals."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


PREFIX = "Taeyoung.Methods.RootedSOS"
YOUNG_DIMS = (32, 52, 34, 30, 6)


def write_if_changed(path: Path, contents: str) -> None:
    if path.exists() and path.read_text(encoding="utf-8") == contents:
        return
    path.write_text(contents, encoding="utf-8")


def exceptional_group_module(tag: str, descriptor: dict[str, object]) -> str:
    block = int(descriptor["block"])
    start = int(descriptor["start"])
    stop = int(descriptor["stop"])
    return (
        f"{tag}ExceptionalGroupScaledBlock{block:02d}"
        f"Rows{start:03d}_{stop - 1:03d}Data"
    )


def exceptional_group_location(
    tag: str,
    descriptors: list[dict[str, object]],
    block: int,
    row: int,
) -> tuple[str, int]:
    for descriptor in descriptors:
        if int(descriptor["block"]) != block:
            continue
        start = int(descriptor["start"])
        stop = int(descriptor["stop"])
        if start <= row < stop:
            return exceptional_group_module(tag, descriptor), row - start
    raise AssertionError((block, row, "missing exceptional group row"))


def group_module(tag: str, descriptor: dict[str, object]) -> str:
    start = int(descriptor["start"])
    stop = int(descriptor["stop"])
    return f"{tag}GroupRows{start:03d}_{stop - 1:03d}Data"


def group_location(
    tag: str, descriptors: list[dict[str, object]], row: int
) -> tuple[str, int]:
    for descriptor in descriptors:
        start = int(descriptor["start"])
        stop = int(descriptor["stop"])
        if start <= row < stop:
            return group_module(tag, descriptor), row - start
    raise AssertionError(row)


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
    lean_root = Path(args.lean_root)
    lean_root.mkdir(parents=True, exist_ok=True)
    tag = f"S4{args.tag}"
    namespace = f"{tag}ExceptionalGroupChecks"
    base_module = f"{tag}ExceptionalGroupCheckBase"
    imports = [f"{PREFIX}.S4YoungData"]
    imports.extend(
        f"{PREFIX}.{tag}ExceptionalBlock{block:02d}CheckBase"
        for block in range(10)
    )

    block_definitions: list[str] = []
    for block in range(10):
        young_block = block % 5
        dimension = YOUNG_DIMS[young_block]
        check = f"{tag}ExceptionalBlock{block:02d}Checks"
        data = f"{tag}Block{block:02d}Data"
        if block < 5:
            slot_product = f"""def block{block:02d}SlotProduct
    (slot i j u v : Nat) : Int :=
  match slot with
  | 0 => {data}.factor i u * {data}.factor j v
  | 1 =>
      {data}.factor i u * {data}.factor ({dimension} + j) v +
        {data}.factor ({dimension} + i) u * {data}.factor j v
  | 2 =>
      {data}.factor ({dimension} + i) u *
        {data}.factor ({dimension} + j) v
  | _ => 0
"""
        else:
            slot_product = f"""def block{block:02d}SlotProduct
    (slot i j u v : Nat) : Int :=
  if slot = 3 then {data}.factor i u * {data}.factor j v else 0
"""
        block_definitions.append(slot_product)
        block_definitions.append(
            f"""def block{block:02d}ExceptionalContribution
    (row slot exceptionIndex : Nat) : Int :=
  let exception := {check}.exceptionalEntry exceptionIndex
  let u := entryCoordinate exception 0
  let v := entryCoordinate exception 1
  let correction := entryValue exception
  let entries := S4YoungData.pulledGroupEntries (groupFin row) {young_block}
  if u = v then
    correction * groupEntrySum entries
      (fun i j => block{block:02d}SlotProduct slot i j u v)
  else
    correction * groupEntrySum entries
      (fun i j => block{block:02d}SlotProduct slot i j u v +
        block{block:02d}SlotProduct slot i j v u)

def block{block:02d}ExceptionalGroupScaled (row slot : Nat) : Int :=
  (List.range {check}.exceptionalCount).foldl
    (fun total index => total + block{block:02d}ExceptionalContribution row slot index) 0
"""
        )

    base_source = f"""{'\n'.join(f'import {module}' for module in imports)}

namespace {PREFIX}.{namespace}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

def groupFin (row : Nat) : Fin 143 :=
  ⟨row % 143, Nat.mod_lt _ (by decide)⟩

def entryCoordinate (entry : Array Int) (coordinate : Nat) : Nat :=
  ((entry[coordinate]?).getD 0).toNat

def entryValue (entry : Array Int) : Int :=
  (entry[2]?).getD 0

def groupEntrySum (entries : Array (Array Int)) (value : Nat → Nat → Int) : Int :=
  entries.foldl (fun total entry =>
    total + 24 * entryValue entry *
      value (entryCoordinate entry 0) (entryCoordinate entry 1)) 0

{chr(10).join(block_definitions)}
end {PREFIX}.{namespace}
"""
    write_if_changed(lean_root / f"{base_module}.lean", base_source)

    targets = [f"{PREFIX}.{base_module}"]
    row_modules: list[str] = []
    for row in range(143):
        locations = [
            exceptional_group_location(
                tag, manifest["exceptional_group_chunks"], block, row
            )
            for block in range(10)
        ]
        total_module, total_local_row = group_location(tag, manifest["group_chunks"], row)
        imports = [base_module, total_module]
        imports.extend(module for module, _ in locations)
        imports.extend(
            f"{tag}ExceptionalScaleBlock{block:02d}Data" for block in range(10)
        )
        imports = list(dict.fromkeys(imports))
        module = f"{tag}ExceptionalGroupRow{row:03d}Check"
        row_namespace = f"{namespace}.Row{row:03d}"
        claims = []
        block_checks = []
        block_theorems = []
        block_fields = []
        block_witnesses = []
        for block, (data_module, local_row) in enumerate(locations):
            claims.append(
                f"def claimedBlock{block:02d} (slot : Nat) : Int :=\n"
                f"  {data_module}.component {local_row} slot"
            )
            block_checks.append(
                f"def block{block:02d}Valid : Bool :=\n"
                f"  (List.range 4).all (fun slot =>\n"
                f"    block{block:02d}ExceptionalGroupScaled {row} slot == "
                f"claimedBlock{block:02d} slot)"
            )
            block_theorems.append(
                f"theorem block_{block:02d}_valid : block{block:02d}Valid = true := "
                f"by decide +kernel"
            )
            block_fields.append(f"  block{block:02d} : block{block:02d}Valid = true")
            block_witnesses.append(f"  block{block:02d} := block_{block:02d}_valid")
        exceptional_sum = " +\n    ".join(
            f"Rat.ofInt (claimedBlock{block:02d} slot) / "
            f"Rat.ofInt ({tag}ExceptionalScaleBlock{block:02d}Data.denominator : Int)"
            for block in range(10)
        )
        source = f"""{'\n'.join(f'import {PREFIX}.{name}' for name in imports)}

namespace {PREFIX}.{row_namespace}

open {PREFIX}.{namespace}

private def ratPair (numerator denominator : Int) : Rat :=
  Rat.ofInt numerator / Rat.ofInt denominator

{chr(10).join(claims)}

{chr(10).join(block_checks)}

{chr(10).join(block_theorems)}

def storedCommon (slot : Nat) : Rat :=
  ratPair ({total_module}.commonTotalComponent {total_local_row} slot 0)
    ({total_module}.commonTotalComponent {total_local_row} slot 1)

def storedFull (slot : Nat) : Rat :=
  ratPair ({total_module}.fullTotalComponent {total_local_row} slot 0)
    ({total_module}.fullTotalComponent {total_local_row} slot 1)

def rebuiltFull (slot : Nat) : Rat :=
  storedCommon slot +
    {exceptional_sum}

def fullGroupValid : Bool :=
  (List.range 4).all (fun slot => storedFull slot == rebuiltFull slot)

theorem full_group_valid : fullGroupValid = true := by decide +kernel

structure ExceptionalGroupRowVerified : Prop where
{chr(10).join(block_fields)}
  full : fullGroupValid = true

theorem exceptional_group_row_verified : ExceptionalGroupRowVerified where
{chr(10).join(block_witnesses)}
  full := full_group_valid

end {PREFIX}.{row_namespace}
"""
        write_if_changed(lean_root / f"{module}.lean", source)
        targets.append(f"{PREFIX}.{module}")
        row_modules.append(module)

    umbrella = f"{tag}ExceptionalGroupChecks"
    imports = "\n".join(f"import {PREFIX}.{module}" for module in row_modules)
    fields = "\n".join(
        f"  row{row:03d} : Row{row:03d}.ExceptionalGroupRowVerified"
        for row in range(143)
    )
    witnesses = "\n".join(
        f"  row{row:03d} := Row{row:03d}.exceptional_group_row_verified"
        for row in range(143)
    )
    source = f"""{imports}

namespace {PREFIX}.{namespace}

structure ExceptionalGroupTotalsVerified : Prop where
{fields}

theorem exceptional_group_totals_verified : ExceptionalGroupTotalsVerified where
{witnesses}

end {PREFIX}.{namespace}
"""
    write_if_changed(lean_root / f"{umbrella}.lean", source)
    targets.append(f"{PREFIX}.{umbrella}")

    target_file = directory / f"{manifest_path.stem}_exceptional_group_check_targets.txt"
    write_if_changed(target_file, "\n".join(targets) + "\n")
    print(
        f"wrote {len(row_modules)} exceptional-group checks, "
        f"umbrella={PREFIX}.{umbrella}, targets={target_file}"
    )


if __name__ == "__main__":
    main()
