"""Generate bounded checks for S4 fixed-density group arithmetic.

This layer reconstructs every claimed *common* group total directly from the
kernel-checked common Gram entries and the shared sparse Young pullback.  The
exceptional correction contribution remains a separate proof layer; keeping
the common audit independent makes the large majority of each certificate
checkable even if that later layer needs repair.
"""

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
    raise AssertionError(f"missing group row {row}")


def fin(expression: str, bound: int) -> str:
    return f"⟨({expression}) % {bound}, Nat.mod_lt _ (by decide)⟩"


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
    denominator = int(meta["common_correction_denominator"])
    factor_rows = []
    for header in manifest["header_blocks"]:
        factor_payload = json.loads(
            (directory / str(header["factor_file"])).read_text(encoding="utf-8")
        )
        factor_rows.append(len(factor_payload["data"]))
    expected_rows = [2 * dimension for dimension in YOUNG_DIMS] + list(YOUNG_DIMS)
    if factor_rows != expected_rows:
        raise AssertionError((factor_rows, expected_rows))

    lean_root = Path(args.lean_root)
    lean_root.mkdir(parents=True, exist_ok=True)
    tag = f"S4{args.tag}"
    namespace = f"{tag}CommonGroupChecks"
    base_module = f"{tag}CommonGroupCheckBase"
    imports = [f"{PREFIX}.S4YoungData"] + [
        f"{PREFIX}.{tag}Block{block:02d}CheckBase" for block in range(10)
    ]

    block_definitions: list[str] = []
    total_names: dict[int, list[str]] = {slot: [] for slot in range(4)}
    for block in range(10):
        young_block = block % 5
        dimension = YOUNG_DIMS[young_block]
        rows = factor_rows[block]
        slots = range(3) if block < 5 else (3,)
        for slot in slots:
            if slot == 0 or slot == 3:
                left = fin("i", rows)
                right = fin("j", rows)
                body = (
                    f"{tag}Block{block:02d}Checks.claimedCommonGramScaled "
                    f"{left} {right}"
                )
            elif slot == 1:
                left0 = fin("i", rows)
                right1 = fin(f"{dimension} + j", rows)
                left1 = fin(f"{dimension} + i", rows)
                right0 = fin("j", rows)
                body = (
                    f"{tag}Block{block:02d}Checks.claimedCommonGramScaled "
                    f"{left0} {right1} +\n      "
                    f"{tag}Block{block:02d}Checks.claimedCommonGramScaled "
                    f"{left1} {right0}"
                )
            else:
                left = fin(f"{dimension} + i", rows)
                right = fin(f"{dimension} + j", rows)
                body = (
                    f"{tag}Block{block:02d}Checks.claimedCommonGramScaled "
                    f"{left} {right}"
                )
            name = f"commonBlock{block:02d}Slot{slot}Numerator"
            total_names[slot].append(name)
            block_definitions.append(
                f"""def {name} (row : Nat) : Int :=
  groupEntrySum (S4YoungData.pulledGroupEntries (groupFin row) {young_block})
    (fun i j =>
      {body})
"""
            )

    total_cases = []
    for slot in range(4):
        expression = " +\n      ".join(f"{name} row" for name in total_names[slot])
        total_cases.append(f"  | {slot} =>\n      {expression}")
    base_source = f"""{'\n'.join(f'import {module}' for module in imports)}

namespace {PREFIX}.{namespace}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

def commonCorrectionDenominator : Nat := {denominator}

def groupFin (row : Nat) : Fin 143 :=
  ⟨row % 143, Nat.mod_lt _ (by decide)⟩

private def entryCoordinate (entry : Array Int) (coordinate : Nat) : Nat :=
  ((entry[coordinate]?).getD 0).toNat

private def entryValue (entry : Array Int) : Int :=
  (entry[2]?).getD 0

def groupEntrySum (entries : Array (Array Int)) (value : Nat → Nat → Int) : Int :=
  entries.foldl (fun total entry =>
    total + 24 * entryValue entry *
      value (entryCoordinate entry 0) (entryCoordinate entry 1)) 0

{chr(10).join(block_definitions)}
def commonGroupNumerator (row slot : Nat) : Int :=
  match slot with
{chr(10).join(total_cases)}
  | _ => 0

end {PREFIX}.{namespace}
"""
    write_if_changed(lean_root / f"{base_module}.lean", base_source)

    targets = [f"{PREFIX}.{base_module}"]
    row_modules: list[str] = []
    for row in range(143):
        data_module, local_row = group_location(tag, manifest["group_chunks"], row)
        module = f"{tag}CommonGroupRow{row:03d}Check"
        row_namespace = f"{namespace}.Row{row:03d}"
        source = f"""import {PREFIX}.{base_module}
import {PREFIX}.{data_module}

namespace {PREFIX}.{row_namespace}

open {PREFIX}.{namespace}

def storedNumerator (slot : Nat) : Int :=
  {data_module}.commonTotalComponent {local_row} slot 0

def storedDenominator (slot : Nat) : Int :=
  {data_module}.commonTotalComponent {local_row} slot 1

def slotValid (slot : Nat) : Bool :=
  commonGroupNumerator {row} slot * storedDenominator slot ==
    storedNumerator slot * (commonCorrectionDenominator : Int)

def rowValid : Bool := (List.range 4).all slotValid

theorem common_group_row_{row:03d}_valid : rowValid = true := by decide +kernel

end {PREFIX}.{row_namespace}
"""
        write_if_changed(lean_root / f"{module}.lean", source)
        targets.append(f"{PREFIX}.{module}")
        row_modules.append(module)

    umbrella = f"{tag}CommonGroupChecks"
    umbrella_imports = "\n".join(
        f"import {PREFIX}.{module}" for module in row_modules
    )
    fields = "\n".join(
        f"  row{row:03d} : Row{row:03d}.rowValid = true" for row in range(143)
    )
    witnesses = "\n".join(
        f"  row{row:03d} := Row{row:03d}.common_group_row_{row:03d}_valid"
        for row in range(143)
    )
    umbrella_source = f"""{umbrella_imports}

namespace {PREFIX}.{namespace}

structure CommonGroupTotalsVerified : Prop where
{fields}

theorem common_group_totals_verified : CommonGroupTotalsVerified where
{witnesses}

end {PREFIX}.{namespace}
"""
    write_if_changed(lean_root / f"{umbrella}.lean", umbrella_source)
    targets.append(f"{PREFIX}.{umbrella}")

    target_file = directory / f"{manifest_path.stem}_common_group_check_targets.txt"
    write_if_changed(target_file, "\n".join(targets) + "\n")
    print(
        f"wrote {len(row_modules)} common-group checks, "
        f"umbrella={PREFIX}.{umbrella}, targets={target_file}"
    )


if __name__ == "__main__":
    main()
