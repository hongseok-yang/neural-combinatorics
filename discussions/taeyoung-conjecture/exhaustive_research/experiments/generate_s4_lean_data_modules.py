"""Generate one bounded-memory Lean decoder module per fine S4 sidecar.

The mathematical certificate remains the original exact JSON.  The exporter
derives a manifest of <=32 KB leaves; this script turns each leaf into a small
kernel-checked Lean constant and records a sequential target list.  Aggregate
modules only import cached leaves and never decode the large certificate.
"""

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


def camel(value: str) -> str:
    return "".join(part.capitalize() for part in value.split("_"))


def source_literal(filename: str) -> str:
    return (
        'include_str ".."/".."/".."/".."/"experiments"/'
        f'"{filename}"'
    )


def module_source(module: str, body: str) -> str:
    return f"""import {PREFIX}.S4JsonData

namespace {PREFIX}.{module}

set_option maxRecDepth 1000000

{body}

end {PREFIX}.{module}
"""


def decoded_def(filename: str, type_: str, field: str = "data") -> str:
    return f"""private def source : String :=
  {source_literal(filename)}

def data : {type_} := eval% S4JsonData.decodeFieldFrom source "{field}"
"""


def common_module_name(tag: str, descriptor: dict[str, object]) -> str:
    field = str(descriptor["field"])
    block = int(descriptor["block"])
    start = int(descriptor["start"])
    stop = int(descriptor["stop"])
    return (
        f"{tag}{camel(field)}Block{block:02d}"
        f"Chunk{start:03d}_{stop - 1:03d}Data"
    )


def exceptional_group_module_name(tag: str, descriptor: dict[str, object]) -> str:
    block = int(descriptor["block"])
    start = int(descriptor["start"])
    stop = int(descriptor["stop"])
    return (
        f"{tag}ExceptionalGroupScaledBlock{block:02d}"
        f"Rows{start:03d}_{stop - 1:03d}Data"
    )


def dispatch_array_rows(
    descriptors: list[dict[str, object]],
    tag: str,
    default: str,
    index: str = "row",
) -> str:
    """Lean expression selecting one row from contiguous decoded chunks."""
    result = default
    for descriptor in reversed(sorted(descriptors, key=lambda item: int(item["start"]))):
        start = int(descriptor["start"])
        stop = int(descriptor["stop"])
        module = common_module_name(tag, descriptor)
        result = (
            f"if {index} < {stop} then\n"
            f"    ({module}.data[{index} - {start}]?).getD {default}\n"
            f"  else {result}"
        )
    return result


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
    lean_root = Path(args.lean_root)
    lean_root.mkdir(parents=True, exist_ok=True)
    tag = f"S4{args.tag}"
    targets: list[str] = []

    def emit(module: str, body: str) -> None:
        write_if_changed(lean_root / f"{module}.lean", module_source(module, body))
        targets.append(f"{PREFIX}.{module}")

    meta_info = manifest["meta"]
    meta_file = str(meta_info["file"])
    meta_body = f"""private def source : String :=
  {source_literal(meta_file)}

def certificateSource : String := eval% S4JsonData.decodeFieldFrom source "source"
def atlas : Nat := eval% S4JsonData.decodeFieldFrom source "atlas"
def interval : Array String := eval% S4JsonData.decodeFieldFrom source "interval"
def factorDenominator : Nat :=
  eval% S4JsonData.decodeFieldFrom source "factor_denominator"
def orders : Array Nat := eval% S4JsonData.decodeFieldFrom source "orders"
def factorBounds : Array Nat := eval% S4JsonData.decodeFieldFrom source "factor_bounds"
def commonCorrectionDenominator : Nat :=
  eval% S4JsonData.decodeFieldFrom source "common_correction_denominator"
def commonCorrectionScaledBounds : Array Nat :=
  eval% S4JsonData.decodeFieldFrom source "common_correction_scaled_bounds"
def intermediateBounds : Array Nat :=
  eval% S4JsonData.decodeFieldFrom source "intermediate_bounds"
def gramBounds : Array Nat := eval% S4JsonData.decodeFieldFrom source "gram_bounds"
def groupKeys : Array (Array Nat) := eval% S4JsonData.decodeFieldFrom source "group_keys"
def targetCore : Nat := eval% S4JsonData.decodeFieldFrom source "target_core"

def shapeValid : Bool :=
  atlas == {int(manifest['atlas'])} && interval.size == 2 && orders.size == 10 &&
  factorBounds.size == 10 && commonCorrectionScaledBounds.size == 10 &&
  intermediateBounds.size == 10 && gramBounds.size == 10 &&
  groupKeys.size == 143 && groupKeys.all (fun key => key.size == 2)

theorem shape_valid : shapeValid = true := by decide +kernel
"""
    emit(f"{tag}FineMetaData", meta_body)

    meta_payload = json.loads((directory / meta_file).read_text(encoding="utf-8"))
    orders = list(map(int, meta_payload["orders"]))

    factor_rows: list[int] = []
    for descriptor in manifest["header_blocks"]:
        block = int(descriptor["block"])
        factor_file = str(descriptor["factor_file"])
        factor_payload = json.loads((directory / factor_file).read_text(encoding="utf-8"))
        rows = len(factor_payload["data"])
        factor_rows.append(rows)
        factor_module = f"{tag}FactorBlock{block:02d}Data"
        factor_body = decoded_def(factor_file, "Array (Array Int)") + f"""
def shapeValid : Bool :=
  data.size == {rows} && data.all (fun row => row.size == {orders[block]})
theorem shape_valid : shapeValid = true := by decide +kernel
"""
        emit(factor_module, factor_body)

        margin_file = str(descriptor["margin_file"])
        margin_module = f"{tag}DDMarginBlock{block:02d}Data"
        margin_body = decoded_def(margin_file, "Array Int") + """
def shapeValid : Bool := data.size == 2
theorem shape_valid : shapeValid = true := by decide +kernel
"""
        emit(margin_module, margin_body)

    for descriptor in manifest["common_chunks"]:
        field = str(descriptor["field"])
        block = int(descriptor["block"])
        start = int(descriptor["start"])
        stop = int(descriptor["stop"])
        count = stop - start
        filename = str(descriptor["file"])
        module = common_module_name(tag, descriptor)
        if field == "common_correction_scaled_upper":
            type_ = "Array (Array Int)"
            shape = (
                f"data.size == {count} && decide (∀ i : Fin {count}, "
                f"((data[i.1]?).getD #[]).size = {orders[block]} - ({start} + i.1))"
            )
        elif field == "intermediate_scaled":
            type_ = "Array (Array Int)"
            shape = (
                f"data.size == {count} && "
                f"data.all (fun row => row.size == {orders[block]})"
            )
        elif field == "common_gram_scaled_upper":
            type_ = "Array (Array Int)"
            shape = (
                f"data.size == {count} && decide (∀ i : Fin {count}, "
                f"((data[i.1]?).getD #[]).size = {factor_rows[block]} - ({start} + i.1))"
            )
        else:
            raise AssertionError(field)
        body = decoded_def(filename, type_) + f"""
def shapeValid : Bool := {shape}
theorem shape_valid : shapeValid = true := by decide +kernel
"""
        emit(module, body)

    for descriptor in manifest["group_chunks"]:
        start = int(descriptor["start"])
        stop = int(descriptor["stop"])
        count = stop - start
        filename = str(descriptor["file"])
        module = f"{tag}GroupRows{start:03d}_{stop - 1:03d}Data"
        body = decoded_def(filename, "Array (Array (Array (Array Int)))") + f"""
def totalComponent (table row slot component : Nat) : Int :=
  let tableData := (data[table]?).getD #[]
  let rowData := (tableData[row]?).getD #[]
  let slotData := (rowData[slot]?).getD #[]
  (slotData[component]?).getD 0

def commonTotalComponent (row slot component : Nat) : Int :=
  totalComponent 0 row slot component

def fullTotalComponent (row slot component : Nat) : Int :=
  totalComponent 1 row slot component

def shapeValid : Bool :=
  data.size == 2 && data.all (fun table =>
    table.size == {count} && table.all (fun row =>
      row.size == 4 && row.all (fun entry => entry.size == 2)))
theorem shape_valid : shapeValid = true := by decide +kernel
"""
        emit(module, body)

    for descriptor in manifest.get("exceptional_group_chunks", []):
        start = int(descriptor["start"])
        stop = int(descriptor["stop"])
        count = stop - start
        filename = str(descriptor["file"])
        module = exceptional_group_module_name(tag, descriptor)
        body = decoded_def(filename, "Array (Array Int)") + f"""
def component (row slot : Nat) : Int :=
  (((data[row]?).getD #[])[slot]?).getD 0

def shapeValid : Bool :=
  data.size == {count} && data.all (fun row => row.size == 4)
theorem shape_valid : shapeValid = true := by decide +kernel
"""
        emit(module, body)

    for descriptor in manifest.get("coefficient_chunks", []):
        index = int(descriptor["index"])
        filename = str(descriptor["file"])
        module = f"{tag}CoefficientEquation{index:03d}Data"
        body = f"""private def source : String :=
  {source_literal(filename)}

def corePower : Array Nat :=
  eval% S4JsonData.decodeFieldFrom source "core_power"
def expected : Array Int :=
  eval% S4JsonData.decodeFieldFrom source "expected"
def terms : Array (Array Int) :=
  eval% S4JsonData.decodeFieldFrom source "terms"

def shapeValid : Bool :=
  corePower.size == 2 && expected.size == 2 &&
  terms.all (fun term => term.size == 4)
theorem shape_valid : shapeValid = true := by decide +kernel
"""
        emit(module, body)

    common_fields = (
        "common_correction_scaled_upper", "intermediate_scaled",
        "common_gram_scaled_upper",
    )
    for block in range(10):
        block_common = [
            descriptor for descriptor in manifest["common_chunks"]
            if int(descriptor["block"]) == block
        ]
        by_field = {
            field: [
                descriptor for descriptor in block_common
                if str(descriptor["field"]) == field
            ]
            for field in common_fields
        }
        factor_module = f"{tag}FactorBlock{block:02d}Data"
        margin_module = f"{tag}DDMarginBlock{block:02d}Data"
        imports = [
            f"{PREFIX}.{tag}FineMetaData",
            f"{PREFIX}.{factor_module}",
            f"{PREFIX}.{margin_module}",
        ]
        imports.extend(
            f"{PREFIX}.{common_module_name(tag, descriptor)}"
            for descriptor in block_common
        )
        order = orders[block]
        rows = factor_rows[block]
        correction_dispatch = dispatch_array_rows(
            by_field["common_correction_scaled_upper"], tag, "#[]"
        )
        intermediate_dispatch = dispatch_array_rows(
            by_field["intermediate_scaled"], tag, "#[]"
        )
        gram_dispatch = dispatch_array_rows(
            by_field["common_gram_scaled_upper"], tag, "#[]"
        )
        block_module = f"{tag}Block{block:02d}Data"
        import_lines = "\n".join(f"import {name}" for name in imports)
        block_body = f"""{import_lines}

/-! Cached, bounded-memory accessors for exact certificate block {block}. -/

namespace {PREFIX}.{block_module}

set_option maxRecDepth 100000

abbrev order : Nat := {order}
abbrev factorRows : Nat := {rows}

def factor (row col : Nat) : Int :=
  (({factor_module}.data[row]?).getD #[])[col]?.getD 0

abbrev ddMargin : Array Int := {margin_module}.data

def commonCorrectionUpperRow (row : Nat) : Array Int :=
  {correction_dispatch}

def commonCorrectionScaled (row col : Nat) : Int :=
  if row <= col then
    (commonCorrectionUpperRow row)[col - row]?.getD 0
  else
    (commonCorrectionUpperRow col)[row - col]?.getD 0

def intermediateRow (row : Nat) : Array Int :=
  {intermediate_dispatch}

def intermediateScaled (row col : Nat) : Int :=
  (intermediateRow row)[col]?.getD 0

def commonGramUpperRow (row : Nat) : Array Int :=
  {gram_dispatch}

def commonGramScaled (row col : Nat) : Int :=
  if row <= col then
    (commonGramUpperRow row)[col - row]?.getD 0
  else
    (commonGramUpperRow col)[row - col]?.getD 0

def metadataValid : Bool :=
  (({tag}FineMetaData.orders[{block}]?).getD 0 == order) &&
  (({tag}FineMetaData.factorBounds[{block}]?).getD 0 ==
    {int(meta_payload['factor_bounds'][block])}) &&
  (({tag}FineMetaData.commonCorrectionScaledBounds[{block}]?).getD 0 ==
    {int(meta_payload['common_correction_scaled_bounds'][block])}) &&
  (({tag}FineMetaData.intermediateBounds[{block}]?).getD 0 ==
    {int(meta_payload['intermediate_bounds'][block])}) &&
  (({tag}FineMetaData.gramBounds[{block}]?).getD 0 ==
    {int(meta_payload['gram_bounds'][block])})

theorem metadata_valid : metadataValid = true := by decide +kernel

end {PREFIX}.{block_module}
"""
        write_if_changed(lean_root / f"{block_module}.lean", block_body)
        targets.append(f"{PREFIX}.{block_module}")

    umbrella = f"{tag}FineData"
    imports = "\n".join(f"import {target}" for target in targets)
    write_if_changed(
        lean_root / f"{umbrella}.lean",
        imports
        + f"\n\n/-! Bounded-memory data umbrella for {args.tag}. -/\n",
    )

    target_list = Path(args.target_list) if args.target_list else (
        directory / f"{manifest_path.stem}_lean_targets.txt"
    )
    write_if_changed(target_list, "\n".join(targets) + "\n")
    print(
        f"wrote {len(targets)} leaf modules, umbrella={PREFIX}.{umbrella}, "
        f"targets={target_list}"
    )


if __name__ == "__main__":
    main()
