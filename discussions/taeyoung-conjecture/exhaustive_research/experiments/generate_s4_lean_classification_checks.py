"""Generate bounded Lean checks for the common S4 graph classification."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


PREFIX = "Taeyoung.Methods.RootedSOS"


def write_if_changed(path: Path, contents: str) -> None:
    if path.exists() and path.read_text(encoding="utf-8") == contents:
        return
    path.write_text(contents, encoding="utf-8")


def source_literal(filename: str) -> str:
    return 'include_str ".."/".."/".."/".."/"experiments"/' + f'"{filename}"'


def group_data_module(start: int, stop: int) -> str:
    return f"S4ClassificationGroups{start:03d}_{stop - 1:03d}Data"


def lookup_data_module(start: int, stop: int) -> str:
    return f"S4ClassificationLookups{start:03d}_{stop - 1:03d}Data"


def group_lookup_data_module(start: int, stop: int) -> str:
    return f"S4ClassificationLookupGroups{start:03d}_{stop - 1:03d}Data"


def decoded_group_lookup_data_module(start: int, stop: int) -> str:
    return f"S4ClassificationLookupGroupArrays{start:03d}_{stop - 1:03d}Data"


def lookup_base_module(start: int, stop: int) -> str:
    return f"S4ClassificationLookupChunk{start:03d}_{stop - 1:03d}Base"


def lookup_rows_module(start: int, stop: int) -> str:
    return f"S4ClassificationLookupRows{start:03d}_{stop - 1:03d}"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest")
    parser.add_argument("--lean-root", default="lean/Taeyoung/Methods/RootedSOS")
    args = parser.parse_args()

    manifest_path = Path(args.manifest)
    directory = manifest_path.parent
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    lean_root = Path(args.lean_root)
    lean_root.mkdir(parents=True, exist_ok=True)
    group_count = int(manifest["group_count"])
    basis_size = int(manifest["basis_size"])
    pair_group_base = int(manifest["pair_group_base"])
    permutation_base = int(manifest["pair_permutation_base"])
    cell_base = int(manifest["pair_cell_base"])
    if (group_count, basis_size, pair_group_base, permutation_base) != (143, 352, 143, 6):
        raise AssertionError((group_count, basis_size, pair_group_base, permutation_base))
    label_unions = list(map(int, manifest["label_unions"]))
    union_index = list(map(int, manifest["union_index"]))
    if len(label_unions) != 57 or len(union_index) != 64:
        raise AssertionError((len(label_unions), len(union_index)))

    targets: list[str] = []
    group_modules: list[str] = []
    for descriptor in manifest["group_chunks"]:
        start = int(descriptor["start"])
        stop = int(descriptor["stop"])
        filename = str(descriptor["file"])
        module = group_data_module(start, stop)
        source = f"""import {PREFIX}.S4JsonData

namespace {PREFIX}.{module}

set_option maxRecDepth 1000000

private def source : String :=
  {source_literal(filename)}

def keys : Array (Array Nat) :=
  eval% S4JsonData.decodeFieldFrom source "keys"
def core6 : Array (Array (Array Bool)) :=
  eval% S4JsonData.decodeFieldFrom source "core6"
def core4 : Array (Array (Array Bool)) :=
  eval% S4JsonData.decodeFieldFrom source "core4"
def core2 : Array (Array (Array Bool)) :=
  eval% S4JsonData.decodeFieldFrom source "core2"
def standard : Array (Array (Array Bool)) :=
  eval% S4JsonData.decodeFieldFrom source "standard"

private def matrixShape (rows cols : Nat) (matrix : Array (Array Bool)) : Bool :=
  matrix.size == rows && matrix.all (fun row => row.size == cols)

def shapeValid : Bool :=
  keys.size == {stop - start} && keys.all (fun key => key.size == 2) &&
  core6.size == {stop - start} && core6.all (matrixShape 6 6) &&
  core4.size == {stop - start} && core4.all (matrixShape 4 4) &&
  core2.size == {stop - start} && core2.all (matrixShape 2 2) &&
  standard.size == {stop - start} && standard.all (matrixShape 6 6)

theorem shape_valid : shapeValid = true := by decide +kernel

end {PREFIX}.{module}
"""
        write_if_changed(lean_root / f"{module}.lean", source)
        targets.append(f"{PREFIX}.{module}")
        group_modules.append(module)

    lookup_modules: list[str] = []
    for descriptor in manifest["lookup_chunks"]:
        start = int(descriptor["start"])
        stop = int(descriptor["stop"])
        filename = str(descriptor["file"])
        module = lookup_data_module(start, stop)
        source = f"""import {PREFIX}.S4JsonData

namespace {PREFIX}.{module}

set_option maxRecDepth 1000000

private def source : String :=
  {source_literal(filename)}

def data : Array Int :=
  eval% S4JsonData.decodeFieldFrom source "data"

def shapeValid : Bool := data.size == {stop - start}

theorem shape_valid : shapeValid = true := by decide +kernel

end {PREFIX}.{module}
"""
        write_if_changed(lean_root / f"{module}.lean", source)
        targets.append(f"{PREFIX}.{module}")
        lookup_modules.append(module)

    group_lookup_modules: list[tuple[int, int, str]] = []
    for descriptor in manifest["group_lookup_chunks"]:
        start = int(descriptor["start"])
        stop = int(descriptor["stop"])
        filename = str(descriptor["file"])
        module = group_lookup_data_module(start, stop)
        source = f"""import {PREFIX}.S4JsonData

namespace {PREFIX}.{module}

set_option maxRecDepth 1000000

private def source : String :=
  {source_literal(filename)}

def data : Array Int :=
  eval% S4JsonData.decodeFieldFrom source "data"

def shapeValid : Bool := data.size == {stop - start}

theorem shape_valid : shapeValid = true := by decide +kernel

end {PREFIX}.{module}
"""
        write_if_changed(lean_root / f"{module}.lean", source)
        targets.append(f"{PREFIX}.{module}")
        group_lookup_modules.append((start, stop, module))

    decoded_group_lookup_modules: list[tuple[int, int, str]] = []
    for descriptor in manifest["decoded_group_lookup_chunks"]:
        start = int(descriptor["start"])
        stop = int(descriptor["stop"])
        filename = str(descriptor["file"])
        module = decoded_group_lookup_data_module(start, stop)
        source = f"""import {PREFIX}.S4JsonData

namespace {PREFIX}.{module}

set_option maxRecDepth 1000000

private def source : String :=
  {source_literal(filename)}

def data : Array (Array (Array Nat)) :=
  eval% S4JsonData.decodeFieldFrom source "data"

def shapeValid : Bool :=
  data.size == {stop - start} && data.all (fun leftRows =>
    leftRows.size == 16 && leftRows.all (fun row =>
      row.size == 16 && row.all (fun group => group < 143)))

theorem shape_valid : shapeValid = true := by decide +kernel

end {PREFIX}.{module}
"""
        write_if_changed(lean_root / f"{module}.lean", source)
        targets.append(f"{PREFIX}.{module}")
        decoded_group_lookup_modules.append((start, stop, module))

    def group_dispatch(field: str, fallback: str) -> str:
        result = fallback
        for descriptor in reversed(manifest["group_chunks"]):
            start = int(descriptor["start"])
            stop = int(descriptor["stop"])
            module = group_data_module(start, stop)
            result = (
                f"if row < {stop} then\n"
                f"    ({module}.{field}[row - {start}]?).getD {fallback}\n"
                f"  else {result}"
            )
        return result

    group_imports = "\n".join(f"import {PREFIX}.{module}" for module in group_modules)
    group_base_module = "S4ClassificationGroupBase"
    group_source = f"""import {PREFIX}.S4YoungData
import {PREFIX}.S4Flags
import {PREFIX}.GraphCanonical
import Taeyoung.Foundation.DisjointUnion
{group_imports}

/-! Executable standard representatives for the 143 S4 graph groups. -/

namespace {PREFIX}.S4Classification

open Taeyoung Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def keyRaw (row : Nat) : Array Nat :=
  {group_dispatch("keys", "#[]")}

private def core6Raw (row : Nat) : Array (Array Bool) :=
  {group_dispatch("core6", "#[]")}

private def core4Raw (row : Nat) : Array (Array Bool) :=
  {group_dispatch("core4", "#[]")}

private def core2Raw (row : Nat) : Array (Array Bool) :=
  {group_dispatch("core2", "#[]")}

private def standardRaw (row : Nat) : Array (Array Bool) :=
  {group_dispatch("standard", "#[]")}

private def codeFromArray {{n : Nat}} (data : Array (Array Bool)) : AdjacencyCode n :=
  data.toList.map Array.toList

def groupKey (row : Fin {group_count}) : Nat × Nat :=
  ((keyRaw row.1)[0]?.getD 0, (keyRaw row.1)[1]?.getD 0)

def coreCode6 (row : Fin {group_count}) : AdjacencyCode 6 :=
  codeFromArray (core6Raw row.1)
def coreCode4 (row : Fin {group_count}) : AdjacencyCode 4 :=
  codeFromArray (core4Raw row.1)
def coreCode2 (row : Fin {group_count}) : AdjacencyCode 2 :=
  codeFromArray (core2Raw row.1)
def standardCode (row : Fin {group_count}) : AdjacencyCode 6 :=
  codeFromArray (standardRaw row.1)

def coreGraph6 (row : Fin {group_count}) : SimpleGraph (Fin 6) :=
  graphOfCode (coreCode6 row)
def coreGraph4 (row : Fin {group_count}) : SimpleGraph (Fin 4) :=
  graphOfCode (coreCode4 row)
def coreGraph2 (row : Fin {group_count}) : SimpleGraph (Fin 2) :=
  graphOfCode (coreCode2 row)

instance (row : Fin {group_count}) : DecidableRel (coreGraph6 row).Adj := by
  unfold coreGraph6
  infer_instance
instance (row : Fin {group_count}) : DecidableRel (coreGraph4 row).Adj := by
  unfold coreGraph4
  infer_instance
instance (row : Fin {group_count}) : DecidableRel (coreGraph2 row).Adj := by
  unfold coreGraph2
  infer_instance

def standardGraph (row : Fin {group_count}) : SimpleGraph (Fin 6) :=
  match (groupKey row).2 with
  | 0 => coreGraph6 row
  | 1 => disjointUnion (coreGraph4 row) (⊤ : SimpleGraph (Fin 2))
  | 2 => disjointUnion
      (disjointUnion (coreGraph2 row) (⊤ : SimpleGraph (Fin 2)))
      (⊤ : SimpleGraph (Fin 2))
  | _ => disjointUnion
      (disjointUnion (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 2)))
      (⊤ : SimpleGraph (Fin 2))

instance (row : Fin {group_count}) : DecidableRel (standardGraph row).Adj := by
  unfold standardGraph
  split <;> infer_instance

private def singletonIf {{α : Type*}} [DecidableEq α]
    (condition : Bool) (value : α) : Finset α :=
  if condition then {{value}} else ∅

def labelEdgesFromMask (mask : Nat) : Finset (Sym2 (Fin 4)) :=
  singletonIf (mask.testBit 0) s(0, 1) ∪
    singletonIf (mask.testBit 1) s(0, 2) ∪
    singletonIf (mask.testBit 2) s(0, 3) ∪
    singletonIf (mask.testBit 3) s(1, 2) ∪
    singletonIf (mask.testBit 4) s(1, 3) ∪
    singletonIf (mask.testBit 5) s(2, 3)

def neighborsFromMask (mask : Nat) : Finset (Fin 4) :=
  singletonIf (mask.testBit 0) 0 ∪
    singletonIf (mask.testBit 1) 1 ∪
    singletonIf (mask.testBit 2) 2 ∪
    singletonIf (mask.testBit 3) 3

def labelGraphFromMask (mask : Nat) : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet ↑(labelEdgesFromMask mask)

instance (mask : Nat) : DecidableRel (labelGraphFromMask mask).Adj := by
  unfold labelGraphFromMask
  infer_instance

def lookupGraph (labelUnion leftBranch rightBranch : Nat) :
    SimpleGraph (Fin 6) :=
  gluedRootedFlagGraph (S4Flags.labelGraphFromMask labelUnion)
    (⊥ : SimpleGraph (Fin 4))
    (S4Flags.branchNeighborsFromMask leftBranch)
    (S4Flags.branchNeighborsFromMask rightBranch)

instance (labelUnion leftBranch rightBranch : Nat) :
    DecidableRel (lookupGraph labelUnion leftBranch rightBranch).Adj := by
  unfold lookupGraph
  infer_instance

def groupDataValid (row : Fin {group_count}) : Bool :=
  groupKey row == S4YoungData.rawGroupKey row &&
  decide ((groupKey row).2 ≤ 3) &&
  decide (adjacencyCode (standardGraph row) = standardCode row) &&
  match (groupKey row).2 with
  | 0 => true
  | 1 => decide (adjacencyCode (coreGraph6 row) =
      adjacencyCode ((coreGraph4 row).map (Fin.castAdd 2)))
  | 2 => decide (adjacencyCode (coreGraph6 row) =
      adjacencyCode ((coreGraph2 row).map (Fin.castAdd 4)))
  | 3 => decide (adjacencyCode (coreGraph6 row) =
      adjacencyCode (⊥ : SimpleGraph (Fin 6)))
  | _ => false

end {PREFIX}.S4Classification
"""
    write_if_changed(lean_root / f"{group_base_module}.lean", group_source)
    targets.append(f"{PREFIX}.{group_base_module}")

    group_check_modules: list[tuple[int, int, str]] = []
    for descriptor in manifest["group_chunks"]:
        start = int(descriptor["start"])
        stop = int(descriptor["stop"])
        module = f"S4ClassificationGroupChecks{start:03d}_{stop - 1:03d}"
        source = f"""import {PREFIX}.{group_base_module}

namespace {PREFIX}.S4Classification

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem group_data_valid_{start:03d}_{stop - 1:03d} :
    ∀ index : Fin {stop - start},
      groupDataValid ⟨{start} + index.1, by omega⟩ = true := by
  decide +kernel

end {PREFIX}.S4Classification
"""
        write_if_changed(lean_root / f"{module}.lean", source)
        targets.append(f"{PREFIX}.{module}")
        group_check_modules.append((start, stop, module))

    group_checks = "S4ClassificationGroupChecks"
    group_check_imports = "\n".join(
        f"import {PREFIX}.{module}" for _, _, module in group_check_modules
    )
    group_cases: list[str] = []
    for start, stop, _ in group_check_modules:
        theorem = f"group_data_valid_{start:03d}_{stop - 1:03d}"
        group_cases.append(f"""  by_cases h : row.1 < {stop}
  · let index : Fin {stop - start} := ⟨row.1 - {start}, by omega⟩
    let row' : Fin {group_count} := ⟨{start} + index.1, by omega⟩
    have hrow : row' = row := by
      apply Fin.ext
      dsimp [row', index]
      omega
    rw [← hrow]
    exact {theorem} index
""")
    group_source = f"""{group_check_imports}

namespace {PREFIX}.S4Classification

theorem all_group_data_valid : ∀ row : Fin {group_count}, groupDataValid row = true := by
  intro row
{"".join(group_cases)}  omega

end {PREFIX}.S4Classification
"""
    write_if_changed(lean_root / f"{group_checks}.lean", group_source)
    targets.append(f"{PREFIX}.{group_checks}")

    label_unions_literal = "#[" + ", ".join(map(str, label_unions)) + "]"
    lookup_chunk_aggregates: list[tuple[int, int, str]] = []
    for descriptor in manifest["lookup_chunks"]:
        start = int(descriptor["start"])
        stop = int(descriptor["stop"])
        data_module = lookup_data_module(start, stop)
        base_module = lookup_base_module(start, stop)
        base_source = f"""import {PREFIX}.{group_checks}
import {PREFIX}.{data_module}

namespace {PREFIX}.S4Classification.LookupChunk{start:03d}_{stop - 1:03d}

open {PREFIX}
open {PREFIX}.S4Classification

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

abbrev start : Nat := {start}
abbrev stop : Nat := {stop}
abbrev cellBase : Nat := {cell_base}
abbrev groupBase : Nat := {pair_group_base}
abbrev permutationBase : Nat := {permutation_base}

def encodedRow (index : Fin {stop - start}) : Nat :=
  ({data_module}.data[index.1]?).getD 0 |>.natAbs

def labelUnions : Array Nat := {label_unions_literal}

def labelUnion (index : Fin {stop - start}) : Nat :=
  (labelUnions[{start} + index.1]?).getD 0

def lookupCell (index : Fin {stop - start}) (left right : Fin 16) : Nat :=
  encodedRow index / cellBase ^ (16 * left.1 + right.1) % cellBase

def witnessGroup (index : Fin {stop - start}) (left right : Fin 16) :
    Fin {group_count} :=
  ⟨lookupCell index left right % groupBase, Nat.mod_lt _ (by decide)⟩

def witnessPermutation (index : Fin {stop - start}) (left right : Fin 16) :
    List (Fin 6) :=
  List.ofFn fun coordinate : Fin 6 ↦
    ⟨(lookupCell index left right / groupBase /
      permutationBase ^ coordinate.1) % permutationBase,
      Nat.mod_lt _ (by decide)⟩

def lookupWitnessValid (index : Fin {stop - start})
    (left right : Fin 16) : Bool :=
  let row := witnessGroup index left right
  let permutation := witnessPermutation index left right
  decide permutation.Nodup &&
    decide (relabelCodeByListFin
      (lookupGraph (labelUnion index) left.1 right.1) permutation = standardCode row)

end {PREFIX}.S4Classification.LookupChunk{start:03d}_{stop - 1:03d}
"""
        write_if_changed(lean_root / f"{base_module}.lean", base_source)
        targets.append(f"{PREFIX}.{base_module}")

        row_modules: list[str] = []
        theorem_names: list[str] = []
        namespace = f"S4Classification.LookupChunk{start:03d}_{stop - 1:03d}"
        for global_row in range(start, stop):
            local_row = global_row - start
            module = f"S4ClassificationLookupRow{global_row:03d}"
            theorem = f"lookup_witness_row_{global_row:03d}"
            source = f"""import {PREFIX}.{base_module}

namespace {PREFIX}.{namespace}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem {theorem} : ∀ left right : Fin 16,
    lookupWitnessValid {local_row} left right = true := by
  decide +kernel

end {PREFIX}.{namespace}
"""
            write_if_changed(lean_root / f"{module}.lean", source)
            targets.append(f"{PREFIX}.{module}")
            row_modules.append(module)
            theorem_names.append(theorem)

        theorem_cases = "\n".join(
            f"  | {index} => by\n"
            f"      have hi : index = ({index} : Fin {stop - start}) := by\n"
            f"        apply Fin.ext\n"
            f"        exact hindex\n"
            f"      simpa [hi] using {theorem} left right"
            for index, theorem in enumerate(theorem_names)
        )
        impossible_pattern = "Nat.succ (" * (stop - start) + "k" + ")" * (stop - start)
        aggregate_module = lookup_rows_module(start, stop)
        imports = "\n".join(f"import {PREFIX}.{module}" for module in row_modules)
        aggregate_source = f"""{imports}

namespace {PREFIX}.{namespace}

theorem all_lookup_witnesses_valid :
    ∀ index : Fin {stop - start}, ∀ left right : Fin 16,
      lookupWitnessValid index left right = true := by
  intro index left right
  exact match hindex : index.1 with
{theorem_cases}
  | {impossible_pattern} => by
      have hlt := index.isLt
      omega

end {PREFIX}.{namespace}
"""
        write_if_changed(lean_root / f"{aggregate_module}.lean", aggregate_source)
        targets.append(f"{PREFIX}.{aggregate_module}")
        lookup_chunk_aggregates.append((start, stop, aggregate_module))

    fast_group_base = "S4ClassificationFastGroupBase"
    fast_group_imports = "\n".join(
        f"import {PREFIX}.{module}" for _, _, module in group_lookup_modules
    )
    fast_dispatch = "0"
    for start, stop, module in reversed(group_lookup_modules):
        fast_dispatch = (
            f"if index.1 < {stop} then\n"
            f"    (({module}.data[index.1 - {start}]?).getD 0).natAbs\n"
            f"  else {fast_dispatch}"
        )
    fast_group_source = f"""import {PREFIX}.S4ClassificationLookupBase
{fast_group_imports}

namespace {PREFIX}.S4Classification

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

def fastGroupEncodedRow (index : Fin 57) : Nat :=
  {fast_dispatch}

def fastWitnessGroup (index : Fin 57) (left right : Fin 16) : Fin 143 :=
  ⟨fastGroupEncodedRow index / 143 ^ (16 * left.1 + right.1) % 143,
    Nat.mod_lt _ (by decide)⟩

def fastGroupValid (index : Fin 57) (left right : Fin 16) : Bool :=
  fastWitnessGroup index left right == witnessGroup index left right

end {PREFIX}.S4Classification
"""
    write_if_changed(lean_root / f"{fast_group_base}.lean", fast_group_source)
    targets.append(f"{PREFIX}.{fast_group_base}")

    fast_row_modules: list[str] = []
    fast_theorem_names: list[str] = []
    for row in range(57):
        module = f"S4ClassificationFastGroupRow{row:03d}"
        theorem = f"fast_group_row_{row:03d}"
        source = f"""import {PREFIX}.{fast_group_base}

namespace {PREFIX}.S4Classification

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem {theorem} : ∀ left right : Fin 16,
    fastGroupValid {row} left right = true := by
  decide +kernel

end {PREFIX}.S4Classification
"""
        write_if_changed(lean_root / f"{module}.lean", source)
        targets.append(f"{PREFIX}.{module}")
        fast_row_modules.append(module)
        fast_theorem_names.append(theorem)

    fast_theorem_cases = "\n".join(
        f"  | {index} => by\n"
        f"      have hi : index = ({index} : Fin 57) := by\n"
        f"        apply Fin.ext\n"
        f"        exact hindex\n"
        f"      simpa [hi] using {theorem} left right"
        for index, theorem in enumerate(fast_theorem_names)
    )
    fast_impossible_pattern = "Nat.succ (" * 57 + "k" + ")" * 57
    fast_group_checks = "S4ClassificationFastGroupChecks"
    fast_row_imports = "\n".join(
        f"import {PREFIX}.{module}" for module in fast_row_modules
    )
    fast_checks_source = f"""{fast_row_imports}

namespace {PREFIX}.S4Classification

theorem all_fast_groups_valid :
    ∀ index : Fin 57, ∀ left right : Fin 16,
      fastGroupValid index left right = true := by
  intro index left right
  exact match hindex : index.1 with
{fast_theorem_cases}
  | {fast_impossible_pattern} => by
      have hlt := index.isLt
      omega

end {PREFIX}.S4Classification
"""
    write_if_changed(lean_root / f"{fast_group_checks}.lean", fast_checks_source)
    targets.append(f"{PREFIX}.{fast_group_checks}")

    decoded_group_base = "S4ClassificationDecodedGroupBase"
    decoded_imports = "\n".join(
        f"import {PREFIX}.{module}"
        for _, _, module in decoded_group_lookup_modules
    )
    decoded_dispatch = "#[]"
    for start, stop, module in reversed(decoded_group_lookup_modules):
        decoded_dispatch = (
            f"if index.1 < {stop} then\n"
            f"    ({module}.data[index.1 - {start}]?).getD #[]\n"
            f"  else {decoded_dispatch}"
        )
    decoded_base_source = f"""import {PREFIX}.{fast_group_base}
{decoded_imports}

namespace {PREFIX}.S4Classification

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

def decodedGroupRow (index : Fin 57) : Array (Array Nat) :=
  {decoded_dispatch}

def decodedWitnessGroup (index : Fin 57) (left right : Fin 16) : Fin 143 :=
  ⟨((((decodedGroupRow index)[left.1]?).getD #[])[right.1]?).getD 0 % 143,
    Nat.mod_lt _ (by decide)⟩

def decodedGroupValid (index : Fin 57) (left right : Fin 16) : Bool :=
  decodedWitnessGroup index left right == fastWitnessGroup index left right

end {PREFIX}.S4Classification
"""
    write_if_changed(lean_root / f"{decoded_group_base}.lean", decoded_base_source)
    targets.append(f"{PREFIX}.{decoded_group_base}")

    decoded_row_modules: list[str] = []
    decoded_theorems: list[str] = []
    for row in range(57):
        module = f"S4ClassificationDecodedGroupRow{row:03d}"
        theorem = f"decoded_group_row_{row:03d}"
        source = f"""import {PREFIX}.{decoded_group_base}

namespace {PREFIX}.S4Classification

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem {theorem} : ∀ left right : Fin 16,
    decodedGroupValid {row} left right = true := by
  decide +kernel

end {PREFIX}.S4Classification
"""
        write_if_changed(lean_root / f"{module}.lean", source)
        targets.append(f"{PREFIX}.{module}")
        decoded_row_modules.append(module)
        decoded_theorems.append(theorem)

    decoded_cases = "\n".join(
        f"  | {index} => by\n"
        f"      have hi : index = ({index} : Fin 57) := by\n"
        f"        apply Fin.ext\n"
        f"        exact hindex\n"
        f"      simpa [hi] using {theorem} left right"
        for index, theorem in enumerate(decoded_theorems)
    )
    decoded_impossible = "Nat.succ (" * 57 + "k" + ")" * 57
    decoded_checks = "S4ClassificationDecodedGroupChecks"
    decoded_row_imports = "\n".join(
        f"import {PREFIX}.{module}" for module in decoded_row_modules
    )
    decoded_checks_source = f"""{decoded_row_imports}

namespace {PREFIX}.S4Classification

theorem all_decoded_groups_valid :
    ∀ index : Fin 57, ∀ left right : Fin 16,
      decodedGroupValid index left right = true := by
  intro index left right
  exact match hindex : index.1 with
{decoded_cases}
  | {decoded_impossible} => by
      have hlt := index.isLt
      omega

end {PREFIX}.S4Classification
"""
    write_if_changed(lean_root / f"{decoded_checks}.lean", decoded_checks_source)
    targets.append(f"{PREFIX}.{decoded_checks}")

    decoded_module = "S4ClassificationDecodedGroup"
    decoded_source = f"""import {PREFIX}.{decoded_checks}
import {PREFIX}.S4ClassificationFastGroup

namespace {PREFIX}.S4Classification

theorem decodedWitnessGroup_eq (index : Fin 57) (left right : Fin 16) :
    decodedWitnessGroup index left right = fastWitnessGroup index left right := by
  have h := all_decoded_groups_valid index left right
  simpa [decodedGroupValid] using h

def pairDecodedWitnessGroup (a b : Fin 352) : Fin 143 :=
  decodedWitnessGroup (pairUnionIndex a b)
    (pairLeftBranchFin a) (pairRightBranchFin b)

theorem pairDecodedWitnessGroup_eq (a b : Fin 352) :
    pairDecodedWitnessGroup a b = pairWitnessGroup a b := by
  rw [pairDecodedWitnessGroup, decodedWitnessGroup_eq]
  exact fastWitnessGroup_eq _ _ _

end {PREFIX}.S4Classification
"""
    write_if_changed(lean_root / f"{decoded_module}.lean", decoded_source)
    targets.append(f"{PREFIX}.{decoded_module}")

    umbrella = "S4ClassificationChecks"
    umbrella_imports = "\n".join(
        f"import {PREFIX}.{module}" for _, _, module in lookup_chunk_aggregates
    )
    umbrella_source = f"""import {PREFIX}.{group_checks}
{umbrella_imports}
import {PREFIX}.{fast_group_checks}

/-! Complete bounded S4 six-vertex classification audit. -/
"""
    write_if_changed(lean_root / f"{umbrella}.lean", umbrella_source)
    targets.append(f"{PREFIX}.{umbrella}")

    target_file = directory / f"{manifest_path.stem}_lean_targets.txt"
    write_if_changed(target_file, "\n".join(targets) + "\n")
    print(
        f"wrote {len(targets)} classification modules, "
        f"umbrella={PREFIX}.{umbrella}, targets={target_file}"
    )


if __name__ == "__main__":
    main()
