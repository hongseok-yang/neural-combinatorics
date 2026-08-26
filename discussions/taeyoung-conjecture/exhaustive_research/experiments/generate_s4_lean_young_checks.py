"""Generate memory-bounded Lean checks for the common S4 Young pullback.

Dense Young columns are divided into consecutive parts of at most six
nonzero entries. Lean verifies every part directly from the decoded flag-pair
classification, then independently verifies that the committed parts sum to
the full committed pullback. This keeps kernel reduction bounded without
weakening the certificate identity.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


PREFIX = "Taeyoung.Methods.RootedSOS"
BLOCKS = (("4", 32), ("31", 52), ("22", 34), ("211", 30), ("1111", 6))
def parts_for_support(tag: str, support: int) -> list[tuple[int, int]]:
    part_size = 6 if tag in {"4", "1111"} or support <= 6 else 4
    return [
        (start, min(start + part_size, support))
        for start in range(0, support, part_size)
    ]


def raw_group_chunks_for_block(tag: str) -> list[tuple[int, int]]:
    # The 52-, 34-, and 30-dimensional blocks retain too many TreeMap nodes
    # when all graph groups are normalized together.  Blocks 4 and 1111 have
    # been measured safe as one chunk; the wider blocks use three chunks.
    if tag in {"4", "1111"}:
        return [(0, 143)]
    return [(0, 48), (48, 96), (96, 143)]


def sum_group_chunks_for_column(tag: str, support: int) -> list[tuple[int, int]]:
    if tag in {"4", "1111"} or support <= 6:
        return [(0, 143)]
    return [(start, min(start + 24, 143)) for start in range(0, 143, 24)]


def write_if_changed(path: Path, contents: str) -> None:
    if path.exists() and path.read_text(encoding="utf-8") == contents:
        return
    path.write_text(contents, encoding="utf-8")


def source_literal(filename: str) -> str:
    return (
        'include_str ".."/".."/".."/".."/"experiments"/'
        f'"{filename}"'
    )


def module_source(imports: list[str], namespace: str, body: str) -> str:
    import_lines = "\n".join(f"import {name}" for name in imports)
    return f"""{import_lines}

namespace {PREFIX}.{namespace}

{body}

end {PREFIX}.{namespace}
"""


def conjunction(items: list[str], indent: str = "      ") -> str:
    if not items:
        return "True"
    return (" ∧\n" + indent).join(items)


def witnesses(items: list[str]) -> str:
    if not items:
        return "trivial"
    return f"exact ⟨{', '.join(items)}⟩"


def dispatch_cases(theorem_prefix: str, dim: int, theorem_args: str = "") -> str:
    cases = []
    for index in range(dim):
        cases.append(
            f"""  | {index} => by
      have hi : i = ({index} : Fin {dim}) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using {theorem_prefix}_{index:03d}{theorem_args}"""
        )
    impossible = "Nat.succ (" * dim + "k" + ")" * dim
    cases.append(
        f"""  | {impossible} => by
      have hlt := i.isLt
      omega"""
    )
    return "\n".join(cases)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean-root", default="lean/Taeyoung/Methods/RootedSOS")
    parser.add_argument("--target-list", default="experiments/s4_lean_young_targets.txt")
    args = parser.parse_args()

    lean_root = Path(args.lean_root)
    lean_root.mkdir(parents=True, exist_ok=True)
    targets: list[str] = []
    emitted_paths: set[Path] = set()
    sparse_supports = {
        tag: [
            len(column)
            for column in json.loads(
                Path(f"experiments/s4_lean_common_young_sparse_{tag}.json")
                .read_text(encoding="utf-8")
            )["columns"]
        ]
        for tag, _ in BLOCKS
    }

    def emit(module: str, imports: list[str], namespace: str, body: str) -> None:
        path = lean_root / f"{module}.lean"
        write_if_changed(
            path,
            module_source(imports, namespace, body),
        )
        emitted_paths.add(path.resolve())
        targets.append(f"{PREFIX}.{module}")

    # Check that every sparse column is exactly the corresponding dense
    # integer Young column committed in the original certificates.
    for tag, dim in BLOCKS:
        module = f"S4YoungSparse{tag}Data"
        body = f"""set_option maxRecDepth 1000000

private def source : String :=
  {source_literal(f"s4_lean_common_young_sparse_{tag}.json")}

def columns : Array (Array (Array Int)) :=
  eval% S4JsonData.decodeFieldFrom source "columns"

def column (index : Nat) : Array (Array Int) :=
  (columns[index]?).getD #[]

def shapeValid : Bool :=
  columns.size == {dim} && columns.all (fun entries =>
    entries.all (fun entry =>
      entry.size == 2 && (entry[0]?.getD 352).natAbs < 352))

theorem shape_valid : shapeValid = true := by
  decide +kernel"""
        emit(module, [f"{PREFIX}.S4JsonData"], module, body)

        exact_module = f"S4YoungSparse{tag}ExactBase"
        body = f"""set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

def sparseIndex (entry : Array Int) : Fin 352 :=
  ⟨(entry[0]?.getD 0).natAbs % 352, Nat.mod_lt _ (by decide)⟩
def sparseValue (entry : Array Int) : Int :=
  entry[1]?.getD 0

def sparseCoeff (a : Fin 352) (i : Fin {dim}) : Int :=
  (S4YoungSparse{tag}Data.column i.1).foldl (fun total entry =>
    if sparseIndex entry = a then total + sparseValue entry else total) 0"""
        emit(
            exact_module,
            [f"{PREFIX}.S4Young{tag}Data", f"{PREFIX}.S4YoungSparse{tag}Data"],
            exact_module,
            body,
        )

        exact_columns: list[str] = []
        theorem_prefix = f"sparse_exact_{tag}"
        for index in range(dim):
            column_module = f"S4YoungSparse{tag}ExactColumn{index:03d}"
            exact_columns.append(column_module)
            body = f"""set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem {theorem_prefix}_{index:03d} (a : Fin 352) :
    S4YoungSparse{tag}ExactBase.sparseCoeff a {index} =
      S4Young{tag}Data.entry a {index} := by
  decide +kernel +revert"""
            emit(
                column_module,
                [f"{PREFIX}.{exact_module}"],
                "S4YoungPullback",
                body,
            )

        checks = f"S4YoungSparse{tag}ExactChecks"
        body = f"""theorem sparse_exact_{tag} (a : Fin 352) (i : Fin {dim}) :
    S4YoungSparse{tag}ExactBase.sparseCoeff a i =
      S4Young{tag}Data.entry a i := by
  exact match hindex : i.1 with
{dispatch_cases(theorem_prefix, dim, " a")}"""
        emit(
            checks,
            [f"{PREFIX}.{module}" for module in exact_columns],
            "S4YoungPullback",
            body,
        )

    sparse_dispatch = "\n".join(
        f"  | {index} => S4YoungSparse{tag}Data.column i"
        for index, (tag, _) in enumerate(BLOCKS)
    )
    dim_dispatch = "\n".join(
        f"  | {index} => {dim}" for index, (_, dim) in enumerate(BLOCKS)
    )
    base_imports = [
        "Std.Data.TreeMap",
        f"{PREFIX}.S4ClassificationDecodedGroup",
        f"{PREFIX}.S4YoungData",
    ]
    base_imports.extend(f"{PREFIX}.S4YoungSparse{tag}Data" for tag, _ in BLOCKS)
    base_body = f"""set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

def youngDim (block : Fin 5) : Nat :=
  match block.1 with
{dim_dispatch}
  | _ => 0

def sparseColumn (block : Fin 5) (i : Nat) : Array (Array Int) :=
  match block.1 with
{sparse_dispatch}
  | _ => #[]

def sparseIndex (entry : Array Int) : Fin 352 :=
  ⟨(entry[0]?.getD 0).natAbs % 352, Nat.mod_lt _ (by decide)⟩
def sparseValue (entry : Array Int) : Int :=
  entry[1]?.getD 0

def groupFin (row : Nat) : Fin 143 :=
  ⟨row % 143, Nat.mod_lt _ (by decide)⟩

abbrev CoefficientMap := Std.TreeMap Nat Int

def addCoefficient (coefficients : CoefficientMap) (index : Nat) (value : Int) :
    CoefficientMap :=
  let next := (coefficients.get? index).getD 0 + value
  if next = 0 then coefficients.erase index else coefficients.insert index next

def rawPullPartChunkCoefficients
    (block : Fin 5) (i partStart partCount start count : Nat) : CoefficientMap :=
  (List.range (youngDim block)).foldl (fun coefficients j =>
    (List.range partCount).foldl (fun coefficients offset =>
      let left := ((sparseColumn block i)[partStart + offset]?).getD #[]
      (sparseColumn block j).foldl (fun coefficients right =>
        let group := (S4Classification.pairDecodedWitnessGroup
          (sparseIndex left) (sparseIndex right)).1
        if start ≤ group ∧ group < start + count then
          addCoefficient coefficients
            ((group - start) * youngDim block + j)
            (sparseValue left * sparseValue right)
        else coefficients) coefficients) coefficients)
    Std.TreeMap.empty

def pulledPartEntryGroup (entry : Array Int) : Nat :=
  (entry[0]?.getD 0).natAbs
def pulledPartEntryColumn (entry : Array Int) : Nat :=
  (entry[1]?.getD 0).natAbs
def pulledPartEntryValue (entry : Array Int) : Int :=
  entry[2]?.getD 0

def addStoredPartChunkCoefficients
    (coefficients : CoefficientMap) (entries : Array (Array Int))
    (block : Fin 5) (start count : Nat) : CoefficientMap :=
  entries.foldl (fun coefficients entry =>
    let group := pulledPartEntryGroup entry
    if start ≤ group ∧ group < start + count then
      addCoefficient coefficients
        ((group - start) * youngDim block + pulledPartEntryColumn entry)
        (pulledPartEntryValue entry)
    else coefficients) coefficients

def storedPartChunkCoefficients
    (entries : Array (Array Int)) (block : Fin 5) (start count : Nat) :
    CoefficientMap :=
  addStoredPartChunkCoefficients Std.TreeMap.empty entries block start count

def pullPartChunkValid
    (entries : Array (Array Int))
    (block : Fin 5) (i partStart partCount start count : Nat) : Bool :=
  rawPullPartChunkCoefficients block i partStart partCount start count ==
    storedPartChunkCoefficients entries block start count

def pulledEntryRow (entry : Array Int) : Nat :=
  (entry[0]?.getD 0).natAbs
def pulledEntryColumn (entry : Array Int) : Nat :=
  (entry[1]?.getD 0).natAbs
def pulledEntryValue (entry : Array Int) : Int :=
  entry[2]?.getD 0

def storedFullPullCoefficients
    (block : Fin 5) (i start count : Nat) : CoefficientMap :=
  (List.range count).foldl (fun coefficients offset =>
    let row := start + offset
    (S4YoungData.pulledGroupEntries (groupFin row) block).foldl
      (fun coefficients entry =>
        if pulledEntryRow entry = i then
          addCoefficient coefficients
            (offset * youngDim block + pulledEntryColumn entry)
            (pulledEntryValue entry)
        else coefficients) coefficients)
    Std.TreeMap.empty"""
    emit("S4YoungPullbackBase", base_imports, "S4YoungPullback", base_body)

    block_modules: list[str] = []
    for block, (tag, dim) in enumerate(BLOCKS):
        column_modules: list[str] = []
        column_props: list[str] = []
        column_theorems: list[str] = []
        for column_index, support in enumerate(sparse_supports[tag]):
            parts = parts_for_support(tag, support)
            raw_group_chunks = raw_group_chunks_for_block(tag)
            sum_group_chunks = sum_group_chunks_for_column(tag, support)
            part_data_modules: list[str] = []
            leaf_modules: list[str] = []
            leaf_props: list[str] = []
            leaf_theorems: list[str] = []
            for part_start, part_stop in parts:
                data_module = (
                    f"S4YoungPullPart{tag}Column{column_index:03d}"
                    f"Entries{part_start:02d}_{part_stop - 1:02d}Data"
                )
                part_data_modules.append(data_module)
                filename = (
                    f"s4_lean_common_young_pull_part_{tag}_column_"
                    f"{column_index:03d}_entries_{part_start:02d}_{part_stop - 1:02d}.json"
                )
                body = f"""set_option maxRecDepth 1000000

private def source : String :=
  {source_literal(filename)}

def entries : Array (Array Int) :=
  eval% S4JsonData.decodeFieldFrom source "entries"

def shapeValid : Bool :=
  entries.all (fun entry =>
    entry.size == 3 &&
    (entry[0]?.getD 143).natAbs < 143 &&
    (entry[1]?.getD {dim}).natAbs < {dim})

theorem shape_valid : shapeValid = true := by
  decide +kernel"""
                emit(data_module, [f"{PREFIX}.S4JsonData"], data_module, body)

                for group_start, group_stop in raw_group_chunks:
                    if len(raw_group_chunks) == 1:
                        module_suffix = ""
                        theorem_suffix = ""
                    else:
                        module_suffix = f"Groups{group_start:03d}_{group_stop - 1:03d}"
                        theorem_suffix = f"_{group_start:03d}_{group_stop - 1:03d}"
                    leaf_module = (
                        f"S4YoungPullback{tag}Column{column_index:03d}"
                        f"Entries{part_start:02d}_{part_stop - 1:02d}{module_suffix}"
                    )
                    leaf_modules.append(leaf_module)
                    prop = (
                        f"pullPartChunkValid {data_module}.entries {block} "
                        f"{column_index} {part_start} {part_stop - part_start} "
                        f"{group_start} {group_stop - group_start} = true"
                    )
                    theorem = (
                        f"pull_part_{tag}_{column_index:03d}_"
                        f"{part_start:02d}_{part_stop - 1:02d}"
                        f"{theorem_suffix}_valid"
                    )
                    leaf_props.append(prop)
                    leaf_theorems.append(theorem)
                    body = f"""set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem {theorem} :
    {prop} := by
  decide +kernel"""
                    emit(
                        leaf_module,
                        [f"{PREFIX}.S4YoungPullbackBase", f"{PREFIX}.{data_module}"],
                        "S4YoungPullback",
                        body,
                    )

            full_data_module = (
                f"S4YoungPullFull{tag}Column{column_index:03d}Data"
            )
            full_filename = (
                f"s4_lean_common_young_pull_full_{tag}_column_"
                f"{column_index:03d}.json"
            )
            body = f"""set_option maxRecDepth 1000000

private def source : String :=
  {source_literal(full_filename)}

def entries : Array (Array Int) :=
  eval% S4JsonData.decodeFieldFrom source "entries"

def shapeValid : Bool :=
  entries.all (fun entry =>
    entry.size == 3 &&
    (entry[0]?.getD 143).natAbs < 143 &&
    (entry[1]?.getD {dim}).natAbs < {dim})

theorem shape_valid : shapeValid = true := by
  decide +kernel"""
            emit(full_data_module, [f"{PREFIX}.S4JsonData"], full_data_module, body)

            sum_modules: list[str] = []
            sum_props: list[str] = []
            sum_theorems: list[str] = []
            for group_start, group_stop in sum_group_chunks:
                if len(sum_group_chunks) == 1:
                    module_suffix = ""
                    symbol_suffix = ""
                else:
                    module_suffix = f"Groups{group_start:03d}_{group_stop - 1:03d}"
                    symbol_suffix = f"_{group_start:03d}_{group_stop - 1:03d}"
                sum_module = (
                    f"S4YoungPullback{tag}Column{column_index:03d}Sum{module_suffix}"
                )
                sum_modules.append(sum_module)
                sum_prop = (
                    f"pullPartsSumValid_{tag}_{column_index:03d}{symbol_suffix} = true"
                )
                sum_theorem = (
                    f"pull_parts_sum_{tag}_{column_index:03d}{symbol_suffix}_valid"
                )
                sum_props.append(sum_prop)
                sum_theorems.append(sum_theorem)
                sum_steps = [
                    "  let coefficients0 : CoefficientMap := Std.TreeMap.empty"
                ]
                for part_index, data_module in enumerate(part_data_modules):
                    sum_steps.append(
                        f"  let coefficients{part_index + 1} := "
                        f"addStoredPartChunkCoefficients coefficients{part_index} "
                        f"{data_module}.entries {block} {group_start} "
                        f"{group_stop - group_start}"
                    )
                sum_steps.append(f"  exact coefficients{len(part_data_modules)}")
                sum_definition = "\n".join(sum_steps)
                if len(sum_group_chunks) == 1 and tag not in {"4", "1111"}:
                    full_call = (
                        f"storedPartChunkCoefficients {full_data_module}.entries "
                        f"{block} {group_start} {group_stop - group_start}"
                    )
                else:
                    full_call = (
                        f"storedPartChunkCoefficients {full_data_module}.entries {block}\n"
                        f"      {group_start} {group_stop - group_start}"
                    )
                body = f"""set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

def storedPartSumCoefficients_{tag}_{column_index:03d}{symbol_suffix} : CoefficientMap := by
{sum_definition}

def pullPartsSumValid_{tag}_{column_index:03d}{symbol_suffix} : Bool :=
  storedPartSumCoefficients_{tag}_{column_index:03d}{symbol_suffix} ==
    {full_call}

theorem {sum_theorem} : {sum_prop} := by
  decide +kernel"""
                emit(
                    sum_module,
                    [f"{PREFIX}.S4YoungPullbackBase"]
                    + [f"{PREFIX}.{module}" for module in part_data_modules]
                    + [f"{PREFIX}.{full_data_module}"],
                    "S4YoungPullback",
                    body,
                )

            column_module = f"S4YoungPullback{tag}Column{column_index:03d}Checks"
            column_modules.append(column_module)
            column_prop = f"pullColumn{tag}_{column_index:03d}Valid"
            column_theorem = f"pull_column_{tag}_{column_index:03d}_verified"
            column_props.append(column_prop)
            column_theorems.append(column_theorem)
            all_props = leaf_props + sum_props
            all_theorems = leaf_theorems + sum_theorems
            body = f"""def {column_prop} : Prop :=
    {conjunction(all_props)}

theorem {column_theorem} : {column_prop} := by
  {witnesses(all_theorems)}"""
            emit(
                column_module,
                [f"{PREFIX}.{module}" for module in leaf_modules]
                + [f"{PREFIX}.{module}" for module in sum_modules],
                "S4YoungPullback",
                body,
            )

        block_module = f"S4YoungPullback{tag}Checks"
        block_modules.append(block_module)
        block_prop = f"pullBlock{tag}Valid"
        block_theorem = f"pull_block_{tag}_verified"
        body = f"""def {block_prop} : Prop :=
    {conjunction(column_props)}

theorem {block_theorem} : {block_prop} := by
  {witnesses(column_theorems)}"""
        emit(
            block_module,
            [f"{PREFIX}.{module}" for module in column_modules],
            "S4YoungPullback",
            body,
        )

    foundation_body = """structure PullbackFoundationVerified : Prop where
  sparse4 : ∀ (a : Fin 352) (i : Fin 32),
    S4YoungSparse4ExactBase.sparseCoeff a i = S4Young4Data.entry a i
  sparse31 : ∀ (a : Fin 352) (i : Fin 52),
    S4YoungSparse31ExactBase.sparseCoeff a i = S4Young31Data.entry a i
  sparse22 : ∀ (a : Fin 352) (i : Fin 34),
    S4YoungSparse22ExactBase.sparseCoeff a i = S4Young22Data.entry a i
  sparse211 : ∀ (a : Fin 352) (i : Fin 30),
    S4YoungSparse211ExactBase.sparseCoeff a i = S4Young211Data.entry a i
  sparse1111 : ∀ (a : Fin 352) (i : Fin 6),
    S4YoungSparse1111ExactBase.sparseCoeff a i = S4Young1111Data.entry a i
  pull4 : pullBlock4Valid
  pull31 : pullBlock31Valid
  pull22 : pullBlock22Valid
  pull211 : pullBlock211Valid
  pull1111 : pullBlock1111Valid

theorem pullback_foundation_verified : PullbackFoundationVerified where
  sparse4 := sparse_exact_4
  sparse31 := sparse_exact_31
  sparse22 := sparse_exact_22
  sparse211 := sparse_exact_211
  sparse1111 := sparse_exact_1111
  pull4 := pull_block_4_verified
  pull31 := pull_block_31_verified
  pull22 := pull_block_22_verified
  pull211 := pull_block_211_verified
  pull1111 := pull_block_1111_verified"""
    emit(
        "S4YoungPullbackChecks",
        [f"{PREFIX}.S4YoungSparse{tag}ExactChecks" for tag, _ in BLOCKS]
        + [f"{PREFIX}.{module}" for module in block_modules],
        "S4YoungPullback",
        foundation_body,
    )

    final_body = """theorem pullPartChunk_eq_of_valid
    {entries : Array (Array Int)} {block : Fin 5}
    {i partStart partCount start count : Nat}
    (h : pullPartChunkValid entries block i partStart partCount start count = true) :
    rawPullPartChunkCoefficients block i partStart partCount start count =
      storedPartChunkCoefficients entries block start count := by
  simpa [pullPartChunkValid] using h
"""
    emit(
        "S4YoungPullback",
        [f"{PREFIX}.S4YoungPullbackChecks"],
        "S4YoungPullback",
        final_body,
    )

    target_path = Path(args.target_list)
    target_path.parent.mkdir(parents=True, exist_ok=True)
    write_if_changed(target_path, "\n".join(targets) + "\n")
    removed = 0
    for pattern in (
        "S4YoungPullback*.lean",
        "S4YoungPullPart*.lean",
        "S4YoungPullFull*.lean",
    ):
        for path in lean_root.glob(pattern):
            if path.resolve() not in emitted_paths:
                path.unlink()
                removed += 1
    print(
        f"wrote {len(targets)} Young-pullback modules to {lean_root}; "
        f"removed {removed} obsolete generated modules"
    )


if __name__ == "__main__":
    main()
