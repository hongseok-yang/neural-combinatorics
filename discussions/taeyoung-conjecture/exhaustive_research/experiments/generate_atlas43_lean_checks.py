"""Generate bounded-memory Lean audit modules for the Atlas-43 certificate.

Each generated module asks the kernel to validate one matrix row.  This is
deliberately finer than the mathematical decomposition: a single eight-row
`decide` can retain tens of gigabytes of reduction state, whereas independent
row modules have predictable memory and can be cached separately by Lake.

The same rule is used for the derived raw-group arithmetic, the final
coefficient table, and the finite partition check.  Aggregate modules only
dispatch to already checked lemmas; they never repeat a large `decide`.
"""

from __future__ import annotations

import argparse
from pathlib import Path


PREFIX = "Taeyoung.Methods.RootedSOS"
NAMESPACE = "Taeyoung.Methods.RootedSOS.Atlas43Coefficients"


def write_if_changed(path: Path, contents: str) -> None:
    """Preserve mtimes, and therefore Lake artifacts, for identical modules."""
    if path.exists() and path.read_text(encoding="utf-8") == contents:
        return
    path.write_text(contents, encoding="utf-8")


def row_source(block: int, row: int) -> str:
    digit = "₀" if block == 0 else "₁"
    return f"""import {PREFIX}.Atlas43CoefficientBase

namespace {NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem block{block}_witness_row_{row:03d} :
    block{digit}WitnessRowValid {row} = true := by
  decide +kernel

end {NAMESPACE}
"""


def aggregate_source() -> str:
    imports = [
        f"import {PREFIX}.Atlas43CommonBlock{block}Row{row:03d}"
        for block, count in ((0, 128), (1, 64))
        for row in range(count)
    ]
    block0_lemmas = ", ".join(
        f"block0_witness_row_{row:03d}" for row in range(128)
    )
    block1_lemmas = ", ".join(
        f"block1_witness_row_{row:03d}" for row in range(64)
    )
    return "\n".join(imports) + f"""

/-! # Complete bounded-memory kernel audit of the common Gram witness -/

namespace {NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem witness_shape_valid : witnessShapeCheck = true := by
  decide +kernel

theorem arithmetic_bound_formulas_valid :
    arithmeticBoundFormulasValid = true := by
  decide +kernel

theorem all_block0_witness_rows_valid :
    ∀ row : Fin 128, block₀WitnessRowValid row = true := by
  intro row
  fin_cases row <;> simp [{block0_lemmas}]

theorem all_block1_witness_rows_valid :
    ∀ row : Fin 64, block₁WitnessRowValid row = true := by
  intro row
  fin_cases row <;> simp [{block1_lemmas}]

end {NAMESPACE}
"""


def exceptional_step0_source(step: int, slot: int) -> str:
    return f"""import {PREFIX}.Atlas43RawGroupCellBase

namespace {NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem exceptional_step0_{step:03d}_{slot} :
    ∀ row : Fin 33,
      rawGroupExceptionalStep₀Valid {step} row {slot} = true := by
  decide +kernel

end {NAMESPACE}
"""


def exceptional_step1_source(step: int) -> str:
    return f"""import {PREFIX}.Atlas43RawGroupCellBase

namespace {NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem exceptional_step1_{step:03d} :
    ∀ row : Fin 33,
      rawGroupExceptionalStep₁Valid {step} row = true := by
  decide +kernel

end {NAMESPACE}
"""


def exceptional_base0_source(slot: int) -> str:
    return f"""import {PREFIX}.Atlas43RawGroupCellBase

namespace {NAMESPACE}

theorem exceptional_base0_{slot} :
    ∀ row : Fin 33, rawGroupExceptionalBase₀Valid row {slot} = true := by
  decide +kernel

end {NAMESPACE}
"""


def exceptional_base1_source() -> str:
    return f"""import {PREFIX}.Atlas43RawGroupCellBase

namespace {NAMESPACE}

theorem exceptional_base1 :
    ∀ row : Fin 33, rawGroupExceptionalBase₁Valid row = true := by
  decide +kernel

end {NAMESPACE}
"""


def raw_group_final_cell_source(row: int, slot: int) -> str:
    return f"""import {PREFIX}.Atlas43RawGroupCellBase

namespace {NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem raw_group_final_cell_{row:03d}_{slot} :
    rawGroupFinalCellValid {row} {slot} = true := by
  decide +kernel

end {NAMESPACE}
"""


def scaled_correction_row_source(block: int, row: int) -> str:
    order = 107 if block == 0 else 48
    digit = "₀" if block == 0 else "₁"
    return f"""import {PREFIX}.Atlas43RawGroupCellBase

namespace {NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem scaled_correction{block}_row_{row:03d} :
    ∀ j : Fin {order}, stagedCorrectionRational{digit}Valid {row} j = true := by
  decide +kernel

end {NAMESPACE}
"""


def scaled_group_cell_source(row: int, slot: int) -> str:
    return f"""import {PREFIX}.Atlas43RawGroupCellBase

namespace {NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem scaled_group_cell_{row:03d}_{slot} :
    rawGroupScaledCellValid {row} {slot} = true := by
  decide +kernel

end {NAMESPACE}
"""


def exceptional_pair_weight0_source(entry: int, slot: int) -> str:
    return f"""import {PREFIX}.Atlas43RawGroupCellBase

namespace {NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem exceptional_pair_weight0_{entry:02d}_{slot} :
    exceptionalPairWeight₀EncodingValid {entry} {slot} = true := by
  decide +kernel

end {NAMESPACE}
"""


def exceptional_pair_weight1_source(entry: int) -> str:
    return f"""import {PREFIX}.Atlas43RawGroupCellBase

namespace {NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem exceptional_pair_weight1_{entry:02d} :
    exceptionalPairWeight₁EncodingValid {entry} = true := by
  decide +kernel

end {NAMESPACE}
"""


def scaled_correction_aggregate_source() -> str:
    imports0 = [f"import {PREFIX}.Atlas43ScaledCorrection0Row{row:03d}"
        for row in range(107)]
    imports1 = [f"import {PREFIX}.Atlas43ScaledCorrection1Row{row:03d}"
        for row in range(48)]
    lemmas0 = ", ".join(
        f"scaled_correction0_row_{row:03d}" for row in range(107)
    )
    lemmas1 = ", ".join(
        f"scaled_correction1_row_{row:03d}" for row in range(48)
    )
    exact0 = "\n".join(
        f"  · exact scaled_correction0_row_{row:03d} j" for row in range(107)
    )
    exact1 = "\n".join(
        f"  · exact scaled_correction1_row_{row:03d} j" for row in range(48)
    )
    imports = imports0 + imports1
    return "\n".join(imports) + f"""

/-! # Bounded-memory audit of the exceptional correction matrices -/

namespace {NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem all_scaled_correction0_rational_valid (i j : Fin 107) :
    stagedCorrectionRational₀Valid i j = true := by
  fin_cases i
{exact0}

theorem all_scaled_correction1_rational_valid (i j : Fin 48) :
    stagedCorrectionRational₁Valid i j = true := by
  fin_cases i
{exact1}

end {NAMESPACE}
"""


def scaled_group_aggregate_source() -> str:
    imports_cells = [
        f"import {PREFIX}.Atlas43ScaledGroupCell{row:03d}_{slot}"
        for row in range(33)
        for slot in range(4)
    ]
    lemmas_cells = ", ".join(
        f"scaled_group_cell_{row:03d}_{slot}"
        for row in range(33)
        for slot in range(4)
    )
    exact_cells = "\n".join(
        f"  · exact scaled_group_cell_{row:03d}_{slot}"
        for row in range(33)
        for slot in range(4)
    )
    return "\n".join(imports_cells) + f"""

/-! # Bounded-memory audit of the 33 scaled group totals -/

namespace {NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem all_scaled_group_cells_valid
    (row : Fin 33) (slot : Fin 4) :
    rawGroupScaledCellValid row slot = true := by
  fin_cases row <;> fin_cases slot
{exact_cells}

end {NAMESPACE}
"""


def exceptional_pair_weight_aggregate_source() -> str:
    imports_weights0 = [
        f"import {PREFIX}.Atlas43ExceptionalPairWeight0_{entry:02d}_{slot}"
        for entry in range(66)
        for slot in range(3)
    ]
    imports_weights1 = [
        f"import {PREFIX}.Atlas43ExceptionalPairWeight1_{entry:02d}"
        for entry in range(15)
    ]
    lemmas_weights0 = ", ".join(
        f"exceptional_pair_weight0_{entry:02d}_{slot}"
        for entry in range(66)
        for slot in range(3)
    )
    lemmas_weights1 = ", ".join(
        f"exceptional_pair_weight1_{entry:02d}" for entry in range(15)
    )
    exact_weights0 = "\n".join(
        f"  · exact exceptional_pair_weight0_{entry:02d}_{slot}"
        for entry in range(66)
        for slot in range(3)
    )
    exact_weights1 = "\n".join(
        f"  · exact exceptional_pair_weight1_{entry:02d}"
        for entry in range(15)
    )
    imports = imports_weights0 + imports_weights1
    return "\n".join(imports) + f"""

/-! # Bounded-memory audit of the exceptional pair weights -/

namespace {NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem all_exceptional_pair_weight0_valid
    (entry : Fin 66) (slot : Fin 3) :
    exceptionalPairWeight₀EncodingValid entry slot = true := by
  fin_cases entry <;> fin_cases slot
{exact_weights0}

theorem all_exceptional_pair_weight1_valid
    (entry : Fin 15) :
    exceptionalPairWeight₁EncodingValid entry = true := by
  fin_cases entry
{exact_weights1}

end {NAMESPACE}
"""


def raw_group_aggregate_source() -> str:
    return f"""import {PREFIX}.Atlas43ScaledCorrectionChecks
import {PREFIX}.Atlas43ExceptionalPairWeightChecks
import {PREFIX}.Atlas43ScaledGroupChecks

/-! # Complete bounded-memory audit of the 33 raw graph groups

The three imported modules are deliberately separate compilation checkpoints so
that Lean never has to elaborate every certificate layer in one source file.
-/
"""


def coefficient_cell_source(core: int, degree: int) -> str:
    return f"""import {PREFIX}.Atlas43RawGroups

namespace {NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem coefficient_cell_{core:02d}_{degree} :
    (certificateCoefficient {core} {degree} ==
      targetCoefficient {core} {degree}) = true := by
  decide +kernel

end {NAMESPACE}
"""


def coefficient_aggregate_source() -> str:
    imports = [
        f"import {PREFIX}.Atlas43CoefficientCell{core:02d}_{degree}"
        for core in range(53)
        for degree in range(5)
    ]
    lemmas = ", ".join(
        f"coefficient_cell_{core:02d}_{degree}"
        for core in range(53)
        for degree in range(5)
    )
    exact_cells = "\n".join(
        f"  · exact coefficient_cell_{core:02d}_{degree}"
        for core in range(53)
        for degree in range(5)
    )
    return "\n".join(imports) + f"""

/-! # Complete bounded-memory audit of the final coefficient table -/

namespace {NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem all_coefficient_equations_valid :
    allCoefficientEquationsValid = true := by
  simp only [allCoefficientEquationsValid, List.all_eq_true,
    List.mem_range]
  intro core hcore degree hdegree
  interval_cases core <;> interval_cases degree
{exact_cells}

end {NAMESPACE}
"""


def partition_row_source(row: int) -> str:
    return f"""import {PREFIX}.Atlas43RawGroupCellBase

namespace {NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem raw_group_partition_row_{row:02d} :
    ∀ b : Fin 64,
      claimedRawGroupIndex {row} b < 33 ∧
      sameRawGroup
        (rawGroupKey (claimedRawGroupIndexFin {row} b)).1
        (rawGroupKey (claimedRawGroupIndexFin {row} b)).2 {row} b ∧
        ∀ other : Fin 33,
          sameRawGroup (rawGroupKey other).1 (rawGroupKey other).2 {row} b →
            other = claimedRawGroupIndexFin {row} b := by
  decide +kernel

end {NAMESPACE}
"""


def partition_aggregate_source() -> str:
    imports = [
        f"import {PREFIX}.Atlas43PartitionRow{row:02d}"
        for row in range(64)
    ]
    lemmas = ", ".join(
        f"raw_group_partition_row_{row:02d}" for row in range(64)
    )
    exact_rows = "\n".join(
        f"  · exact raw_group_partition_row_{row:02d} b" for row in range(64)
    )
    return "\n".join(imports) + f"""

/-! # Bounded-memory audit that the 33 raw groups partition all flag pairs -/

namespace {NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem raw_group_index_checked (a b : Fin 64) :
    claimedRawGroupIndex a b < 33 ∧
      sameRawGroup
        (rawGroupKey (claimedRawGroupIndexFin a b)).1
        (rawGroupKey (claimedRawGroupIndexFin a b)).2 a b ∧
      ∀ other : Fin 33,
        sameRawGroup (rawGroupKey other).1 (rawGroupKey other).2 a b →
          other = claimedRawGroupIndexFin a b := by
  fin_cases a
{exact_rows}

theorem raw_group_partition_checked (a b : Fin 64) :
    ∃ group : Fin 33,
      sameRawGroup (rawGroupKey group).1 (rawGroupKey group).2 a b ∧
        ∀ other : Fin 33,
          sameRawGroup (rawGroupKey other).1 (rawGroupKey other).2 a b →
            other = group := by
  refine ⟨claimedRawGroupIndexFin a b, ?_, ?_⟩
  · exact (raw_group_index_checked a b).2.1
  · exact (raw_group_index_checked a b).2.2

theorem raw_group_isolated_le_two_checked (row : Fin 33) :
    (rawGroupKey row).2 ≤ 2 := by
  fin_cases row <;> decide

theorem raw_group_core_lt_53_checked (row : Fin 33) :
    (rawGroupKey row).1 < 53 := by
  fin_cases row <;> decide

end {NAMESPACE}
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "lean_directory",
        nargs="?",
        default="lean/Taeyoung/Methods/RootedSOS",
    )
    args = parser.parse_args()
    destination = Path(args.lean_directory)
    destination.mkdir(parents=True, exist_ok=True)

    for block, count in ((0, 128), (1, 64)):
        for row in range(count):
            path = destination / f"Atlas43CommonBlock{block}Row{row:03d}.lean"
            write_if_changed(path, row_source(block, row))

    write_if_changed(
        destination / "Atlas43CommonGramChecks.lean", aggregate_source()
    )

    for row in range(107):
        write_if_changed(
            destination / f"Atlas43ScaledCorrection0Row{row:03d}.lean",
            scaled_correction_row_source(0, row),
        )
    for row in range(48):
        write_if_changed(
            destination / f"Atlas43ScaledCorrection1Row{row:03d}.lean",
            scaled_correction_row_source(1, row),
        )
    for row in range(33):
        for slot in range(4):
            write_if_changed(
                destination / f"Atlas43ScaledGroupCell{row:03d}_{slot}.lean",
                scaled_group_cell_source(row, slot),
            )
    for entry in range(66):
        for slot in range(3):
            write_if_changed(
                destination / f"Atlas43ExceptionalPairWeight0_{entry:02d}_{slot}.lean",
                exceptional_pair_weight0_source(entry, slot),
            )
    for entry in range(15):
        write_if_changed(
            destination / f"Atlas43ExceptionalPairWeight1_{entry:02d}.lean",
            exceptional_pair_weight1_source(entry),
        )
    write_if_changed(
        destination / "Atlas43ScaledCorrectionChecks.lean",
        scaled_correction_aggregate_source(),
    )
    write_if_changed(
        destination / "Atlas43ExceptionalPairWeightChecks.lean",
        exceptional_pair_weight_aggregate_source(),
    )
    write_if_changed(
        destination / "Atlas43ScaledGroupChecks.lean",
        scaled_group_aggregate_source(),
    )
    write_if_changed(
        destination / "Atlas43RawGroups.lean",
        raw_group_aggregate_source(),
    )

    for core in range(53):
        for degree in range(5):
            write_if_changed(
                destination / f"Atlas43CoefficientCell{core:02d}_{degree}.lean",
                coefficient_cell_source(core, degree),
            )
    write_if_changed(
        destination / "Atlas43CoefficientChecks.lean", coefficient_aggregate_source()
    )

    for row in range(64):
        write_if_changed(
            destination / f"Atlas43PartitionRow{row:02d}.lean",
            partition_row_source(row),
        )
    write_if_changed(
        destination / "Atlas43PartitionChecks.lean", partition_aggregate_source()
    )


if __name__ == "__main__":
    main()
