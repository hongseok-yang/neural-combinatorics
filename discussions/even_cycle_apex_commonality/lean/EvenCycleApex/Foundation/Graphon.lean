-- Provenance (plan D7): copied from
--   discussions/schur_decomposition/cycle_commonality/lean/CycleCommonality/Foundation/Graphon.lean
--   at neural-combinatorics commit e2d96440.
-- Changes: import paths and the namespace prefix CycleCommonality -> EvenCycleApex; pruned in M11
-- (declarations unused by this development removed, `good_smul` moved here from the removed
-- `PathDensity.lean`, module docstring updated to match).
import Mathlib

/-!
# Graphons on an arbitrary probability space

* `IsGraphon U μ` — `U : Ω → Ω → ℝ` is jointly measurable, symmetric and `[0,1]`-valued; this is
  the hypothesis on `W` in every public statement;
* `Good f` — bounded, strongly measurable real functions, and `good_smul`;
* `kernelOp U μ f x = ∫ y, U x y * f y`, the kernel form.
-/

open MeasureTheory

namespace EvenCycleApex.Foundation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A graphon: symmetric, jointly measurable, `[0,1]`-valued. -/
structure IsGraphon (U : Ω → Ω → ℝ) (μ : Measure Ω) : Prop where
  meas : Measurable (Function.uncurry U)
  nonneg : ∀ x y, 0 ≤ U x y
  le_one : ∀ x y, U x y ≤ 1
  symm : ∀ x y, U x y = U y x

/-- Bounded, strongly measurable real functions: the working space. -/
structure Good (f : Ω → ℝ) : Prop where
  meas : StronglyMeasurable f
  bdd : ∃ C, 0 ≤ C ∧ ∀ x, |f x| ≤ C

lemma good_smul (c : ℝ) {f : Ω → ℝ} (hf : Good f) : Good (c • f) := by
  obtain ⟨C, hC0, hC⟩ := hf.bdd
  refine ⟨hf.meas.const_smul c, ⟨|c| * C, mul_nonneg (abs_nonneg _) hC0, fun x => ?_⟩⟩
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)

variable {U : Ω → Ω → ℝ}

/-- The kernel form `kernelOp U f x = ∫ y, U x y * f y`. -/
noncomputable def kernelOp (U : Ω → Ω → ℝ) (μ : Measure Ω) (f : Ω → ℝ) : Ω → ℝ :=
  fun x => ∫ y, U x y * f y ∂μ

end EvenCycleApex.Foundation
