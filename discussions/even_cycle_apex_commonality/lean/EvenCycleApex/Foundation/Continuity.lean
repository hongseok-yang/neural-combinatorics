-- Provenance (plan D7): copied from
--   discussions/schur_decomposition/cycle_commonality/lean/CycleCommonality/Continuity.lean
--   at neural-combinatorics commit e2d96440.
-- Changes: import paths and the namespace prefix CycleCommonality -> EvenCycleApex; pruned in M11
-- (declarations unused by this development removed, module docstring updated to match).
import EvenCycleApex.Foundation.Fubini

/-!
# The `L¹` norm of a kernel

`l1norm μ D = ∫ x, ∫ y, |D x y| ∂μ ∂μ`, with the facts about it that the `L¹` step approximation
(`StepApprox.lean`) and the Lipschitz bounds of `Graph/Lipschitz.lean` use: nonnegativity, the
swap of the two integrals, and measurability and integrability of row sums.
-/

open MeasureTheory EvenCycleApex.Foundation

set_option linter.unusedSectionVars false

namespace EvenCycleApex

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The `L¹` norm of a kernel. -/
noncomputable def l1norm (μ : Measure Ω) (D : Ω → Ω → ℝ) : ℝ := ∫ x, ∫ y, |D x y| ∂μ ∂μ

lemma l1norm_nonneg (D : Ω → Ω → ℝ) : 0 ≤ l1norm μ D :=
  integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _

lemma goodK_abs {D : Ω → Ω → ℝ} (hD : GoodK D) : GoodK (fun x y => |D x y|) := by
  obtain ⟨C, hC0, hC⟩ := hD.bdd
  exact ⟨hD.meas.abs, C, hC0, fun x y => by rw [abs_abs]; exact hC x y⟩

lemma goodK_sub' {K L : Ω → Ω → ℝ} (hK : GoodK K) (hL : GoodK L) :
    GoodK (fun x y => K x y - L x y) := by
  obtain ⟨C, hC0, hC⟩ := hK.bdd
  obtain ⟨C', hC0', hC'⟩ := hL.bdd
  refine ⟨hK.meas.sub hL.meas, C + C', by linarith, fun x y => ?_⟩
  have htri : |K x y - L x y| ≤ |K x y| + |L x y| := by
    rw [sub_eq_add_neg]
    exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
  exact htri.trans (add_le_add (hC x y) (hC' x y))

/-- Row sums of a bounded measurable kernel are measurable. -/
lemma rowsum_stronglyMeasurable {D : Ω → Ω → ℝ} (hD : GoodK D) :
    StronglyMeasurable (fun x => ∫ y, D x y ∂μ) :=
  (show StronglyMeasurable (Function.uncurry D) from
    hD.meas.stronglyMeasurable).integral_prod_right'

/-- Row sums of a bounded measurable kernel are integrable. -/
lemma rowsum_integrable {D : Ω → Ω → ℝ} (hD : GoodK D) :
    Integrable (fun x => ∫ y, D x y ∂μ) μ := by
  obtain ⟨C, _, hC⟩ := hD.bdd
  refine (integrable_const C).mono' (rowsum_stronglyMeasurable hD).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  calc |∫ y, D x y ∂μ| ≤ ∫ y, |D x y| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _y, C ∂μ := integral_mono (hD.integrable_row x).abs (integrable_const C) (hC x)
    _ = C := by simp

/-- Both iterated integrals of `|D|` agree. -/
lemma l1norm_swap {D : Ω → Ω → ℝ} (hD : GoodK D) :
    l1norm μ D = ∫ y, ∫ x, |D x y| ∂μ ∂μ := by
  have hint : Integrable (Function.uncurry fun x y => |D x y|) (μ.prod μ) :=
    (goodK_abs hD).integrable_prod
  exact integral_integral_swap hint

end EvenCycleApex
