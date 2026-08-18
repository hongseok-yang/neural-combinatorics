import Taeyoung.Methods.OddCycleC5.Internal.Necklace

/-!
# The short-cycle `C₅` graphon bound

This file deliberately extracts only the length-five case needed by the
six-vertex Atlas project.  Its proof starts from integral kernel definitions;
it does not invoke a theorem about all odd cycles.
-/

open MeasureTheory

namespace Taeyoung.Methods.OddCycleC5.Internal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]
variable {U W : Ω → Ω → ℝ}

/-- Complement-form `C₅` inequality, assembled from the necklace identity,
the length-five moment sum-of-squares certificate, and edge deletion. -/
theorem C5_integral (hU : IsGraphon U μ) :
    trace μ (compPow μ (compl U) 4) ≥
      (1 - edgeDensity U μ) ^ 5 -
        (1 - edgeDensity U μ) * edgeDensity U μ ^ 4 := by
  have hx1 : pathDensity U μ 1 = edgeDensity U μ := pathDensity_one hU
  have hx2 : pathDensity U μ 2 =
      edgeDensity U μ ^ 2 + specMoment U μ 0 := pathDensity_two hU
  have hx3 : pathDensity U μ 3 =
      edgeDensity U μ ^ 3 + 2 * edgeDensity U μ * specMoment U μ 0 +
        specMoment U μ 1 := pathDensity_three hU
  have hx4 : pathDensity U μ 4 =
      edgeDensity U μ ^ 4 + 3 * edgeDensity U μ ^ 2 * specMoment U μ 0 +
        2 * edgeDensity U μ * specMoment U μ 1 + specMoment U μ 0 ^ 2 +
        specMoment U μ 2 := pathDensity_four hU
  have hed : trace μ (compPow μ U 4) ≤ pathDensity U μ 4 :=
    edge_deletion_general hU 3
  have hcert := specMoment_sos_five hU (edgeDensity U μ)
  rw [complTrace_necklace hU 3]
  simp only [pairing_pathIter_complIter_closed hU, complMean_succ hU,
    complMean_zero, pathDensity_zero, pairing_pathIter_zero,
    Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
    Nat.reduceSub, Nat.reduceAdd, mul_one, one_mul, mul_neg, neg_neg,
    zero_add, add_zero]
  rw [hx1, hx2, hx3, hx4]
  rw [hx4] at hed
  nlinarith [hcert, hed]

omit [MeasurableSpace Ω] in
/-- Taking the pointwise complement twice returns the original kernel. -/
theorem compl_compl (W : Ω → Ω → ℝ) : compl (compl W) = W := by
  funext x y
  simp only [compl]
  ring

/-- The edge density of the pointwise complement. -/
theorem edgeDensity_compl (hW : IsGraphon W μ) :
    edgeDensity (compl W) μ = 1 - edgeDensity W μ := by
  have hGW : GoodK W := goodK_of_isGraphon hW
  have hdegint : Integrable (degree W μ) μ :=
    hGW.colsum_integrable.congr (ae_of_all _ fun x => by
      rw [degree]
      exact integral_congr_ae (ae_of_all _ fun y => hW.symm y x))
  have hone : (∫ _x : Ω, (1 : ℝ) ∂μ) = 1 := by simp
  have hdeg : ∀ x, degree (compl W) μ x = 1 - degree W μ x := fun x => by
    show (∫ y, compl W x y ∂μ) = 1 - degree W μ x
    have hwk : (fun y => compl W x y) = fun y => (1 : ℝ) - W x y := rfl
    rw [hwk, integral_sub (integrable_const 1) (hGW.integrable_row x), hone,
      degree]
  show (∫ x, degree (compl W) μ x ∂μ) = 1 - edgeDensity W μ
  rw [integral_congr_ae (ae_of_all _ hdeg),
    integral_sub (integrable_const 1) hdegint, hone]
  rfl

/-- `C₅` in the original-kernel form. -/
theorem cycleDensity_five_bound (hW : IsGraphon W μ) :
    cycleDensity μ W 5 ≥
      edgeDensity W μ ^ 5 - edgeDensity W μ * (1 - edgeDensity W μ) ^ 4 := by
  have h := C5_integral (isGraphon_compl hW)
  rw [compl_compl, edgeDensity_compl hW,
    show (1 : ℝ) - (1 - edgeDensity W μ) = edgeDensity W μ from by ring] at h
  exact h

end Taeyoung.Methods.OddCycleC5.Internal
