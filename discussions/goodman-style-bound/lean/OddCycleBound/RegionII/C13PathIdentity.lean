import OddCycleBound.C13
import OddCycleBound.HighDensity.Expansion

/-!
# Density-independent C13 path defect

The original `C13_path_integral` expands a large certificate polynomial
inline.  The high-density expansion package gives that polynomial the stable
name `momentPhi`.  This file records the path identity directly in that form;
no density assumption enters the identity.
-/

open MeasureTheory

namespace OddCycleBound.RegionII

open OddCycleBound.HighDensity

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 12000 in
theorem c13_path_defect_identity (hU : IsGraphon U μ) :
    trace μ (compPow μ (compl U) 12) =
      ((1 - edgeDensity U μ) ^ 13 -
        (1 - edgeDensity U μ) * edgeDensity U μ ^ 12) +
      momentPhi 13 (edgeDensity U μ) (specMoment U μ) +
      (pathDensity U μ 12 - trace μ (compPow μ U 12)) := by
  have hx1 : pathDensity U μ 1 = edgeDensity U μ := pathDensity_one hU
  have hxtwo := pathDensity_two hU
  have hxthree := pathDensity_three hU
  have hxfour := pathDensity_four hU
  have hxfive := pathDensity_five hU
  have hxsix := pathDensity_six hU
  have hxseven := pathDensity_seven hU
  have hxeight := pathDensity_eight hU
  have hxnine := pathDensity_nine hU
  have hxten := pathDensity_ten hU
  have hxeleven := pathDensity_eleven hU
  have hxtwelve := pathDensity_twelve hU
  rw [complTrace_necklace hU 11]
  simp only [pairing_pathIter_complIter_closed hU, complMean_succ hU,
    complMean_zero, pathDensity_zero, pairing_pathIter_zero,
    Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
    Nat.reduceSub, Nat.reduceAdd, mul_one, one_mul, mul_neg, neg_neg,
    zero_add, add_zero]
  rw [hx1, hxtwo, hxthree, hxfour, hxfive, hxsix, hxseven, hxeight,
    hxnine, hxten, hxeleven, hxtwelve]
  rw [momentPhi_eq_momentKernelExpansion]
  norm_num (config := { maxSteps := 10000000 })
    [momentKernelExpansion, momentKernelTerm, kerB, momentConv,
      Finset.sum_range_succ, Nat.choose]
  ring

theorem c13_path_bound_of_momentPhi_nonneg (hU : IsGraphon U μ)
    (hphi : 0 ≤ momentPhi 13 (edgeDensity U μ) (specMoment U μ)) :
    (1 - edgeDensity U μ) ^ 13 -
        (1 - edgeDensity U μ) * edgeDensity U μ ^ 12 ≤
      trace μ (compPow μ (compl U) 12) := by
  have hed : trace μ (compPow μ U 12) ≤ pathDensity U μ 12 :=
    edge_deletion_general hU 11
  rw [c13_path_defect_identity hU]
  linarith

end OddCycleBound.RegionII
