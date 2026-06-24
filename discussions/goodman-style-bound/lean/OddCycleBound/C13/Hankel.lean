import OddCycleBound.General.SumOfSquares
import OddCycleBound.Certificate

/-! # `C₁₃` L₅/L₆ Hankel blocks. `L₅ = s₀³·B₅` with `B₅ ≥ 0` by the `momcs` minor + a square;
`L₆ = 12 s₀⁶ ≥ 0` trivially. -/

open MeasureTheory
namespace OddCycleBound
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

set_option maxHeartbeats 2000000 in
lemma cert13_L5B (hU : IsGraphon U μ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/3) :
    0 ≤ 252*q^2*specMoment U μ 0^2 - 273*q*specMoment U μ 0^2 + 360*q*specMoment U μ 0*specMoment U μ 1 + 91*specMoment U μ 0^2 - 195*specMoment U μ 0*specMoment U μ 1 + 60*specMoment U μ 0*specMoment U μ 2 + 120*specMoment U μ 1^2 := by
  have hcs : (specMoment U μ 1)^2 ≤ (specMoment U μ 0) * (specMoment U μ 2) := by have h := momcs hU 0 1; simpa using h
  have hs0 := specMoment_zero_nonneg hU
  have hy : (0:ℝ) ≤ 1/3 - q := by linarith
  nlinarith [hcs, hs0, hq0, hy, mul_nonneg hq0 hy,
    sq_nonneg (360*(specMoment U μ 1) + (360*q-195)*(specMoment U μ 0)),
    mul_nonneg (mul_nonneg hq0 hy) (sq_nonneg (specMoment U μ 0)),
    mul_nonneg hq0 (sq_nonneg (specMoment U μ 0)), mul_nonneg hy (sq_nonneg (specMoment U μ 0))]

set_option maxHeartbeats 2000000 in
lemma cert13_L5 (hU : IsGraphon U μ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/3) :
    0 ≤ 252*q^2*specMoment U μ 0^5 - 273*q*specMoment U μ 0^5 + 360*q*specMoment U μ 0^4*specMoment U μ 1 + 91*specMoment U μ 0^5 - 195*specMoment U μ 0^4*specMoment U μ 1 + 60*specMoment U μ 0^4*specMoment U μ 2 + 120*specMoment U μ 0^3*specMoment U μ 1^2 := by
  have hB := cert13_L5B hU q hq0 hq1
  have hs0 := specMoment_zero_nonneg hU
  have e : 252*q^2*specMoment U μ 0^5 - 273*q*specMoment U μ 0^5 + 360*q*specMoment U μ 0^4*specMoment U μ 1 + 91*specMoment U μ 0^5 - 195*specMoment U μ 0^4*specMoment U μ 1 + 60*specMoment U μ 0^4*specMoment U μ 2 + 120*specMoment U μ 0^3*specMoment U μ 1^2 = (specMoment U μ 0)^3 * (252*q^2*specMoment U μ 0^2 - 273*q*specMoment U μ 0^2 + 360*q*specMoment U μ 0*specMoment U μ 1 + 91*specMoment U μ 0^2 - 195*specMoment U μ 0*specMoment U μ 1 + 60*specMoment U μ 0*specMoment U μ 2 + 120*specMoment U μ 1^2) := by ring
  rw [e]; exact mul_nonneg (pow_nonneg hs0 3) hB

lemma cert13_L6 (hU : IsGraphon U μ) : 0 ≤ 12*specMoment U μ 0^6 :=
  mul_nonneg (by norm_num) (pow_nonneg (specMoment_zero_nonneg hU) 6)

end OddCycleBound
