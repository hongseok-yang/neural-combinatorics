import OddCycleBound.IntermediateRegion.Scalar.ParameterFacts
import OddCycleBound.IntermediateRegion.Scalar.EigenvalueAlgebra

/-!
# LeadingEigenvalue-gap coordinates

This file formalizes the corrected `(e, kappa)` chart for the complete
admissible the intermediate region scalar domain.
-/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

def kappaMax (e : Real) : Real := (1 - e) / (1 + e)
def kappaQ (e : Real) : Real := (1 - 3 * e) / (6 * e)
def chartAlpha (e : Real) : Real := (1 - e) / 2
def chartQ (e kappa : Real) : Real := chartAlpha e - kappa * e
def chartP (e kappa : Real) : Real := chartAlpha e + (1 + kappa) * e

theorem chart_quadratic_identity (e kappa : Real) :
    chartAlpha e ^ 2 + chartQ e kappa * chartAlpha e -
        chartQ e kappa =
      e / 2 * (kappa * (1 + e) - (1 - e)) := by
  unfold chartQ chartAlpha
  ring

theorem chart_q_gt_third
    {e kappa : Real} (he : 0 < e) (hkq : kappa < kappaQ e) :
    1 / 3 < chartQ e kappa := by
  have hden : 0 < 6 * e := by positivity
  have hmul := (lt_div_iff₀ hden).mp hkq
  unfold kappaQ chartQ chartAlpha at *
  linarith

theorem chart_alpha_pos {e : Real} (helt : e < 1 / 3) :
    0 < chartAlpha e := by
  unfold chartAlpha
  linarith

theorem chart_alpha_lt_half {e : Real} (he : 0 < e) :
    chartAlpha e < 1 / 2 := by
  unfold chartAlpha
  linarith

theorem chart_leading_eigenvalue_quadratic_nonpos
    {e kappa : Real} (he : 0 < e) (hkmax : kappa <= kappaMax e) :
    chartAlpha e ^ 2 + chartQ e kappa * chartAlpha e -
        chartQ e kappa <= 0 := by
  have hden : 0 < 1 + e := by linarith
  have hmul := (le_div_iff₀ hden).mp hkmax
  rw [chart_quadratic_identity]
  unfold kappaMax at hmul
  nlinarith

/-- Construct an admissible triple from a point in the chart domain. -/
noncomputable def AdmissibleParams.ofChart
    (e kappa : Real) (m : Nat)
    (he : 0 < e) (hethird : e < 1 / 3)
    (hk : 0 < kappa) (hkmax : kappa <= kappaMax e)
    (hkq : kappa < kappaQ e)
    (hm : Odd m) (hm9 : 9 <= m) : AdmissibleParams where
  q := chartQ e kappa
  alpha := chartAlpha e
  m := m
  q_gt_third := chart_q_gt_third he hkq
  q_lt_half := by
    have hqa : chartQ e kappa < chartAlpha e := by
      unfold chartQ
      nlinarith
    exact hqa.trans (chart_alpha_lt_half he)
  alpha_gt_q := by
    unfold chartQ
    nlinarith
  alpha_le_radius := by
    apply alpha_le_leadingEigenvalueRadius_of_quadratic
    · have := chart_q_gt_third he hkq
      linarith
    · exact le_of_lt (chart_alpha_pos hethird)
    · exact chart_leading_eigenvalue_quadratic_nonpos he hkmax
  m_odd := hm
  m_ge_nine := hm9

namespace AdmissibleParams

variable (P : AdmissibleParams)

theorem e_pos : 0 < P.e := by
  dsimp [e]
  linarith [P.alpha_lt_half]

theorem e_lt_third : P.e < 1 / 3 := by
  dsimp [e]
  have halphaThird : 1 / 3 < P.alpha := P.q_gt_third.trans P.alpha_gt_q
  linarith

theorem d_pos : 0 < P.d := by
  dsimp [d]
  exact sub_pos.mpr P.alpha_gt_q

theorem kappa_pos : 0 < P.kappa := by
  unfold kappa
  exact div_pos P.d_pos P.e_pos

theorem kappa_mul_e : P.kappa * P.e = P.d := by
  unfold kappa
  exact div_mul_cancel₀ P.d P.e_pos.ne'

theorem alpha_eq_chart : P.alpha = chartAlpha P.e := by
  unfold chartAlpha e
  ring

theorem q_eq_chart : P.q = chartQ P.e P.kappa := by
  unfold chartQ
  rw [← P.alpha_eq_chart, P.kappa_mul_e]
  unfold d
  ring

theorem p_eq_chart : P.p = chartP P.e P.kappa := by
  unfold chartP
  rw [← P.alpha_eq_chart]
  rw [show (1 + P.kappa) * P.e = P.e + P.kappa * P.e by ring,
    P.kappa_mul_e]
  unfold p d e
  ring

theorem kappa_le_max : P.kappa <= kappaMax P.e := by
  have hquad := P.leading_eigenvalue_quadratic_nonpos
  have hid := chart_quadratic_identity P.e P.kappa
  rw [← P.alpha_eq_chart, ← P.q_eq_chart] at hid
  have hbracket : P.kappa * (1 + P.e) <= 1 - P.e := by
    have hepos : 0 < P.e / 2 := div_pos P.e_pos (by norm_num)
    have hprod : P.e / 2 *
        (P.kappa * (1 + P.e) - (1 - P.e)) <= 0 := by
      rw [← hid]
      exact hquad
    have := nonpos_of_mul_nonpos_right hprod hepos
    linarith
  have hden : 0 < 1 + P.e := by linarith [P.e_pos]
  unfold kappaMax
  exact (le_div_iff₀ hden).2 hbracket

theorem kappa_lt_q : P.kappa < kappaQ P.e := by
  have he : 0 < 6 * P.e := mul_pos (by norm_num) P.e_pos
  apply (lt_div_iff₀ he).2
  have hke := P.kappa_mul_e
  dsimp [d, e] at hke ⊢
  linarith [P.q_gt_third]

theorem L_sq_chart :
    P.L ^ 2 = P.alpha * P.e - P.d * (P.d + P.e) := by
  rw [P.L_sq]
  unfold p d e
  ring

theorem xi_chart :
    P.xi = (1 - P.e) ^ 2 * P.kappa / P.e := by
  unfold xi
  rw [← P.kappa_mul_e]
  have he : P.e ≠ 0 := P.e_pos.ne'
  have halpha : 2 * P.alpha = 1 - P.e := by
    unfold e
    ring
  have hsq : 4 * P.alpha ^ 2 = (1 - P.e) ^ 2 := by
    calc
      4 * P.alpha ^ 2 = (2 * P.alpha) ^ 2 := by ring
      _ = (1 - P.e) ^ 2 := by rw [halpha]
  rw [hsq]
  field_simp [he]

theorem one_div_x_chart :
    1 / P.x = 1 + 2 * (1 + P.kappa) * P.e / (1 - P.e) := by
  have halpha : 0 < P.alpha := P.alpha_pos
  have honee : 0 < 1 - P.e := by
    unfold e
    linarith
  unfold x
  rw [P.p_eq_chart]
  unfold chartP
  rw [← P.alpha_eq_chart]
  have heq : 1 - P.e = 2 * P.alpha := by
    unfold e
    ring
  rw [heq]
  field_simp [halpha.ne']

theorem one_sub_tau_chart :
    1 - P.tau = 2 * P.kappa * P.e / (1 - P.e) := by
  have halpha : 0 < P.alpha := P.alpha_pos
  unfold tau
  rw [P.q_eq_chart]
  unfold chartQ
  rw [← P.alpha_eq_chart]
  have heq : 1 - P.e = 2 * P.alpha := by
    unfold e
    ring
  rw [heq]
  field_simp [halpha.ne']
  ring

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
