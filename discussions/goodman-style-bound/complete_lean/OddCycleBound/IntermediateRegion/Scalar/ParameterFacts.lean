import OddCycleBound.IntermediateRegion.Scalar.ShapeElimination

/-!
# Elementary facts about admissible the intermediate region parameters

These lemmas centralize the sign and square-root facts used by the Envelope
reduction and the scalar branch analysis.
-/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

/-- The explicit leading_eigenvalue radius is strictly below `1/2` throughout Region
II. -/
theorem leadingEigenvalueRadius_lt_half {q : Real}
    (hq0 : 0 <= q) (hqhalf : q < 1 / 2) :
    leadingEigenvalueRadius q < 1 / 2 := by
  have hrad : 0 <= q ^ 2 + 4 * q := by positivity
  have hqone : 0 <= q + 1 := by linarith
  have hsqrt : Real.sqrt (q ^ 2 + 4 * q) < q + 1 := by
    apply (Real.sqrt_lt hrad hqone).2
    nlinarith
  unfold leadingEigenvalueRadius
  linarith

/-- The leading_eigenvalue radius is nonnegative. -/
theorem leadingEigenvalueRadius_nonneg {q : Real} (hq : 0 <= q) :
    0 <= leadingEigenvalueRadius q := by
  have hrad : 0 <= q ^ 2 + 4 * q := by positivity
  have hqSq : q ^ 2 <= q ^ 2 + 4 * q := by nlinarith
  have hsqrt : q <= Real.sqrt (q ^ 2 + 4 * q) :=
    Real.le_sqrt_of_sq_le hqSq
  unfold leadingEigenvalueRadius
  linarith

/-- The explicit radius is the positive root of the leading_eigenvalue quadratic. -/
theorem leadingEigenvalueRadius_quadratic_eq {q : Real} (hq : 0 <= q) :
    leadingEigenvalueRadius q ^ 2 + q * leadingEigenvalueRadius q - q = 0 := by
  let s := Real.sqrt (q ^ 2 + 4 * q)
  have hrad : 0 <= q ^ 2 + 4 * q := by positivity
  have hsq : s ^ 2 = q ^ 2 + 4 * q := by
    dsimp [s]
    exact Real.sq_sqrt hrad
  unfold leadingEigenvalueRadius
  dsimp [s] at hsq ⊢
  nlinarith

/-- Positivity of the manuscript quotient kernel below `p`. -/
theorem quotientKernel_pos
    {p lambda : Real} {m : Nat}
    (hp : 0 < p) (hlambda : 0 <= lambda) (hlt : lambda < p)
    (hm2 : 2 <= m) :
    0 < (p ^ (m - 1) - lambda ^ (m - 1)) / (p + lambda) := by
  have hexp : m - 1 ≠ 0 := by omega
  have hpow : lambda ^ (m - 1) < p ^ (m - 1) :=
    pow_lt_pow_left₀ hlt hlambda hexp
  exact div_pos (sub_pos.mpr hpow) (by linarith)

namespace AdmissibleParams

variable (P : AdmissibleParams)

theorem q_pos : 0 < P.q := by linarith [P.q_gt_third]
theorem q_nonneg : 0 <= P.q := le_of_lt P.q_pos
theorem p_gt_half : 1 / 2 < P.p := by
  dsimp [p]
  linarith [P.q_lt_half]
theorem p_pos : 0 < P.p := lt_trans (by norm_num) P.p_gt_half
theorem p_eq_one_sub_q : P.p = 1 - P.q := rfl
theorem alpha_pos : 0 < P.alpha := lt_trans P.q_pos P.alpha_gt_q
theorem alpha_nonneg : 0 <= P.alpha := le_of_lt P.alpha_pos

theorem alpha_lt_half : P.alpha < 1 / 2 :=
  P.alpha_le_radius.trans_lt
    (leadingEigenvalueRadius_lt_half P.q_nonneg P.q_lt_half)

theorem alpha_lt_p : P.alpha < P.p :=
  lt_trans P.alpha_lt_half P.p_gt_half

theorem leading_eigenvalue_quadratic_nonpos :
    P.alpha ^ 2 + P.q * P.alpha - P.q <= 0 := by
  let r := leadingEigenvalueRadius P.q
  have hr0 : 0 <= r := leadingEigenvalueRadius_nonneg P.q_nonneg
  have hroot : r ^ 2 + P.q * r - P.q = 0 :=
    leadingEigenvalueRadius_quadratic_eq P.q_nonneg
  have hdiff : 0 <= (r - P.alpha) * (r + P.alpha + P.q) :=
    mul_nonneg (sub_nonneg.mpr P.alpha_le_radius)
      (add_nonneg (add_nonneg hr0 P.alpha_nonneg) P.q_nonneg)
  nlinarith

theorem L_radicand_nonneg :
    0 <= P.p * P.q - P.alpha ^ 2 := by
  have hquad := P.leading_eigenvalue_quadratic_nonpos
  dsimp [p] at *
  have hqa : P.q ^ 2 < P.q * P.alpha := by
    nlinarith [mul_pos P.q_pos (sub_pos.mpr P.alpha_gt_q)]
  nlinarith

theorem L_sq : P.L ^ 2 = P.p * P.q - P.alpha ^ 2 := by
  unfold L
  exact Real.sq_sqrt P.L_radicand_nonneg

theorem L_nonneg : 0 <= P.L := Real.sqrt_nonneg _

theorem L_lt_alpha : P.L < P.alpha := by
  have hpq : P.p * P.q < 2 * P.alpha ^ 2 := by
    have hp2q : P.p < 2 * P.q := by
      dsimp [p]
      linarith [P.q_gt_third]
    have hpq2q : P.p * P.q < (2 * P.q) * P.q :=
      mul_lt_mul_of_pos_right hp2q P.q_pos
    have hqSq : P.q ^ 2 < P.alpha ^ 2 :=
      pow_lt_pow_left₀ P.alpha_gt_q P.q_nonneg (by norm_num)
    nlinarith
  have hsq : P.L ^ 2 < P.alpha ^ 2 := by
    rw [P.L_sq]
    linarith
  by_contra hnot
  have hale : P.alpha <= P.L := le_of_not_gt hnot
  have hsquareLe : P.alpha ^ 2 <= P.L ^ 2 :=
    pow_le_pow_left₀ P.alpha_nonneg hale 2
  exact (not_lt_of_ge hsquareLe) hsq

theorem L_lt_p : P.L < P.p := P.L_lt_alpha.trans P.alpha_lt_p

theorem f_pos : 0 < P.f := by
  dsimp [f]
  exact sub_pos.mpr P.L_lt_alpha

theorem k_alpha_pos : 0 < P.k P.alpha := by
  unfold k
  exact quotientKernel_pos P.p_pos P.alpha_nonneg P.alpha_lt_p
    (le_trans (by norm_num : 2 <= 9) P.m_ge_nine)

theorem k_L_pos : 0 < P.k P.L := by
  unfold k
  exact quotientKernel_pos P.p_pos P.L_nonneg P.L_lt_p
    (le_trans (by norm_num : 2 <= 9) P.m_ge_nine)

theorem A_pos : 0 < P.A := by
  unfold A
  have hmNat : 0 < P.m :=
    lt_of_lt_of_le (by norm_num : 0 < 9) P.m_ge_nine
  have hmpos : 0 < (P.m : Real) := by exact_mod_cast hmNat
  have hterm : 0 < (P.m : Real) * P.k P.alpha :=
    mul_pos hmpos P.k_alpha_pos
  have hlead : 0 <= 2 * P.L ^ (P.m - 2) :=
    mul_nonneg (by norm_num) (pow_nonneg P.L_nonneg _)
  linarith

theorem A_nonneg : 0 <= P.A := le_of_lt P.A_pos

theorem B_pos : 0 < P.B := by
  unfold B
  have hmNat : 0 < P.m :=
    lt_of_lt_of_le (by norm_num : 0 < 9) P.m_ge_nine
  have hmpos : 0 < (P.m : Real) := by exact_mod_cast hmNat
  have hterm : 0 < (P.m : Real) * P.k P.L :=
    mul_pos hmpos P.k_L_pos
  have hlead : 0 <= 2 * P.L ^ (P.m - 2) :=
    mul_nonneg (by norm_num) (pow_nonneg P.L_nonneg _)
  linarith

theorem C_pos : 0 < P.C := by
  unfold C
  have he : 0 < P.e := by dsimp [e]; linarith [P.alpha_lt_half]
  apply div_pos
  · exact mul_pos
      (mul_pos (mul_pos P.B_pos P.f_pos)
        (Real.sqrt_pos.2 (mul_pos (by norm_num) P.alpha_pos)))
      (sq_pos_of_pos he)
  · exact mul_pos (by norm_num) (sq_pos_of_pos P.alpha_pos)

theorem xi_pos : 0 < P.xi := by
  unfold xi d e
  have he : 0 < 1 - 2 * P.alpha := by linarith [P.alpha_lt_half]
  exact div_pos
    (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos P.alpha_pos))
      (sub_pos.mpr P.alpha_gt_q))
    (sq_pos_of_pos he)

theorem rho_pos : 0 < P.rho := by
  unfold rho
  exact mul_pos (div_pos P.A_pos P.B_pos)
    (div_pos (Real.sqrt_pos.2 P.alpha_pos)
      (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num))) P.f_pos))

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
