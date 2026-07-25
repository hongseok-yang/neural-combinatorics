import OddCycleBound.IntermediateRegion.Scalar.ThreeGeometric
import OddCycleBound.IntermediateRegion.DirectedKernel

/-! # Scalar envelope-value bounds -/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar
namespace AdmissibleParams

variable (P : AdmissibleParams)

def rhoLo : Real :=
  (1 - P.x ^ 14) * Real.sqrt P.alpha /
    (2 * Real.sqrt 2 * P.f * (1 + P.x))

theorem k_eq_directedKernel (lambda : Real) (hlambda : -P.p <= lambda)
    (hden : P.p + lambda ≠ 0) :
    P.k lambda = IntermediateRegion.directedKernel P.p P.m lambda := by
  unfold k
  symm
  exact IntermediateRegion.directedKernel_eq_div P.m_odd
    (le_trans (by norm_num) P.m_ge_nine) hlambda hden

theorem k_alpha_le_k_L : P.k P.alpha <= P.k P.L := by
  rw [P.k_eq_directedKernel P.alpha
      ((neg_nonpos.mpr P.p_pos.le).trans P.alpha_nonneg)
      (ne_of_gt (add_pos P.p_pos P.alpha_pos)),
    P.k_eq_directedKernel P.L
      ((neg_nonpos.mpr P.p_pos.le).trans P.L_nonneg)
      (ne_of_gt (add_pos_of_pos_of_nonneg P.p_pos P.L_nonneg))]
  exact IntermediateRegion.directedKernel_anti_on_nonneg P.p_pos P.L_nonneg
    P.L_lt_alpha.le P.m_odd (le_trans (by norm_num) P.m_ge_nine)

theorem k_ratio_le_A_div_B :
    P.k P.alpha / P.k P.L <= P.A / P.B := by
  rw [div_le_div_iff₀ P.k_L_pos P.B_pos]
  unfold A B
  have hz : 0 <= 2 * P.L ^ (P.m - 2) :=
    mul_nonneg (by norm_num) (pow_nonneg P.L_nonneg _)
  have hk := P.k_alpha_le_k_L
  nlinarith [mul_nonneg hz (sub_nonneg.mpr hk)]

theorem k_ratio_formula (lambda ratio : Real)
    (hlambda : 0 <= lambda) (hratio : ratio = lambda / P.p) :
    P.k lambda =
      P.p ^ (P.m - 2) * (1 - ratio ^ (P.m - 1)) / (1 + ratio) := by
  have hm15 := P.m_ge_nine
  have hm1 : P.m - 2 + 1 = P.m - 1 := by omega
  have hpPow : P.p ^ (P.m - 2) ≠ 0 := pow_ne_zero _ P.p_pos.ne'
  have hpSucc : P.p ^ (P.m - 1) = P.p ^ (P.m - 2) * P.p := by
    rw [← pow_succ, hm1]
  unfold k
  subst ratio
  rw [div_pow, hpSucc]
  field_simp [P.p_pos.ne', hpPow]

theorem k_alpha_formula :
    P.k P.alpha =
      P.p ^ (P.m - 2) * (1 - P.x ^ (P.m - 1)) / (1 + P.x) :=
  P.k_ratio_formula P.alpha P.x P.alpha_nonneg rfl

theorem k_L_formula :
    P.k P.L =
      P.p ^ (P.m - 2) * (1 - P.y ^ (P.m - 1)) / (1 + P.y) :=
  P.k_ratio_formula P.L P.y P.L_nonneg rfl

theorem one_sub_x_pow_pos : 0 < 1 - P.x ^ (P.m - 1) := by
  have hx0 : 0 <= P.x := div_nonneg P.alpha_nonneg P.p_pos.le
  have hx1 := P.x_lt_one
  have hm15 := P.m_ge_nine
  have hexp : P.m - 1 ≠ 0 := by omega
  exact sub_pos.mpr (pow_lt_one₀ hx0 hx1 hexp)

theorem one_sub_y_pow_pos : 0 < 1 - P.y ^ (P.m - 1) := by
  have hy1 : P.y < 1 := P.y_lt_s.trans P.s_lt_x |>.trans P.x_lt_one
  have hm15 := P.m_ge_nine
  have hexp : P.m - 1 ≠ 0 := by omega
  exact sub_pos.mpr (pow_lt_one₀ P.y_nonneg hy1 hexp)

theorem normalized_k_ratio_lower :
    (1 - P.x ^ (P.m - 1)) / (1 + P.x) <=
      P.k P.alpha / P.k P.L := by
  have hpPow : 0 < P.p ^ (P.m - 2) := pow_pos P.p_pos _
  have hxden : 0 < 1 + P.x := by
    have hx0 : 0 <= P.x := div_nonneg P.alpha_nonneg P.p_pos.le
    linarith
  have hyden : 0 < 1 + P.y := by linarith [P.y_nonneg]
  have hsubY := P.one_sub_y_pow_pos
  rw [le_div_iff₀ P.k_L_pos]
  rw [P.k_alpha_formula, P.k_L_formula]
  field_simp [hpPow.ne', hxden.ne', hyden.ne', hsubY.ne']
  have hyPow : 0 <= P.y ^ (P.m - 1) := pow_nonneg P.y_nonneg _
  have hsubX := P.one_sub_x_pow_pos
  nlinarith [mul_nonneg hsubX.le (add_nonneg P.y_nonneg hyPow)]

theorem A_div_B_lower :
    (1 - P.x ^ (P.m - 1)) / (1 + P.x) <= P.A / P.B :=
  P.normalized_k_ratio_lower.trans P.k_ratio_le_A_div_B

theorem x_pow_le_x_pow_fourteen (hm15 : 15 <= P.m) :
    P.x ^ (P.m - 1) <= P.x ^ 14 := by
  have hm14 : 14 <= P.m - 1 := by omega
  have hx0 : 0 <= P.x := div_nonneg P.alpha_nonneg P.p_pos.le
  exact pow_le_pow_of_le_one hx0 P.x_lt_one.le hm14

theorem rhoLo_pos : 0 < P.rhoLo := by
  unfold rhoLo
  have hx14 : P.x ^ 14 < 1 :=
    pow_lt_one₀ (div_nonneg P.alpha_nonneg P.p_pos.le) P.x_lt_one (by norm_num)
  exact div_pos (mul_pos (sub_pos.mpr hx14) (Real.sqrt_pos.2 P.alpha_pos))
    (mul_pos (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num))) P.f_pos)
      (by have hx0 : 0 <= P.x := div_nonneg P.alpha_nonneg P.p_pos.le; linarith))

/-- Explicit m-free lower bound used to choose the dual branch. -/
theorem rhoLo_le_rho (hm15 : 15 <= P.m) : P.rhoLo <= P.rho := by
  have hAB : (1 - P.x ^ 14) / (1 + P.x) <= P.A / P.B := by
    have hden : 0 < 1 + P.x := by
      have hx0 : 0 <= P.x := div_nonneg P.alpha_nonneg P.p_pos.le
      linarith
    have hfirst : (1 - P.x ^ 14) / (1 + P.x) <=
        (1 - P.x ^ (P.m - 1)) / (1 + P.x) :=
      (div_le_div_iff_of_pos_right hden).2 (by linarith [P.x_pow_le_x_pow_fourteen hm15])
    exact hfirst.trans P.A_div_B_lower
  have hscale : 0 < Real.sqrt P.alpha / (2 * Real.sqrt 2 * P.f) :=
    div_pos (Real.sqrt_pos.2 P.alpha_pos)
      (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num))) P.f_pos)
  have hlo : P.rhoLo =
      ((1 - P.x ^ 14) / (1 + P.x)) *
        (Real.sqrt P.alpha / (2 * Real.sqrt 2 * P.f)) := by
    unfold rhoLo
    have hxden : 1 + P.x ≠ 0 := by
      have hx0 : 0 <= P.x := div_nonneg P.alpha_nonneg P.p_pos.le
      linarith
    have hsqrtTwo : Real.sqrt (2 : Real) ≠ 0 :=
      (Real.sqrt_pos.2 (by norm_num)).ne'
    field_simp [hxden, hsqrtTwo, P.f_pos.ne']
  have hrho : P.rho =
      (P.A / P.B) * (Real.sqrt P.alpha / (2 * Real.sqrt 2 * P.f)) := by
    rfl
  rw [hlo, hrho]
  exact mul_le_mul_of_nonneg_right hAB hscale.le

/-- The first dual envelope value, using the explicit lower comparison
`rhoLo <= rho` but retaining the exact Envelope minimum on the right. -/
theorem psi_ge_rhoLo_branch (hm15 : 15 <= P.m)
    (hgate : 2 * P.rhoLo * P.xi <= 1) :
    P.rhoLo * P.xi ^ 2 * (1 + 4 * P.xi) / (1 + 2 * P.xi) <=
      psi P.xi P.rho := by
  let lambda : Real := 2 * P.rhoLo * P.xi
  have hlambda0 : 0 <= lambda := by
    dsimp [lambda]
    exact mul_nonneg (mul_nonneg (by norm_num) P.rhoLo_pos.le) P.xi_pos.le
  have hlambda1 : lambda <= 1 := by simpa [lambda] using hgate
  have hcert := envelopeDual_le_psi
    (xi := P.xi) (rho := P.rho) (lambda := lambda)
    P.rho_pos.le (by exact ⟨hlambda0, hlambda1⟩)
  have hdenLo : 0 < 4 * (P.rhoLo + lambda) := by
    have := P.rhoLo_pos
    positivity
  have hdenRho : 0 < 4 * (P.rho + lambda) := by
    have := P.rho_pos
    positivity
  have hfrac :
      lambda ^ 2 / (4 * (P.rho + lambda)) <=
        lambda ^ 2 / (4 * (P.rhoLo + lambda)) := by
    rw [div_le_div_iff₀ hdenRho hdenLo]
    exact mul_le_mul_of_nonneg_left
      (by nlinarith [P.rhoLo_le_rho hm15]) (sq_nonneg lambda)
  have hmono :
      envelopeDual P.xi P.rhoLo lambda <= envelopeDual P.xi P.rho lambda := by
    unfold envelopeDual
    linarith
  have hxiDen : 1 + 2 * P.xi ≠ 0 := by linarith [P.xi_pos]
  have hrhoLo : P.rhoLo ≠ 0 := P.rhoLo_pos.ne'
  have hvalue :
      envelopeDual P.xi P.rhoLo lambda =
        P.rhoLo * P.xi ^ 2 * (1 + 4 * P.xi) / (1 + 2 * P.xi) := by
    dsimp [lambda]
    unfold envelopeDual
    field_simp [hxiDen, hrhoLo]
    ring
  rw [← hvalue]
  exact hmono.trans hcert

/-- The linear dual envelope_value forced once the explicit lower comparison crosses
the Envelope transition gate. -/
theorem psi_ge_linear_rhoLo_branch (hm15 : 15 <= P.m)
    (hgate : 1 < 2 * P.rhoLo * P.xi) :
    P.xi * (4 * P.xi + 1) / (4 * P.xi + 2) <=
      psi P.xi P.rho := by
  have hcross : 2 < 4 * P.xi * P.rho := by
    have hlo := P.rhoLo_le_rho hm15
    have hxi := P.xi_pos
    nlinarith [mul_le_mul_of_nonneg_right hlo hxi.le]
  have hdenXi : 0 < 4 * P.xi + 2 := by linarith [P.xi_pos]
  have hdenRho : 0 < 4 * (P.rho + 1) := by linarith [P.rho_pos]
  have htarget :
      P.xi * (4 * P.xi + 1) / (4 * P.xi + 2) <=
        P.xi - 1 / (4 * (P.rho + 1)) := by
    have hfrac :
        1 / (4 * (P.rho + 1)) <= P.xi / (4 * P.xi + 2) := by
      rw [div_le_div_iff₀ hdenRho hdenXi]
      nlinarith
    have hrewrite :
        P.xi * (4 * P.xi + 1) / (4 * P.xi + 2) =
          P.xi - P.xi / (4 * P.xi + 2) := by
      apply (div_eq_iff hdenXi.ne').2
      rw [sub_mul, div_mul_cancel₀ _ hdenXi.ne']
      ring
    rw [hrewrite]
    linarith
  exact htarget.trans (psi_ge_dual_one P.rho_pos.le)

/-- The positive summand in `B` may be discarded, leaving its normalized
quotient-kernel contribution. -/
theorem B_lower :
    (P.m : Real) * P.p ^ (P.m - 2) *
        (1 - P.y ^ (P.m - 1)) / (1 + P.y) <= P.B := by
  rw [show (P.m : Real) * P.p ^ (P.m - 2) *
      (1 - P.y ^ (P.m - 1)) / (1 + P.y) =
      (P.m : Real) * P.k P.L by rw [P.k_L_formula]; ring]
  unfold B
  have hlead : 0 <= 2 * P.L ^ (P.m - 2) :=
    mul_nonneg (by norm_num) (pow_nonneg P.L_nonneg _)
  linarith

/-- Exact normalization used in the second envelope-value branch. -/
theorem C_mul_xi :
    P.C * P.xi = Real.sqrt (2 * P.alpha) * P.B * P.f * P.d := by
  unfold C xi
  have he : P.e ≠ 0 := P.e_pos.ne'
  have ha : P.alpha ≠ 0 := P.alpha_pos.ne'
  field_simp [he, ha]

/-- Exact normalization used in the first envelope-value branch. -/
theorem C_mul_rhoLo_mul_xi_sq :
    P.C * P.rhoLo * P.xi ^ 2 =
      2 * P.alpha ^ 3 * P.B * (1 - P.x ^ 14) * P.kappa ^ 2 /
        (1 + P.x) := by
  let ra := Real.sqrt P.alpha
  let rt := Real.sqrt 2
  have hraSq : ra ^ 2 = P.alpha := by
    dsimp [ra]
    exact Real.sq_sqrt P.alpha_nonneg
  have hrtPos : 0 < rt := by
    dsimp [rt]
    exact Real.sqrt_pos.2 (by norm_num)
  have hsEq : Real.sqrt (2 * P.alpha) = rt * ra := by
    dsimp [rt, ra]
    rw [Real.sqrt_mul (by norm_num : (0 : Real) <= 2)]
  have hroot :
      Real.sqrt (2 * P.alpha) * Real.sqrt P.alpha =
        Real.sqrt 2 * P.alpha := by
    rw [hsEq]
    change rt * ra * ra = rt * P.alpha
    calc
      rt * ra * ra = rt * ra ^ 2 := by ring
      _ = rt * P.alpha := by rw [hraSq]
  have he : P.e ≠ 0 := P.e_pos.ne'
  have ha : P.alpha ≠ 0 := P.alpha_pos.ne'
  have hf : P.f ≠ 0 := P.f_pos.ne'
  have hx : 1 + P.x ≠ 0 := by
    have hx0 : 0 <= P.x := div_nonneg P.alpha_nonneg P.p_pos.le
    linarith
  unfold C rhoLo xi kappa
  field_simp [he, ha, hf, hx, hrtPos.ne']
  ring_nf at hroot ⊢
  rw [hroot]

/-- The dimensionless envelope-value coefficient used by the first moderate
certificate branch. -/
def envelopeValueCoeffI : Real :=
  2 * (1 - P.x ^ 14) * (1 - P.y ^ (P.m - 1)) * P.kappa ^ 2 *
      (1 + 4 * P.xi) /
    ((1 + P.x) * (1 + P.y) * (1 + 2 * P.xi))

/-- The dimensionless envelope-value coefficient used by the linear moderate
certificate branch. -/
def envelopeValueCoeffII : Real :=
  Real.sqrt (2 * P.alpha) * (1 - P.y ^ (P.m - 1)) * P.f * P.d *
      (4 * P.xi + 1) /
    (P.alpha ^ 3 * (1 + P.y) * (4 * P.xi + 2))

theorem normalized_envelope_value_pos :
    0 < P.alpha ^ 3 * P.p ^ (P.m - 2) :=
  mul_pos (pow_pos P.alpha_pos _) (pow_pos P.p_pos _)

/-- First half of the manuscript's m-free-gated envelope_value estimate. -/
theorem envelopeValueCoeffI_le_normalized_psi (hm15 : 15 <= P.m)
    (hgate : 2 * P.rhoLo * P.xi <= 1) :
    (P.m : Real) * P.envelopeValueCoeffI <=
      P.C * psi P.xi P.rho / (P.alpha ^ 3 * P.p ^ (P.m - 2)) := by
  have hx14 : 0 <= 1 - P.x ^ 14 := by
    exact (sub_pos.mpr
      (pow_lt_one₀ (div_nonneg P.alpha_nonneg P.p_pos.le)
        P.x_lt_one (by norm_num))).le
  have hkappaSq : 0 <= P.kappa ^ 2 := sq_nonneg _
  have hxiNum : 0 <= 1 + 4 * P.xi := by linarith [P.xi_pos]
  have hxDen : 0 < 1 + P.x := by
    have hx0 : 0 <= P.x := div_nonneg P.alpha_nonneg P.p_pos.le
    linarith
  have hyDen : 0 < 1 + P.y := by linarith [P.y_nonneg]
  have hxiDen : 0 < 1 + 2 * P.xi := by linarith [P.xi_pos]
  let scale : Real :=
    2 * P.alpha ^ 3 * (1 - P.x ^ 14) * P.kappa ^ 2 *
      (1 + 4 * P.xi) / ((1 + P.x) * (1 + 2 * P.xi))
  have hscale : 0 <= scale := by
    dsimp [scale]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num)
              (pow_nonneg P.alpha_nonneg 3))
            hx14)
          hkappaSq)
        hxiNum)
      (mul_nonneg hxDen.le hxiDen.le)
  have hB := mul_le_mul_of_nonneg_right P.B_lower hscale
  have hpsi := mul_le_mul_of_nonneg_left
    (P.psi_ge_rhoLo_branch hm15 hgate) P.C_pos.le
  apply (le_div_iff₀ P.normalized_envelope_value_pos).2
  calc
    (P.m : Real) * P.envelopeValueCoeffI *
        (P.alpha ^ 3 * P.p ^ (P.m - 2)) =
        ((P.m : Real) * P.p ^ (P.m - 2) *
          (1 - P.y ^ (P.m - 1)) / (1 + P.y)) * scale := by
      unfold envelopeValueCoeffI
      dsimp [scale]
      field_simp [hxDen.ne', hyDen.ne', hxiDen.ne']
    _ <= P.B * scale := hB
    _ = P.C * (P.rhoLo * P.xi ^ 2 *
        (1 + 4 * P.xi) / (1 + 2 * P.xi)) := by
      rw [show P.C * (P.rhoLo * P.xi ^ 2 *
          (1 + 4 * P.xi) / (1 + 2 * P.xi)) =
          (P.C * P.rhoLo * P.xi ^ 2) *
            ((1 + 4 * P.xi) / (1 + 2 * P.xi)) by ring]
      rw [P.C_mul_rhoLo_mul_xi_sq]
      dsimp [scale]
      field_simp [hxDen.ne', hxiDen.ne']
    _ <= P.C * psi P.xi P.rho := hpsi

/-- Second half of the manuscript's m-free-gated envelope_value estimate. -/
theorem envelopeValueCoeffII_le_normalized_psi (hm15 : 15 <= P.m)
    (hgate : 1 < 2 * P.rhoLo * P.xi) :
    (P.m : Real) * P.envelopeValueCoeffII <=
      P.C * psi P.xi P.rho / (P.alpha ^ 3 * P.p ^ (P.m - 2)) := by
  have hyDen : 0 < 1 + P.y := by linarith [P.y_nonneg]
  have hxiDen : 0 < 4 * P.xi + 2 := by linarith [P.xi_pos]
  let scale : Real :=
    Real.sqrt (2 * P.alpha) * P.f * P.d *
      (4 * P.xi + 1) / (4 * P.xi + 2)
  have hd : 0 < P.d := by unfold d; linarith [P.alpha_gt_q]
  have hscale : 0 <= scale := by
    dsimp [scale]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (Real.sqrt_nonneg _) P.f_pos.le)
          hd.le)
        (by linarith [P.xi_pos]))
      hxiDen.le
  have hB := mul_le_mul_of_nonneg_right P.B_lower hscale
  have hpsi := mul_le_mul_of_nonneg_left
    (P.psi_ge_linear_rhoLo_branch hm15 hgate) P.C_pos.le
  apply (le_div_iff₀ P.normalized_envelope_value_pos).2
  calc
    (P.m : Real) * P.envelopeValueCoeffII *
        (P.alpha ^ 3 * P.p ^ (P.m - 2)) =
        ((P.m : Real) * P.p ^ (P.m - 2) *
          (1 - P.y ^ (P.m - 1)) / (1 + P.y)) * scale := by
      unfold envelopeValueCoeffII
      dsimp [scale]
      field_simp [P.alpha_pos.ne', hyDen.ne', hxiDen.ne']
    _ <= P.B * scale := hB
    _ = P.C * (P.xi * (4 * P.xi + 1) / (4 * P.xi + 2)) := by
      rw [show P.C * (P.xi * (4 * P.xi + 1) / (4 * P.xi + 2)) =
          (P.C * P.xi) * ((4 * P.xi + 1) / (4 * P.xi + 2)) by ring]
      rw [P.C_mul_xi]
      dsimp [scale]
      field_simp [hxiDen.ne']
    _ <= P.C * psi P.xi P.rho := hpsi

end AdmissibleParams
end OddCycleBound.IntermediateRegion.Scalar
