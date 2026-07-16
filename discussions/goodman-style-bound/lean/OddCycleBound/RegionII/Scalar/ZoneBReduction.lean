import OddCycleBound.RegionII.Scalar.ZoneBMax

/-!
# Zone-B payment and defect reduction

This module connects the verified two-variable battle to the manuscript's
actual cycle-length quantities.  The definitions below are the left side,
tail, and linear Huber payment in equations (reducedB) and (cert-II).
-/

noncomputable section

namespace OddCycleBound.RegionII.Scalar

open OddCycleBound.RegionII.Certificate

namespace AdmissibleParams

variable (P : AdmissibleParams)

def epsII : Real :=
  P.e / (4 * (1 - P.e) ^ 2 * (1 + P.rho) * P.kappa)

def piII : Real :=
  Real.sqrt (1 - P.e) * (1 - P.ell) *
    (1 - P.y ^ (P.m - 1)) * (1 - P.epsII) / (1 + P.y)

def lambdaII : Real :=
  Real.sqrt (P.alpha * P.e) ^ P.m /
    ((P.m : Real) * P.d * P.alpha * P.p ^ (P.m - 2))

def reducedBracketII : Real :=
  P.x ^ (P.m - 2) *
    (((P.m - 1 : Nat) : Real) / ((P.m : Real) * P.x) -
      (1 + 1 / P.kappa) / (P.m : Real))

def linearPaymentII : Real :=
  Real.sqrt (2 * P.alpha) * P.B * P.f *
    (P.d - P.e ^ 2 / (16 * P.alpha ^ 2 * (1 + P.rho)))

def normalizationII : Real :=
  (P.m : Real) * P.d * P.alpha * P.p ^ (P.m - 2)

def defectUpperII : Real :=
  P.alpha ^ (P.m - 1) *
      (((P.m - 1 : Nat) : Real) * P.d / P.x - (P.d + P.e)) +
    Real.sqrt (P.alpha * P.e) ^ P.m

lemma e_lt_alpha : P.e < P.alpha := by
  unfold e
  linarith [P.alpha_gt_q, P.q_gt_third]

lemma sqrt_alpha_mul_e :
    Real.sqrt (P.alpha * P.e) =
      P.alpha * Real.sqrt (P.e / P.alpha) := by
  have hae : 0 <= P.alpha * P.e :=
    mul_nonneg P.alpha_pos.le P.e_pos.le
  have hz : 0 <= P.e / P.alpha :=
    div_nonneg P.e_pos.le P.alpha_pos.le
  have hs1 := Real.sq_sqrt hae
  have hright : 0 <= P.alpha * Real.sqrt (P.e / P.alpha) :=
    mul_nonneg P.alpha_pos.le (Real.sqrt_nonneg _)
  have ha : P.alpha ≠ 0 := P.alpha_pos.ne'
  have hs2 : (P.alpha * Real.sqrt (P.e / P.alpha)) ^ 2 =
      P.alpha * P.e := by
    rw [mul_pow, Real.sq_sqrt hz]
    field_simp [ha]
  nlinarith [Real.sqrt_nonneg (P.alpha * P.e)]

lemma lambdaII_normalized :
    P.lambdaII =
      P.x ^ (P.m - 2) *
        (P.e / P.alpha) ^ (P.m / 2 - 1) *
        Real.sqrt (P.e / P.alpha) /
        ((P.m : Real) * P.kappa) := by
  let r := P.m / 2
  let z := P.e / P.alpha
  let t := Real.sqrt z
  have hm : 2 * r + 1 = P.m := by
    simpa [r] using Nat.two_mul_div_two_add_one_of_odd P.m_odd
  have hr : 1 <= r := by
    have hm15 := P.m_ge_fifteen
    omega
  have hm2 : P.m - 2 + 2 = P.m := by omega
  have hr1 : r - 1 + 1 = r := by omega
  have hz : 0 <= z := by
    dsimp [z]
    exact div_nonneg P.e_pos.le P.alpha_pos.le
  have ht_sq : t ^ 2 = z := by
    dsimp [t]
    exact Real.sq_sqrt hz
  have ht_pow : t ^ P.m = z ^ r * t := by
    rw [← hm]
    simp [pow_add, pow_mul, ht_sq]
  have ha_pow : P.alpha ^ P.m =
      P.alpha ^ (P.m - 2) * P.alpha ^ 2 := by
    rw [← pow_add, hm2]
  have hz_pow : z ^ r = z ^ (r - 1) * z := by
    calc
      z ^ r = z ^ (r - 1 + 1) := congrArg (z ^ ·) hr1.symm
      _ = z ^ (r - 1) * z := pow_succ _ _
  have hd : P.d = P.kappa * P.e := by
    rw [P.kappa_mul_e]
  have he : P.e = P.alpha * z := by
    dsimp [z]
    field_simp [P.alpha_pos.ne']
  have hm0 : (P.m : Real) ≠ 0 := by
    exact_mod_cast (show P.m ≠ 0 by omega)
  have hk : P.kappa ≠ 0 := P.kappa_pos.ne'
  have ha : P.alpha ≠ 0 := P.alpha_pos.ne'
  have hp : P.p ≠ 0 := P.p_pos.ne'
  have hz0 : z ≠ 0 := by
    dsimp [z]
    exact div_ne_zero P.e_pos.ne' ha
  have hpowcancel :
      P.p ^ (P.m - 2) * (P.alpha / P.p) ^ (P.m - 2) =
        P.alpha ^ (P.m - 2) := by
    rw [← mul_pow]
    field_simp [hp]
  rw [lambdaII, P.sqrt_alpha_mul_e]
  change (P.alpha * t) ^ P.m /
      ((P.m : Real) * P.d * P.alpha * P.p ^ (P.m - 2)) =
    (P.alpha / P.p) ^ (P.m - 2) * z ^ (r - 1) * t /
      ((P.m : Real) * P.kappa)
  rw [mul_pow, ht_pow, ha_pow, hz_pow, hd, he]
  rw [div_pow]
  field_simp [hm0, hk, ha, hp, hz0]
  calc
    P.alpha ^ (P.m - 2) * P.e ^ (r - 1) * t =
        P.e ^ (r - 1) * t * P.alpha ^ (P.m - 2) := by ring
    _ = P.e ^ (r - 1) * t *
        (P.p ^ (P.m - 2) * (P.alpha / P.p) ^ (P.m - 2)) := by
      rw [hpowcancel]
    _ = P.e ^ (r - 1) * t * P.p ^ (P.m - 2) *
        (P.alpha / P.p) ^ (P.m - 2) := by ring

lemma x_pos : 0 < P.x := div_pos P.alpha_pos P.p_pos

lemma one_sub_e_pos : 0 < 1 - P.e := by
  rw [show 1 - P.e = 2 * P.alpha by unfold e; ring]
  exact mul_pos (by norm_num) P.alpha_pos

lemma one_add_y_pos : 0 < 1 + P.y := by linarith [P.y_nonneg]

lemma one_add_rho_pos : 0 < 1 + P.rho := by linarith [P.rho_pos]

lemma one_sub_e_eq_two_alpha : 1 - P.e = 2 * P.alpha := by
  unfold e
  ring

lemma sqrt_one_sub_e : Real.sqrt (1 - P.e) = Real.sqrt (2 * P.alpha) := by
  rw [P.one_sub_e_eq_two_alpha]

lemma f_eq_alpha_mul_one_sub_ell :
    P.f = P.alpha * (1 - P.ell) := by
  unfold f ell
  field_simp [P.alpha_pos.ne']

lemma reducedBracketII_eq_K :
    P.reducedBracketII = bKAt P (P.m - 1) / P.x ^ 2 := by
  have hx : P.x ≠ 0 := P.x_pos.ne'
  have hmge := P.m_ge_fifteen
  have hm0 : (P.m : Real) ≠ 0 := by
    have hm : 0 < P.m := by omega
    exact_mod_cast hm.ne'
  have hm1 : P.m - 1 + 1 = P.m := by omega
  have hm1R : ((P.m - 1 : Nat) : Real) + 1 = (P.m : Real) := by
    exact_mod_cast hm1
  have hm2 : P.m - 1 = (P.m - 2) + 1 := by omega
  unfold reducedBracketII bKAt bAReal
  rw [hm1R, hm2, pow_succ]
  push_cast
  field_simp [hx, P.kappa_pos.ne', hm0]
  ring

lemma epsII_eq_defect_fraction :
    P.epsII = P.e ^ 2 /
      (16 * P.alpha ^ 2 * (1 + P.rho) * P.d) := by
  have he : P.e ≠ 0 := P.e_pos.ne'
  have ha : P.alpha ≠ 0 := P.alpha_pos.ne'
  have hd : P.d ≠ 0 := P.d_pos.ne'
  have hrho : 1 + P.rho ≠ 0 := P.one_add_rho_pos.ne'
  have hk : P.kappa ≠ 0 := P.kappa_pos.ne'
  unfold epsII
  rw [P.one_sub_e_eq_two_alpha]
  have hke : P.kappa * P.e = P.d := P.kappa_mul_e
  field_simp [he, ha, hd, hrho, hk]
  nlinarith

lemma d_mul_one_sub_epsII :
    P.d * (1 - P.epsII) =
      P.d - P.e ^ 2 / (16 * P.alpha ^ 2 * (1 + P.rho)) := by
  rw [P.epsII_eq_defect_fraction]
  have hd : P.d ≠ 0 := P.d_pos.ne'
  have ha : P.alpha ≠ 0 := P.alpha_pos.ne'
  have hrho : 1 + P.rho ≠ 0 := P.one_add_rho_pos.ne'
  field_simp [hd, ha, hrho]

lemma linearPaymentII_eq_C_dual :
    P.linearPaymentII =
      P.C * (P.xi - 1 / (4 * (P.rho + 1))) := by
  have ha : P.alpha ≠ 0 := P.alpha_pos.ne'
  have hrho : P.rho + 1 ≠ 0 := by linarith [P.rho_pos]
  have hrho' : 1 + P.rho ≠ 0 := by linarith [P.rho_pos]
  unfold linearPaymentII
  rw [show P.C * (P.xi - 1 / (4 * (P.rho + 1))) =
      P.C * P.xi - P.C * (1 / (4 * (P.rho + 1))) by ring,
    P.C_mul_xi]
  unfold C
  field_simp [ha, hrho, hrho']
  ring

theorem linearPaymentII_le_C_psi :
    P.linearPaymentII <= P.C * psi P.xi P.rho := by
  rw [P.linearPaymentII_eq_C_dual]
  exact mul_le_mul_of_nonneg_left (psi_ge_dual_one P.rho_pos.le) P.C_pos.le

lemma L_sq_le_alpha_mul_e : P.L ^ 2 <= P.alpha * P.e := by
  rw [P.L_sq_chart]
  have hprod : 0 <= P.d * (P.d + P.e) :=
    mul_nonneg P.d_pos.le (add_nonneg P.d_pos.le P.e_pos.le)
  linarith

lemma ell_sq_le_chart : P.ell ^ 2 <= 2 * P.e / (1 - P.e) := by
  have ha2 : 0 < P.alpha ^ 2 := sq_pos_of_pos P.alpha_pos
  have hbase : P.ell ^ 2 <= P.e / P.alpha := by
    unfold ell
    rw [div_pow, div_le_iff₀ ha2]
    have h := P.L_sq_le_alpha_mul_e
    field_simp [P.alpha_pos.ne']
    nlinarith
  rw [P.one_sub_e_eq_two_alpha]
  have ha : P.alpha ≠ 0 := P.alpha_pos.ne'
  field_simp [ha] at hbase ⊢
  linarith

lemma ell_le_bEllBar : P.ell <= bEllBar P.e := by
  have hr : 0 <= 2 * P.e / (1 - P.e) :=
    div_nonneg (mul_nonneg (by norm_num) P.e_pos.le) P.one_sub_e_pos.le
  unfold bEllBar
  exact (Real.le_sqrt P.ell_nonneg hr).2 P.ell_sq_le_chart

lemma y_le_ell : P.y <= P.ell := by
  unfold y ell
  rw [div_le_div_iff₀ P.p_pos P.alpha_pos]
  exact mul_le_mul_of_nonneg_left P.alpha_lt_p.le P.L_nonneg

lemma y_le_bEllBar : P.y <= bEllBar P.e := P.y_le_ell.trans P.ell_le_bEllBar

lemma bEllBar_nonneg : 0 <= bEllBar P.e := by
  unfold bEllBar
  exact Real.sqrt_nonneg _

lemma bEllBar_lt_one : bEllBar P.e < 1 := by
  have hratio : 2 * P.e / (1 - P.e) < 1 := by
    rw [div_lt_one P.one_sub_e_pos]
    linarith [P.e_lt_third]
  unfold bEllBar
  exact (Real.sqrt_lt' (by norm_num : (0 : Real) < 1)).2 (by simpa using hratio)

lemma y_pow_le_bEllBar_pow_fourteen :
    P.y ^ (P.m - 1) <= bEllBar P.e ^ 14 := by
  have hm := P.m_ge_fifteen
  have hm14 : 14 <= P.m - 1 := by omega
  calc
    P.y ^ (P.m - 1) <= P.y ^ 14 :=
      pow_le_pow_of_le_one P.y_nonneg
        (P.y_lt_s.trans P.s_lt_x |>.trans P.x_lt_one).le hm14
    _ <= bEllBar P.e ^ 14 :=
      pow_le_pow_left₀ P.y_nonneg P.y_le_bEllBar 14

lemma bRhoUnder_nonneg : 0 <= bRhoUnder P.e P.kappa := by
  unfold bRhoUnder
  have ht : 0 <= (1737 / 100 : Real) * (1 + P.kappa) * P.e := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (by linarith [P.kappa_pos])) P.e_pos.le
  have hexp : Real.exp (-(1737 / 100 : Real) * (1 + P.kappa) * P.e) <= 1 :=
    (Real.exp_le_one_iff.mpr (by linarith))
  exact div_nonneg (sub_nonneg.mpr hexp) (by norm_num)

lemma epsII_le_quarter (hxi : 1 <= P.xi) : P.epsII <= 1 / 4 := by
  have hchart := P.xi_chart
  have hnum : P.e <= (1 - P.e) ^ 2 * P.kappa := by
    have he := P.e_pos
    rw [hchart] at hxi
    rw [le_div_iff₀ he] at hxi
    nlinarith
  have hden0 : 0 < 4 * (1 - P.e) ^ 2 * (1 + P.rho) * P.kappa := by
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos P.one_sub_e_pos))
        P.one_add_rho_pos) P.kappa_pos
  unfold epsII
  rw [div_le_iff₀ hden0]
  have hrho : 1 <= 1 + P.rho := by linarith [P.rho_pos]
  nlinarith [mul_le_mul_of_nonneg_left hrho
    (mul_nonneg (sq_nonneg (1 - P.e)) P.kappa_pos.le)]

lemma epsII_le_bEpsBar (hxi : 1 <= P.xi)
    (hrho : bRhoUnder P.e P.kappa <= P.rho) :
    P.epsII <= bEpsBar P.e P.kappa (bRhoUnder P.e P.kappa) := by
  have hrawDen : 0 <
      4 * (1 - P.e) ^ 2 * P.kappa *
        (1 + bRhoUnder P.e P.kappa) := by
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos P.one_sub_e_pos))
        P.kappa_pos) (by linarith [P.bRhoUnder_nonneg])
  have hactDen : 0 <
      4 * (1 - P.e) ^ 2 * P.kappa * (1 + P.rho) := by
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos P.one_sub_e_pos))
        P.kappa_pos) P.one_add_rho_pos
  have hraw : P.epsII <=
      P.e / (4 * (1 - P.e) ^ 2 * P.kappa *
        (1 + bRhoUnder P.e P.kappa)) := by
    unfold epsII
    rw [show 4 * (1 - P.e) ^ 2 * (1 + P.rho) * P.kappa =
      4 * (1 - P.e) ^ 2 * P.kappa * (1 + P.rho) by ring]
    rw [div_le_div_iff₀ hactDen hrawDen]
    have hfac : 0 <= 4 * (1 - P.e) ^ 2 * P.kappa :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) P.kappa_pos.le
    have hdenle :
        4 * (1 - P.e) ^ 2 * P.kappa *
            (1 + bRhoUnder P.e P.kappa) <=
          4 * (1 - P.e) ^ 2 * P.kappa * (1 + P.rho) :=
      mul_le_mul_of_nonneg_left (by linarith) hfac
    exact mul_le_mul_of_nonneg_left hdenle P.e_pos.le
  unfold bEpsBar
  exact le_min (P.epsII_le_quarter hxi) hraw

lemma sqrt_two_mul_alpha_le_sqrt_alpha :
    Real.sqrt 2 * P.alpha <= Real.sqrt P.alpha := by
  have hs2 : Real.sqrt (2 : Real) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsa : Real.sqrt P.alpha ^ 2 = P.alpha := Real.sq_sqrt P.alpha_nonneg
  have hleft : 0 <= Real.sqrt 2 * P.alpha :=
    mul_nonneg (Real.sqrt_nonneg _) P.alpha_nonneg
  have hsq : (Real.sqrt 2 * P.alpha) ^ 2 <= (Real.sqrt P.alpha) ^ 2 := by
    rw [hsa]
    nlinarith [hs2, mul_nonneg P.alpha_nonneg
      (by linarith [P.alpha_lt_half] : 0 <= 1 - 2 * P.alpha)]
  nlinarith [Real.sqrt_nonneg P.alpha]

lemma quarter_le_rho_scale :
    (1 / 4 : Real) <=
      Real.sqrt P.alpha / (2 * Real.sqrt 2 * P.f * (1 + P.x)) := by
  have hs2 : 0 < Real.sqrt (2 : Real) := Real.sqrt_pos.2 (by norm_num)
  have hf_le : P.f <= P.alpha := by unfold f; linarith [P.L_nonneg]
  have hx1 : 1 + P.x <= 2 := by linarith [P.x_lt_one]
  have hprod : P.f * (1 + P.x) <= P.alpha * 2 :=
    mul_le_mul hf_le hx1 (by linarith [P.x_pos]) P.alpha_nonneg
  have hden : 0 < 2 * Real.sqrt 2 * P.f * (1 + P.x) := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) hs2) P.f_pos)
      (by linarith [P.x_pos])
  rw [le_div_iff₀ hden]
  have hscaled :
      2 * Real.sqrt 2 * (P.f * (1 + P.x)) <=
        2 * Real.sqrt 2 * (P.alpha * 2) :=
    mul_le_mul_of_nonneg_left hprod
      (mul_nonneg (by norm_num) hs2.le)
  calc
    (1 / 4 : Real) * (2 * Real.sqrt 2 * P.f * (1 + P.x)) <=
        (1 / 4 : Real) * (2 * Real.sqrt 2 * (P.alpha * 2)) := by
      exact mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using hscaled) (by norm_num)
    _ = Real.sqrt 2 * P.alpha := by ring
    _ <= Real.sqrt P.alpha := P.sqrt_two_mul_alpha_le_sqrt_alpha

lemma quarter_one_sub_x14_le_rhoLo :
    (1 - P.x ^ 14) / 4 <= P.rhoLo := by
  have hxsub : 0 <= 1 - P.x ^ 14 := by
    exact sub_nonneg.mpr (pow_le_one₀ P.x_pos.le P.x_lt_one.le)
  unfold rhoLo
  rw [show (1 - P.x ^ 14) * Real.sqrt P.alpha /
      (2 * Real.sqrt 2 * P.f * (1 + P.x)) =
      (1 - P.x ^ 14) *
        (Real.sqrt P.alpha / (2 * Real.sqrt 2 * P.f * (1 + P.x))) by ring,
    show (1 - P.x ^ 14) / 4 = (1 - P.x ^ 14) * (1 / 4) by ring]
  exact mul_le_mul_of_nonneg_left P.quarter_le_rho_scale hxsub

lemma one_sub_x_chart :
    1 - P.x = 2 * (1 + P.kappa) * P.e /
      (1 + P.e + 2 * P.kappa * P.e) := by
  rw [P.x_eq_chartXR]
  unfold chartXR
  have hden := chartXR_den_pos P.e_pos.le P.kappa_pos.le
  have hdenEq : 1 + P.e + 2 * P.kappa * P.e =
      1 + P.e + P.e * P.kappa * 2 := by ring
  have hden' : 1 + P.e + P.e * P.kappa * 2 ≠ 0 := by
    rw [← hdenEq]
    exact hden.ne'
  rw [hdenEq, eq_div_iff hden']
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hden']
  ring

lemma rho_exponent_le_fourteen_u (heHi : P.e <= 2033 / 10000) :
    (1737 / 100 : Real) * (1 + P.kappa) * P.e <= 14 * (1 - P.x) := by
  have hk1 : P.kappa <= 1 :=
    P.kappa_le_max.trans (by
      unfold kappaMax
      rw [div_le_one (by linarith [P.e_pos] : 0 < 1 + P.e)]
      linarith [P.e_pos])
  have hke : P.kappa * P.e <= P.e :=
    by simpa using mul_le_mul_of_nonneg_right hk1 P.e_pos.le
  have hD : 1 + P.e + 2 * P.kappa * P.e <= 1 + 3 * P.e := by linarith
  have hcoef : (1737 / 100 : Real) *
      (1 + P.e + 2 * P.kappa * P.e) <= 28 := by
    calc
      (1737 / 100 : Real) * (1 + P.e + 2 * P.kappa * P.e) <=
          (1737 / 100 : Real) * (1 + 3 * P.e) :=
        mul_le_mul_of_nonneg_left hD (by norm_num)
      _ <= 28 := by nlinarith
  have hden : 0 < 1 + P.e + 2 * P.kappa * P.e :=
    chartXR_den_pos P.e_pos.le P.kappa_pos.le
  rw [P.one_sub_x_chart]
  rw [show 14 * (2 * (1 + P.kappa) * P.e /
      (1 + P.e + 2 * P.kappa * P.e)) =
      (14 * (2 * (1 + P.kappa) * P.e)) /
        (1 + P.e + 2 * P.kappa * P.e) by ring]
  rw [le_div_iff₀ hden]
  have hfac : 0 <= (1 + P.kappa) * P.e :=
    mul_nonneg (by linarith [P.kappa_pos]) P.e_pos.le
  have hmul := mul_le_mul_of_nonneg_right hcoef hfac
  nlinarith

lemma bRhoUnder_le_rho (heHi : P.e <= 2033 / 10000) :
    bRhoUnder P.e P.kappa <= P.rho := by
  have harg : (1737 / 100 : Real) * (1 + P.kappa) * P.e <=
      14 * bLambdaReal P :=
    (P.rho_exponent_le_fourteen_u heHi).trans
      (mul_le_mul_of_nonneg_left (one_sub_x_le_lambda P) (by norm_num))
  have hxpow : P.x ^ 14 <=
      Real.exp (-(1737 / 100 : Real) * (1 + P.kappa) * P.e) := by
    rw [x_pow_eq_exp_neg_lambda_mul]
    exact Real.exp_le_exp.mpr (by linarith)
  have hquarter : bRhoUnder P.e P.kappa <= (1 - P.x ^ 14) / 4 := by
    unfold bRhoUnder
    linarith
  exact hquarter.trans P.quarter_one_sub_x14_le_rhoLo |>.trans P.rhoLo_le_rho

lemma bEpsBar_nonneg :
    0 <= bEpsBar P.e P.kappa (bRhoUnder P.e P.kappa) := by
  unfold bEpsBar
  apply le_min
  · norm_num
  · have hden : 0 <= 4 * (1 - P.e) ^ 2 * P.kappa *
        (1 + bRhoUnder P.e P.kappa) := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) P.kappa_pos.le)
        (by linarith [P.bRhoUnder_nonneg])
    exact div_nonneg P.e_pos.le hden

lemma bEpsBar_le_quarter :
    bEpsBar P.e P.kappa (bRhoUnder P.e P.kappa) <= 1 / 4 := by
  unfold bEpsBar
  exact min_le_left _ _

theorem bPiUnder_le_piII (hxi : 1 <= P.xi)
    (heHi : P.e <= 2033 / 10000) :
    bPiUnder P.e P.kappa <= P.piII := by
  let l := bEllBar P.e
  let eps := bEpsBar P.e P.kappa (bRhoUnder P.e P.kappa)
  have hl0 : 0 <= l := by simpa [l] using P.bEllBar_nonneg
  have hl1 : l < 1 := by simpa [l] using P.bEllBar_lt_one
  have hell : P.ell <= l := by simpa [l] using P.ell_le_bEllBar
  have hy : P.y <= l := by simpa [l] using P.y_le_bEllBar
  have hypow : P.y ^ (P.m - 1) <= l ^ 14 := by
    simpa [l] using P.y_pow_le_bEllBar_pow_fourteen
  have heps0 : 0 <= eps := by simpa [eps] using P.bEpsBar_nonneg
  have heps1 : eps <= 1 / 4 := by simpa [eps] using P.bEpsBar_le_quarter
  have heps : P.epsII <= eps := by
    simpa [eps] using P.epsII_le_bEpsBar hxi (P.bRhoUnder_le_rho heHi)
  have hsqrt0 : 0 <= Real.sqrt (1 - P.e) := Real.sqrt_nonneg _
  have hUl : 0 <= 1 - l := by linarith
  have hU14 : 0 <= 1 - l ^ 14 :=
    sub_nonneg.mpr (pow_le_one₀ hl0 hl1.le)
  have hUeps : 0 <= 1 - eps := by linarith
  have hAell : 0 <= 1 - P.ell := by linarith
  have hAy : 0 <= 1 - P.y ^ (P.m - 1) := P.one_sub_y_pow_pos.le
  have hAeps : 0 <= 1 - P.epsII := by linarith
  let numU := Real.sqrt (1 - P.e) * (1 - l) * (1 - l ^ 14) * (1 - eps)
  let numA := Real.sqrt (1 - P.e) * (1 - P.ell) *
    (1 - P.y ^ (P.m - 1)) * (1 - P.epsII)
  have hnum : numU <= numA := by
    dsimp [numU, numA]
    exact mul_le_mul
      (mul_le_mul
        (mul_le_mul (le_refl _) (by linarith) hUl hsqrt0)
        (by linarith) hU14
        (mul_nonneg hsqrt0 hAell))
      (by linarith) hUeps
      (mul_nonneg (mul_nonneg hsqrt0 hAell) hAy)
  have hnumU0 : 0 <= numU := by
    dsimp [numU]
    positivity
  have hnumA0 : 0 <= numA := hnumU0.trans hnum
  have hdenA : 0 < 1 + P.y := P.one_add_y_pos
  have hden : 1 + P.y <= 1 + l := by linarith
  rw [bPiUnder]
  change numU / (1 + l) <= P.piII
  unfold piII
  change numU / (1 + l) <= numA / (1 + P.y)
  calc
    numU / (1 + l) <= numA / (1 + l) :=
      div_le_div_of_nonneg_right hnum (by linarith)
    _ <= numA / (1 + P.y) :=
      div_le_div_of_nonneg_left hnumA0 hdenA hden

lemma lambdaII_le_bLambdaBar (hxi : 1 <= P.xi) :
    P.lambdaII <= bLambdaBar P := by
  let r := P.m / 2
  let z := P.e / P.alpha
  let t := Real.sqrt z
  have hm : 2 * r + 1 = P.m := by
    simpa [r] using Nat.two_mul_div_two_add_one_of_odd P.m_odd
  have hm15 := P.m_ge_fifteen
  have hr7 : 7 <= r := by omega
  have hm13 : 13 <= P.m - 2 := by omega
  have hr6 : 6 <= r - 1 := by omega
  have hx0 : 0 <= P.x := P.x_pos.le
  have hx1 : P.x <= 1 := P.x_lt_one.le
  have hz0 : 0 <= z := by
    dsimp [z]
    exact div_nonneg P.e_pos.le P.alpha_pos.le
  have hz1 : z <= 1 := by
    dsimp [z]
    exact (div_le_one P.alpha_pos).2 P.e_lt_alpha.le
  have ht0 : 0 <= t := Real.sqrt_nonneg _
  have hxpow : P.x ^ (P.m - 2) <= P.x ^ 13 :=
    pow_le_pow_of_le_one hx0 hx1 hm13
  have hzpow : z ^ (r - 1) <= z ^ 6 :=
    pow_le_pow_of_le_one hz0 hz1 hr6
  have hnum : P.x ^ (P.m - 2) * z ^ (r - 1) * t <=
      P.x ^ 13 * z ^ 6 * t := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hxpow hzpow (pow_nonneg hz0 _) (pow_nonneg hx0 _)) ht0
  have hnumBar0 : 0 <= P.x ^ 13 * z ^ 6 * t := by positivity
  have hchart := P.xi_chart
  have hkbase : P.e <= (1 - P.e) ^ 2 * P.kappa := by
    rw [hchart] at hxi
    rw [le_div_iff₀ P.e_pos] at hxi
    nlinarith
  have hmR : (15 : Real) <= P.m := by exact_mod_cast hm15
  have hscale0 : 0 <= (1 - P.e) ^ 2 * P.kappa :=
    mul_nonneg (sq_nonneg _) P.kappa_pos.le
  have hmk : 15 * P.e <=
      ((P.m : Real) * P.kappa) * (1 - P.e) ^ 2 := by
    calc
      15 * P.e <= 15 * ((1 - P.e) ^ 2 * P.kappa) :=
        mul_le_mul_of_nonneg_left hkbase (by norm_num)
      _ <= (P.m : Real) * ((1 - P.e) ^ 2 * P.kappa) :=
        mul_le_mul_of_nonneg_right hmR hscale0
      _ = ((P.m : Real) * P.kappa) * (1 - P.e) ^ 2 := by ring
  have hmpos : (0 : Real) < P.m := by
    exact_mod_cast (show 0 < P.m by omega)
  have hmkpos : 0 < (P.m : Real) * P.kappa :=
    mul_pos hmpos P.kappa_pos
  have h15e : 0 < (15 : Real) * P.e := mul_pos (by norm_num) P.e_pos
  have hrecip : 1 / ((P.m : Real) * P.kappa) <=
      (1 - P.e) ^ 2 / (15 * P.e) := by
    rw [div_le_div_iff₀ hmkpos h15e]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmk
  have hzchart : 2 * P.e / (1 - P.e) = z := by
    rw [P.one_sub_e_eq_two_alpha]
    dsimp [z]
    field_simp [P.alpha_pos.ne']
  rw [P.lambdaII_normalized]
  change P.x ^ (P.m - 2) * z ^ (r - 1) * t /
      ((P.m : Real) * P.kappa) <= bLambdaBar P
  calc
    P.x ^ (P.m - 2) * z ^ (r - 1) * t /
        ((P.m : Real) * P.kappa) <=
        (P.x ^ 13 * z ^ 6 * t) /
          ((P.m : Real) * P.kappa) :=
      div_le_div_of_nonneg_right hnum hmkpos.le
    _ = (P.x ^ 13 * z ^ 6 * t) *
        (1 / ((P.m : Real) * P.kappa)) := by ring
    _ <= (P.x ^ 13 * z ^ 6 * t) *
        ((1 - P.e) ^ 2 / (15 * P.e)) :=
      mul_le_mul_of_nonneg_left hrecip hnumBar0
    _ = bLambdaBar P := by
      unfold bLambdaBar bEllBar
      rw [hzchart]
      dsimp [t]
      ring

lemma normalizationII_pos : 0 < P.normalizationII := by
  unfold normalizationII
  have hmpos : (0 : Real) < P.m := by
    have hm15 := P.m_ge_fifteen
    exact_mod_cast (show 0 < P.m by omega)
  exact mul_pos
    (mul_pos (mul_pos hmpos P.d_pos) P.alpha_pos)
    (pow_pos P.p_pos _)

lemma normalizationII_mul_lambdaII :
    P.normalizationII * P.lambdaII =
      Real.sqrt (P.alpha * P.e) ^ P.m := by
  unfold normalizationII lambdaII
  have hden :
      (P.m : Real) * P.d * P.alpha * P.p ^ (P.m - 2) ≠ 0 :=
    P.normalizationII_pos.ne'
  exact mul_div_cancel₀ _ hden

lemma normalizationII_mul_reducedBracketII :
    P.normalizationII * P.reducedBracketII =
      P.alpha ^ (P.m - 1) *
        (((P.m - 1 : Nat) : Real) * P.d / P.x - (P.d + P.e)) := by
  have hm15 := P.m_ge_fifteen
  have hm2 : P.m - 2 + 1 = P.m - 1 := by omega
  have hm0 : (P.m : Real) ≠ 0 := by
    exact_mod_cast (show P.m ≠ 0 by omega)
  have hx : P.x ≠ 0 := P.x_pos.ne'
  have hk : P.kappa ≠ 0 := P.kappa_pos.ne'
  have hp : P.p ≠ 0 := P.p_pos.ne'
  have hd : P.d = P.kappa * P.e := by rw [P.kappa_mul_e]
  have hpow : P.p ^ (P.m - 2) * P.x ^ (P.m - 2) =
      P.alpha ^ (P.m - 2) := by
    unfold x
    rw [← mul_pow]
    field_simp [hp]
  have haPow : P.alpha * P.alpha ^ (P.m - 2) =
      P.alpha ^ (P.m - 1) := by
    rw [mul_comm, ← pow_succ, hm2]
  unfold normalizationII reducedBracketII
  rw [show
      (P.m : Real) * P.d * P.alpha * P.p ^ (P.m - 2) *
          (P.x ^ (P.m - 2) *
            (((P.m - 1 : Nat) : Real) / ((P.m : Real) * P.x) -
              (1 + 1 / P.kappa) / (P.m : Real))) =
        (P.m : Real) * P.d * P.alpha *
          (P.p ^ (P.m - 2) * P.x ^ (P.m - 2)) *
            (((P.m - 1 : Nat) : Real) / ((P.m : Real) * P.x) -
              (1 + 1 / P.kappa) / (P.m : Real)) by ring,
    hpow]
  rw [hd]
  field_simp [hm0, hx, hk, P.e_pos.ne']
  rw [haPow]
  ring

lemma normalizationII_mul_reduced_sum :
    P.normalizationII * (P.reducedBracketII + P.lambdaII) =
      P.defectUpperII := by
  rw [mul_add, P.normalizationII_mul_reducedBracketII,
    P.normalizationII_mul_lambdaII]
  rfl

lemma R_le_defectUpperII : P.R <= P.defectUpperII := by
  have htau0 : 0 <= P.tau := by
    unfold tau
    exact div_nonneg P.q_nonneg P.alpha_pos.le
  have hbern :
      1 + ((P.m - 1 : Nat) : Real) * (P.tau - 1) <=
        P.tau ^ (P.m - 1) :=
    one_add_mul_sub_le_pow (by linarith : (-1 : Real) <= P.tau) _
  have hinner :
      P.alpha - P.p * P.tau ^ (P.m - 1) <=
        ((P.m - 1 : Nat) : Real) * P.d / P.x - (P.d + P.e) := by
    have hmul := mul_le_mul_of_nonneg_left hbern P.p_pos.le
    have hcalc :
        P.alpha - P.p *
            (1 + ((P.m - 1 : Nat) : Real) * (P.tau - 1)) =
          ((P.m - 1 : Nat) : Real) * P.d / P.x - (P.d + P.e) := by
      unfold tau x d e p
      field_simp [P.alpha_pos.ne']
      ring
    rw [← hcalc]
    linarith
  have hae : 0 <= P.alpha * P.e :=
    mul_nonneg P.alpha_pos.le P.e_pos.le
  have hL : P.L <= Real.sqrt (P.alpha * P.e) :=
    (Real.le_sqrt P.L_nonneg hae).2 P.L_sq_le_alpha_mul_e
  have hLpow : P.L ^ P.m <= Real.sqrt (P.alpha * P.e) ^ P.m :=
    pow_le_pow_left₀ P.L_nonneg hL _
  rw [P.R_defect_form]
  unfold defectUpperII
  exact add_le_add
    (mul_le_mul_of_nonneg_left hinner (pow_nonneg P.alpha_nonneg _)) hLpow

lemma normalizationII_mul_piII_le_linearPaymentII
    (hxi : 1 <= P.xi) :
    P.normalizationII * P.piII <= P.linearPaymentII := by
  let base := (P.m : Real) * P.p ^ (P.m - 2) *
    (1 - P.y ^ (P.m - 1)) / (1 + P.y)
  let scale := Real.sqrt (2 * P.alpha) * P.f * P.d *
    (1 - P.epsII)
  have heps : P.epsII <= 1 / 4 := P.epsII_le_quarter hxi
  have hepsFactor : 0 <= 1 - P.epsII := by linarith
  have hscale : 0 <= scale := by
    dsimp [scale]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) P.f_pos.le) P.d_pos.le)
      hepsFactor
  have hB : base * scale <= P.B * scale := by
    exact mul_le_mul_of_nonneg_right P.B_lower hscale
  have hleft : P.normalizationII * P.piII = base * scale := by
    dsimp [base, scale]
    unfold normalizationII piII
    rw [P.sqrt_one_sub_e, P.f_eq_alpha_mul_one_sub_ell]
    ring
  have hright : P.B * scale = P.linearPaymentII := by
    dsimp [scale]
    unfold linearPaymentII
    calc
      P.B * (Real.sqrt (2 * P.alpha) * P.f * P.d *
          (1 - P.epsII)) =
          Real.sqrt (2 * P.alpha) * P.B * P.f *
            (P.d * (1 - P.epsII)) := by ring
      _ = Real.sqrt (2 * P.alpha) * P.B * P.f *
          (P.d - P.e ^ 2 /
            (16 * P.alpha ^ 2 * (1 + P.rho))) := by
        rw [P.d_mul_one_sub_epsII]
  rw [hleft, ← hright]
  exact hB

theorem R_le_linearPaymentII_of_reduced
    (hxi : 1 <= P.xi)
    (hreduced : P.reducedBracketII + P.lambdaII <= P.piII) :
    P.R <= P.linearPaymentII := by
  calc
    P.R <= P.defectUpperII := P.R_le_defectUpperII
    _ = P.normalizationII *
        (P.reducedBracketII + P.lambdaII) :=
      P.normalizationII_mul_reduced_sum.symm
    _ <= P.normalizationII * P.piII :=
      mul_le_mul_of_nonneg_left hreduced P.normalizationII_pos.le
    _ <= P.linearPaymentII :=
      P.normalizationII_mul_piII_le_linearPaymentII hxi

theorem zoneB_reduced_battle
    (heLo : 1 / 60 <= P.e)
    (heHi : P.e <= 2033 / 10000)
    (hxi : 1 <= P.xi)
    (hfrontier : P.kappa <= kappaMax P.e) :
    P.reducedBracketII + P.lambdaII <= P.piII := by
  have hm15 := P.m_ge_fifteen
  have hn : 14 <= P.m - 1 := by omega
  calc
    P.reducedBracketII + P.lambdaII =
        bKAt P (P.m - 1) / P.x ^ 2 + P.lambdaII := by
      rw [P.reducedBracketII_eq_K]
    _ <= bKAt P (P.m - 1) / P.x ^ 2 + bLambdaBar P :=
      add_le_add (le_refl _) (P.lambdaII_le_bLambdaBar hxi)
    _ <= bPiUnder P.e P.kappa :=
      zoneB_certificate_battle P heLo heHi hxi hfrontier (P.m - 1) hn
    _ <= P.piII := P.bPiUnder_le_piII hxi heHi

lemma e_lt_zoneB_cutoff (hxi : 1 <= P.xi) :
    P.e < 2033 / 10000 := by
  have hchart := P.xi_chart
  have hkXi : P.e <= (1 - P.e) ^ 2 * P.kappa := by
    rw [hchart] at hxi
    rw [le_div_iff₀ P.e_pos] at hxi
    nlinarith
  have h6e : 0 < 6 * P.e := mul_pos (by norm_num) P.e_pos
  have hkQ : 6 * P.e * P.kappa < 1 - 3 * P.e := by
    simpa [mul_comm] using (lt_div_iff₀ h6e).mp P.kappa_lt_q
  have hfirst := mul_le_mul_of_nonneg_left hkXi h6e.le
  have hsecond := mul_lt_mul_of_pos_left hkQ (sq_pos_of_pos P.one_sub_e_pos)
  have hcompat :
      6 * P.e ^ 2 < (1 - P.e) ^ 2 * (1 - 3 * P.e) := by
    calc
      6 * P.e ^ 2 <= 6 * P.e * ((1 - P.e) ^ 2 * P.kappa) := by
        nlinarith
      _ < (1 - P.e) ^ 2 * (1 - 3 * P.e) := by
        nlinarith
  let c : Real := 2033 / 10000
  have hc0 : 0 < c := by norm_num [c]
  have hcThird : c < 1 / 3 := by norm_num [c]
  have hFc : 0 < 6 * c ^ 2 - (1 - c) ^ 2 * (1 - 3 * c) := by
    norm_num [c]
  by_contra hnot
  have hce : c <= P.e := le_of_not_gt hnot
  have hfactor :
      (6 * P.e ^ 2 - (1 - P.e) ^ 2 * (1 - 3 * P.e)) -
          (6 * c ^ 2 - (1 - c) ^ 2 * (1 - 3 * c)) =
        (P.e - c) *
          (3 * (P.e ^ 2 + P.e * c + c ^ 2) - (P.e + c) + 5) := by
    ring
  have hbracket :
      0 < 3 * (P.e ^ 2 + P.e * c + c ^ 2) - (P.e + c) + 5 := by
    have hsquares : 0 <= P.e ^ 2 + P.e * c + c ^ 2 := by
      exact add_nonneg
        (add_nonneg (sq_nonneg _) (mul_nonneg P.e_pos.le hc0.le))
        (sq_nonneg _)
    linarith [P.e_lt_third, hcThird]
  have hmono :
      6 * c ^ 2 - (1 - c) ^ 2 * (1 - 3 * c) <=
        6 * P.e ^ 2 - (1 - P.e) ^ 2 * (1 - 3 * P.e) := by
    have hprod : 0 <= (P.e - c) *
        (3 * (P.e ^ 2 + P.e * c + c ^ 2) - (P.e + c) + 5) :=
      mul_nonneg (sub_nonneg.mpr hce) hbracket.le
    nlinarith [hfactor]
  nlinarith

theorem zoneB_bound_of_e_le
    (heLo : 1 / 60 <= P.e)
    (heHi : P.e <= 2033 / 10000)
    (hxi : 1 <= P.xi)
    (hfrontier : P.kappa <= kappaMax P.e) :
    P.R <= P.C * psi P.xi P.rho := by
  have hreduced := P.zoneB_reduced_battle heLo heHi hxi hfrontier
  exact (P.R_le_linearPaymentII_of_reduced hxi hreduced).trans
    P.linearPaymentII_le_C_psi

theorem zoneB_bound
    (heLo : 1 / 60 <= P.e)
    (hxi : 1 <= P.xi)
    (hfrontier : P.kappa <= kappaMax P.e) :
    P.R <= P.C * psi P.xi P.rho :=
  P.zoneB_bound_of_e_le heLo (P.e_lt_zoneB_cutoff hxi).le hxi hfrontier

end AdmissibleParams

end OddCycleBound.RegionII.Scalar
