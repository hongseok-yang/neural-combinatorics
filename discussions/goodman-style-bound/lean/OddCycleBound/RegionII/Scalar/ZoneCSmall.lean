import OddCycleBound.RegionII.Scalar.ZoneA
import OddCycleBound.RegionII.Scalar.Payments

/-!
# Small-e Zone C

This file proves the `e <= 1/60`, `xi <= 1` part of Zone C.  The paper
uses an exponential estimate in `T = m e`.  Here the same decay is obtained
from the already formalized quadratic Bernoulli bound.  This gives a purely
rational battle in `T` and `z = m kappa`.
-/

noncomputable section

namespace OddCycleBound.RegionII.Scalar

def smallCDenom (T : Real) : Real := 1 + (8 / 5 : Real) * T + T ^ 2

namespace AdmissibleParams

variable (P : AdmissibleParams)

def smallCT : Real := (P.m : Real) * P.e

def smallCZ : Real := (P.m : Real) * P.kappa

lemma kappa_le_smallC (hxi : P.xi <= 1) :
    (1 - P.e) ^ 2 * P.kappa <= P.e := by
  rw [P.xi_chart] at hxi
  simpa using (div_le_iff₀ P.e_pos).mp hxi

lemma smallC_link (hxi : P.xi <= 1) :
    (1 - P.e) ^ 2 * P.smallCZ <= P.smallCT := by
  have hm0 : (0 : Real) <= P.m := by positivity
  have h := mul_le_mul_of_nonneg_left (P.kappa_le_smallC hxi) hm0
  simpa [smallCZ, smallCT, mul_assoc, mul_left_comm, mul_comm] using h

lemma kappa_le_smallC_const
    (he : P.e <= 1 / 60) (hxi : P.xi <= 1) :
    P.kappa <= 60 / 3481 := by
  have hone : (59 / 60 : Real) <= 1 - P.e := by linarith
  have hsq : (59 / 60 : Real) ^ 2 <= (1 - P.e) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hone 2
  have hk0 := P.kappa_pos.le
  have hscaled := mul_le_mul_of_nonneg_right hsq hk0
  have hlink := P.kappa_le_smallC hxi
  have hsmall : (59 / 60 : Real) ^ 2 * P.kappa <= 1 / 60 := by
    calc
      (59 / 60 : Real) ^ 2 * P.kappa <=
          (1 - P.e) ^ 2 * P.kappa := hscaled
      _ <= P.e := hlink
      _ <= 1 / 60 := he
  nlinarith

lemma smallC_m_ge_fifty_five
    (he : P.e <= 1 / 60) (hxi : P.xi <= 1) (hR : 0 < P.R) :
    55 <= P.m := by
  have hm15 := P.m_ge_fifteen
  have hm1pos : (0 : Real) < ((P.m - 1 : Nat) : Real) := by
    exact_mod_cast (show 0 < P.m - 1 by omega)
  have hthreshold := P.zoneA_kappa_threshold he hR
  have hbase : 93 / 100 <=
      P.kappa * ((P.m - 1 : Nat) : Real) :=
    (div_le_iff₀ hm1pos).mp hthreshold
  have hk := P.kappa_le_smallC_const he hxi
  by_contra hnot
  have hmle : P.m <= 54 := by omega
  have hm1le : P.m - 1 <= 53 := by omega
  have hm1leR : (((P.m - 1 : Nat) : Real)) <= 53 := by exact_mod_cast hm1le
  have hprod1 : P.kappa * ((P.m - 1 : Nat) : Real) <=
      (60 / 3481 : Real) * ((P.m - 1 : Nat) : Real) :=
    mul_le_mul_of_nonneg_right hk (by positivity)
  have hprod2 : (60 / 3481 : Real) * ((P.m - 1 : Nat) : Real) <=
      (60 / 3481 : Real) * 53 :=
    mul_le_mul_of_nonneg_left hm1leR (by norm_num)
  have hprod := hprod1.trans hprod2
  norm_num at hprod
  nlinarith

lemma smallCZ_ge
    (he : P.e <= 1 / 60) (hR : 0 < P.R) :
    93 / 100 <= P.smallCZ := by
  simpa [smallCZ] using P.m_mul_kappa_lower_zoneA he hR

lemma smallCT_pos : 0 < P.smallCT := by
  unfold smallCT
  have hmpos : (0 : Real) < P.m := by
    have hm15 := P.m_ge_fifteen
    exact_mod_cast (show 0 < P.m by omega)
  exact mul_pos hmpos P.e_pos

lemma smallCZ_pos : 0 < P.smallCZ := by
  unfold smallCZ
  have hmpos : (0 : Real) < P.m := by
    have hm15 := P.m_ge_fifteen
    exact_mod_cast (show 0 < P.m by omega)
  exact mul_pos hmpos P.kappa_pos

lemma smallC_link_fifty_nine
    (he : P.e <= 1 / 60) (hxi : P.xi <= 1) :
    (59 / 60 : Real) ^ 2 * P.smallCZ <= P.smallCT := by
  have hone : (59 / 60 : Real) <= 1 - P.e := by linarith
  have hsq : (59 / 60 : Real) ^ 2 <= (1 - P.e) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hone 2
  have hmul := mul_le_mul_of_nonneg_right hsq P.smallCZ_pos.le
  exact hmul.trans (P.smallC_link hxi)

lemma smallC_linear_le_zA (he : P.e <= 1 / 60) :
    (8 / 5 : Real) * P.smallCT <= P.zA := by
  have h := P.m_mul_e_le_zA he
  have hz := P.zA_pos.le
  unfold smallCT
  nlinarith

lemma smallC_square_le_zA (he : P.e <= 1 / 60) :
    P.smallCT ^ 2 <= (6 / 13 : Real) * P.zA ^ 2 := by
  have h := P.m_mul_e_le_zA he
  have hT0 := P.smallCT_pos.le
  have hz0 := P.zA_pos.le
  have hc0 : 0 <= (3029 / 5000 : Real) * P.zA := by positivity
  have hprod : 0 <=
      ((3029 / 5000 : Real) * P.zA - P.smallCT) *
        ((3029 / 5000 : Real) * P.zA + P.smallCT) :=
    mul_nonneg (sub_nonneg.mpr (by simpa [smallCT] using h))
      (add_nonneg hc0 hT0)
  nlinarith

lemma x_pow_le_smallCDenom (he : P.e <= 1 / 60) :
    P.x ^ (P.m - 2) <= 1 / smallCDenom P.smallCT := by
  let Dz : Real := 1 + P.zA + (6 / 13 : Real) * P.zA ^ 2
  let DT : Real := smallCDenom P.smallCT
  have hlin := P.smallC_linear_le_zA he
  have hsq := P.smallC_square_le_zA he
  have hden : DT <= Dz := by
    dsimp [DT, Dz, smallCDenom]
    linarith
  have hDz : 0 < Dz := by
    dsimp [Dz]
    nlinarith [P.zA_pos, sq_nonneg P.zA]
  have hDT : 0 < DT := by
    dsimp [DT, smallCDenom]
    nlinarith [P.smallCT_pos, sq_nonneg P.smallCT]
  calc
    P.x ^ (P.m - 2) <= 1 / Dz := by
      simpa [Dz] using P.x_pow_le_zoneA_rational
    _ <= 1 / DT := by
      rw [div_le_div_iff₀ hDz hDT]
      simpa [mul_comm] using hden

lemma smallCT_ge_five_eighth
    (he : P.e <= 1 / 60) (hxi : P.xi <= 1) (hR : 0 < P.R) :
    5 / 8 <= P.smallCT := by
  have hz := P.smallCZ_ge he hR
  have hlink := P.smallC_link_fifty_nine he hxi
  have hscaled := mul_le_mul_of_nonneg_left hz
    (by norm_num : (0 : Real) <= (59 / 60) ^ 2)
  norm_num at hscaled ⊢
  linarith

lemma x_pow_m_two_le_half
    (he : P.e <= 1 / 60) (hxi : P.xi <= 1) (hR : 0 < P.R) :
    P.x ^ (P.m - 2) <= 1 / 2 := by
  have hxpow := P.x_pow_le_smallCDenom he
  have hT := P.smallCT_ge_five_eighth he hxi hR
  have hD : 2 <= smallCDenom P.smallCT := by
    unfold smallCDenom
    nlinarith [sq_nonneg P.smallCT]
  have hDpos : 0 < smallCDenom P.smallCT := by
    unfold smallCDenom
    positivity
  have hrecip : 1 / smallCDenom P.smallCT <= 1 / 2 := by
    rw [div_le_div_iff₀ hDpos (by norm_num : (0 : Real) < 2)]
    nlinarith
  exact hxpow.trans hrecip

lemma x_pow_m_one_le_half
    (he : P.e <= 1 / 60) (hxi : P.xi <= 1) (hR : 0 < P.R) :
    P.x ^ (P.m - 1) <= 1 / 2 := by
  have hm15 := P.m_ge_fifteen
  have hm : P.m - 1 = (P.m - 2) + 1 := by omega
  rw [hm, pow_succ]
  calc
    P.x ^ (P.m - 2) * P.x <= P.x ^ (P.m - 2) * 1 :=
      mul_le_mul_of_nonneg_left P.x_lt_one.le (pow_nonneg P.x_pos.le _)
    _ = P.x ^ (P.m - 2) := by ring
    _ <= 1 / 2 := P.x_pow_m_two_le_half he hxi hR

end AdmissibleParams

/-- The rational replacement for the exponential battle in the paper. -/
lemma smallC_scalar_battle
    {T z : Real}
    (hT : 0 < T) (hz : 93 / 100 <= z)
    (hlink : (59 / 60 : Real) ^ 2 * z <= T)
    (hU : 0 < 11 / 10 - 1 / z) :
    (11 / 10 - 1 / z) / smallCDenom T <=
      (3 / 25 : Real) * z / T := by
  have hzpos : 0 < z := lt_of_lt_of_le (by norm_num) hz
  have hD : 0 < smallCDenom T := by unfold smallCDenom; positivity
  have hrewrite : (3 / 25 : Real) * z / T = (3 * z) / (25 * T) := by ring
  rw [hrewrite, div_le_div_iff₀ hD (mul_pos (by norm_num) hT)]
  by_cases hz1 : z <= 1
  · have hinv : 1 <= 1 / z := by
      rw [le_div_iff₀ hzpos]
      simpa using hz1
    have hUup : 11 / 10 - 1 / z <= (1 / 10 : Real) := by linarith
    have hzsq : (93 / 100 : Real) ^ 2 <= z ^ 2 := by
      have hprod : 0 <= (z - 93 / 100) * (z + 93 / 100) :=
        mul_nonneg (sub_nonneg.mpr hz) (by positivity)
      nlinarith
    have hzt : (5 / 6 : Real) <= z * T := by
      have hmul := mul_le_mul_of_nonneg_left hlink hzpos.le
      nlinarith
    have hleft : 25 * T * (11 / 10 - 1 / z) <= (5 / 2 : Real) * T := by
      have := mul_le_mul_of_nonneg_left hUup
        (mul_nonneg (by norm_num : (0 : Real) <= 25) hT.le)
      nlinarith
    have hDsq : T ^ 2 <= smallCDenom T := by
      unfold smallCDenom
      nlinarith
    have hright : (5 / 2 : Real) * T <= 3 * z * smallCDenom T := by
      have h1 := mul_le_mul_of_nonneg_left hDsq
        (mul_nonneg (by norm_num : (0 : Real) <= 3) hzpos.le)
      have h2 := mul_le_mul_of_nonneg_left hzt
        (mul_nonneg (by norm_num : (0 : Real) <= 3) hT.le)
      nlinarith
    simpa [mul_comm] using hleft.trans hright
  · have hzgt : 1 < z := lt_of_not_ge hz1
    have hUup : 11 / 10 - 1 / z <= z / 3 := by
      apply (le_div_iff₀ (by norm_num : (0 : Real) < 3)).2
      field_simp [hzpos.ne']
      nlinarith [sq_nonneg (z - 33 / 20)]
    have hDlin : (25 / 9 : Real) * T <= smallCDenom T := by
      unfold smallCDenom
      nlinarith [sq_nonneg (T - 53 / 90)]
    have hleft : 25 * T * (11 / 10 - 1 / z) <=
        (25 / 3 : Real) * T * z := by
      have := mul_le_mul_of_nonneg_left hUup
        (mul_nonneg (by norm_num : (0 : Real) <= 25) hT.le)
      nlinarith
    have hright : (25 / 3 : Real) * T * z <=
        3 * z * smallCDenom T := by
      have := mul_le_mul_of_nonneg_left hDlin
        (mul_nonneg (by norm_num : (0 : Real) <= 3) hzpos.le)
      nlinarith
    simpa [mul_comm] using hleft.trans hright

namespace AdmissibleParams

variable (P : AdmissibleParams)

lemma smallC_bracket_upper (he : P.e <= 1 / 60) :
    (((P.m - 1 : Nat) : Real) / ((P.m : Real) * P.x) -
        (1 + 1 / P.kappa) / (P.m : Real)) + sigmaA P.e <=
      11 / 10 - 1 / P.smallCZ := by
  have hmpos : (0 : Real) < P.m := by
    have hm15 := P.m_ge_fifteen
    exact_mod_cast (show 0 < P.m by omega)
  have hfirst :
      ((P.m - 1 : Nat) : Real) / ((P.m : Real) * P.x) -
          (1 + 1 / P.kappa) / (P.m : Real) <=
        1 / P.x - 1 / P.smallCZ := by
    have hm1 : ((P.m - 1 : Nat) : Real) + 1 = (P.m : Real) := by
      have hm15 := P.m_ge_fifteen
      exact_mod_cast (show P.m - 1 + 1 = P.m by omega)
    have heq :
        ((P.m - 1 : Nat) : Real) / ((P.m : Real) * P.x) -
            (1 + 1 / P.kappa) / (P.m : Real) =
          (1 / P.x - 1 / P.smallCZ) -
            (1 / P.x + 1) / (P.m : Real) := by
      unfold smallCZ
      field_simp [hmpos.ne', P.x_pos.ne', P.kappa_pos.ne']
      have hm1k := congrArg (fun t : Real => t * P.kappa) hm1
      nlinarith
    rw [heq]
    have hnonneg : 0 <= (1 / P.x + 1) / (P.m : Real) := by
      have hinv : 0 <= 1 / P.x := (one_div_pos.mpr P.x_pos).le
      exact div_nonneg (by linarith) hmpos.le
    linarith
  have hinv := P.one_div_x_upper_zoneA he
  have hk := P.kappa_le_one
  have hsigma := P.sigmaA_lt_zoneA_margin he
  have herr :
      (1017 / 500 : Real) * (1 + P.kappa) * P.e + sigmaA P.e <= 1 / 10 := by
    have he0 := P.e_pos.le
    have hmul := mul_le_mul_of_nonneg_right hk he0
    nlinarith
  linarith

lemma reduced_sum_le_smallC
    (he : P.e <= 1 / 60) (hxi : P.xi <= 1) (hR : 0 < P.R) :
    P.reducedBracketII + P.lambdaII <=
      (3 / 25 : Real) * P.kappa / P.e := by
  let U : Real := 11 / 10 - 1 / P.smallCZ
  have hbracket := P.smallC_bracket_upper he
  have hlambda := P.lambdaII_le_sigma_mul_xpow he hR
  have hsum : P.reducedBracketII + P.lambdaII <=
      P.x ^ (P.m - 2) * U := by
    unfold reducedBracketII
    dsimp [U]
    calc
      P.x ^ (P.m - 2) *
            (((P.m - 1 : Nat) : Real) / ((P.m : Real) * P.x) -
              (1 + 1 / P.kappa) / (P.m : Real)) + P.lambdaII <=
          P.x ^ (P.m - 2) *
            (((P.m - 1 : Nat) : Real) / ((P.m : Real) * P.x) -
              (1 + 1 / P.kappa) / (P.m : Real)) +
            sigmaA P.e * P.x ^ (P.m - 2) :=
        add_le_add (le_refl _) hlambda
      _ = P.x ^ (P.m - 2) *
          ((((P.m - 1 : Nat) : Real) / ((P.m : Real) * P.x) -
            (1 + 1 / P.kappa) / (P.m : Real)) + sigmaA P.e) := by ring
      _ <= P.x ^ (P.m - 2) * (11 / 10 - 1 / P.smallCZ) :=
        mul_le_mul_of_nonneg_left hbracket (pow_nonneg P.x_pos.le _)
  have hU : 0 < U := by
    have hpos := P.reduced_sum_pos_of_R_pos hR
    by_contra hnot
    have hUnonpos : U <= 0 := le_of_not_gt hnot
    have hright : P.x ^ (P.m - 2) * U <= 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg P.x_pos.le _) hUnonpos
    linarith
  have hxpow := P.x_pow_le_smallCDenom he
  have hscaled : P.x ^ (P.m - 2) * U <=
      (1 / smallCDenom P.smallCT) * U :=
    mul_le_mul_of_nonneg_right hxpow hU.le
  have hbattle := smallC_scalar_battle P.smallCT_pos
    (P.smallCZ_ge he hR) (P.smallC_link_fifty_nine he hxi) hU
  have hratio :
      (3 / 25 : Real) * P.smallCZ / P.smallCT =
        (3 / 25 : Real) * P.kappa / P.e := by
    unfold smallCZ smallCT
    have hm0 : (P.m : Real) ≠ 0 := by
      have hm15 := P.m_ge_fifteen
      exact_mod_cast (show P.m ≠ 0 by omega)
    field_simp [hm0, P.e_pos.ne']
  calc
    P.reducedBracketII + P.lambdaII <= P.x ^ (P.m - 2) * U := hsum
    _ <= (1 / smallCDenom P.smallCT) * U := hscaled
    _ = U / smallCDenom P.smallCT := by ring
    _ <= (3 / 25 : Real) * P.smallCZ / P.smallCT := by
      simpa [U] using hbattle
    _ = (3 / 25 : Real) * P.kappa / P.e := hratio

lemma k_alpha_div_k_L_upper :
    P.k P.alpha / P.k P.L <= (1 + P.y) / (1 + P.x) := by
  have hyx : P.y <= P.x := P.y_lt_s.trans P.s_lt_x |>.le
  have hypow : P.y ^ (P.m - 1) <= P.x ^ (P.m - 1) :=
    pow_le_pow_left₀ P.y_nonneg hyx _
  have hpPow : 0 < P.p ^ (P.m - 2) := pow_pos P.p_pos _
  have hxden : 0 < 1 + P.x := by linarith [P.x_pos]
  have hyden : 0 < 1 + P.y := by linarith [P.y_nonneg]
  rw [div_le_iff₀ P.k_L_pos]
  rw [P.k_alpha_formula, P.k_L_formula]
  field_simp [hpPow.ne', hxden.ne', hyden.ne']
  nlinarith

lemma y_pow_m_two_le_seventeen
    (he : P.e <= 1 / 60) :
    P.y ^ (P.m - 2) <= 17 / 500 := by
  have hm15 := P.m_ge_fifteen
  have htwo : 2 <= P.m - 2 := by omega
  have hy1 : P.y <= 1 :=
    P.y_le_ell.trans (P.ell_le_zoneA_decimal he) |>.trans (by norm_num)
  have hpow : P.y ^ (P.m - 2) <= P.y ^ 2 :=
    pow_le_pow_of_le_one P.y_nonneg hy1 htwo
  have hy : P.y <= 921 / 5000 :=
    P.y_le_ell.trans (P.ell_le_zoneA_decimal he)
  have hysq : P.y ^ 2 <= (921 / 5000 : Real) ^ 2 :=
    pow_le_pow_left₀ P.y_nonneg hy 2
  exact hpow.trans hysq |>.trans (by norm_num)

lemma one_sub_y_pow_ge_ninety_nine
    (he : P.e <= 1 / 60) :
    99 / 100 <= 1 - P.y ^ (P.m - 1) := by
  have hypow := P.y_pow_le_sigmaA he
  have hsigma := P.sigmaA_lt_zoneA_margin he
  linarith

lemma one_add_y_le_six_fifths
    (he : P.e <= 1 / 60) :
    1 + P.y <= 6 / 5 := by
  have hy := P.y_le_ell.trans (P.ell_le_zoneA_decimal he)
  linarith

lemma L_pow_eq_p_mul_y_pow :
    P.L ^ (P.m - 2) = P.p ^ (P.m - 2) * P.y ^ (P.m - 2) := by
  unfold y
  rw [← mul_pow]
  field_simp [P.p_pos.ne']

lemma L_tail_le_one_percent
    (he : P.e <= 1 / 60) (hxi : P.xi <= 1) (hR : 0 < P.R) :
    2 * P.L ^ (P.m - 2) <=
      (1 / 100 : Real) * (P.m : Real) * P.k P.L := by
  have hm55 := P.smallC_m_ge_fifty_five he hxi hR
  have hmR : (55 : Real) <= P.m := by exact_mod_cast hm55
  have hypow := P.y_pow_m_two_le_seventeen he
  have hyden := P.one_add_y_le_six_fifths he
  have hsub := P.one_sub_y_pow_ge_ninety_nine he
  have hprod : P.y ^ (P.m - 2) * (1 + P.y) <=
      (17 / 500 : Real) * (6 / 5) :=
    mul_le_mul hypow hyden P.one_add_y_pos.le (by norm_num)
  have hleft : 200 * (P.y ^ (P.m - 2) * (1 + P.y)) <= 204 / 25 := by
    nlinarith
  have hright : (5445 / 100 : Real) <=
      (P.m : Real) * (1 - P.y ^ (P.m - 1)) := by
    have hmul := mul_le_mul hmR hsub (by norm_num)
      (by positivity : (0 : Real) <= P.m)
    norm_num at hmul ⊢
    exact hmul
  have hscalar :
      200 * P.y ^ (P.m - 2) * (1 + P.y) <=
        (P.m : Real) * (1 - P.y ^ (P.m - 1)) := by
    nlinarith
  have hpPow : 0 < P.p ^ (P.m - 2) := pow_pos P.p_pos _
  have hyPos : 0 < 1 + P.y := by linarith [P.y_nonneg]
  rw [P.L_pow_eq_p_mul_y_pow, P.k_L_formula]
  rw [show (1 / 100 : Real) * (P.m : Real) *
      (P.p ^ (P.m - 2) * (1 - P.y ^ (P.m - 1)) / (1 + P.y)) =
      ((1 / 100 : Real) * (P.m : Real) * P.p ^ (P.m - 2) *
        (1 - P.y ^ (P.m - 1))) / (1 + P.y) by ring]
  apply (le_div_iff₀ hyPos).2
  have hscaled := mul_le_mul_of_nonneg_left hscalar
    (div_nonneg hpPow.le (by norm_num : (0 : Real) <= 200))
  nlinarith

lemma ratio_yx_le (he : P.e <= 1 / 60) :
    (1 + P.y) / (1 + P.x) <= 49 / 80 := by
  have hy : P.y <= 921 / 5000 := by
    exact P.y_le_ell.trans (P.ell_le_zoneA_decimal he)
  have hx : 59 / 63 <= P.x :=
    P.x_ge_zoneA he
  have hxden : 0 < 1 + P.x := by linarith [P.x_pos]
  rw [div_le_iff₀ hxden]
  nlinarith

lemma A_div_B_le_five_eighths
    (he : P.e <= 1 / 60) (hxi : P.xi <= 1) (hR : 0 < P.R) :
    P.A / P.B <= 5 / 8 := by
  let r : Real := (1 + P.y) / (1 + P.x)
  have hr0 : 0 <= r := by
    dsimp [r]
    exact div_nonneg (by linarith [P.y_nonneg]) (by linarith [P.x_pos])
  have hr : r <= 49 / 80 := by simpa [r] using P.ratio_yx_le he
  have hk : P.k P.alpha <= r * P.k P.L := by
    exact (div_le_iff₀ P.k_L_pos).mp (by simpa [r] using P.k_alpha_div_k_L_upper)
  have hm0 : (0 : Real) <= P.m := by positivity
  have hmk := mul_le_mul_of_nonneg_left hk hm0
  have htail := P.L_tail_le_one_percent he hxi hR
  have hlead : 0 <= 2 * P.L ^ (P.m - 2) :=
    mul_nonneg (by norm_num) (pow_nonneg P.L_nonneg _)
  have hkL0 : 0 <= (P.m : Real) * P.k P.L :=
    mul_nonneg hm0 P.k_L_pos.le
  have hcoef0 : 0 <= r + 1 / 100 := by positivity
  apply (div_le_iff₀ P.B_pos).2
  unfold A B
  have htail' : 2 * P.L ^ (P.m - 2) <=
      (1 / 100 : Real) * ((P.m : Real) * P.k P.L) := by
    simpa [mul_assoc] using htail
  have hmk' : (P.m : Real) * P.k P.alpha <=
      r * ((P.m : Real) * P.k P.L) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmk
  calc
    2 * P.L ^ (P.m - 2) + (P.m : Real) * P.k P.alpha <=
        (1 / 100 : Real) * ((P.m : Real) * P.k P.L) +
          r * ((P.m : Real) * P.k P.L) := by
      exact add_le_add htail' hmk'
    _ = (r + 1 / 100) * ((P.m : Real) * P.k P.L) := by ring
    _ <= (r + 1 / 100) *
        (2 * P.L ^ (P.m - 2) + (P.m : Real) * P.k P.L) := by
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hlead) hcoef0
    _ <= (5 / 8 : Real) *
        (2 * P.L ^ (P.m - 2) + (P.m : Real) * P.k P.L) := by
      exact mul_le_mul_of_nonneg_right (by linarith)
        (add_nonneg hlead hkL0)

lemma rho_scale_le_five_eighths (he : P.e <= 1 / 60) :
    Real.sqrt P.alpha / (2 * Real.sqrt 2 * P.f) <= 5 / 8 := by
  let c : Real := (59 / 120) * (4079 / 5000)
  have ha := P.alpha_ge_zoneA he
  have hell : 4079 / 5000 <= 1 - P.ell := by
    linarith [P.ell_le_zoneA_decimal he]
  have hfactor : 0 <= 1 - P.ell := by linarith [P.ell_lt_one_global]
  have hfLower : c <= P.f := by
    rw [P.f_eq_alpha_mul_one_sub_ell]
    dsimp [c]
    exact mul_le_mul ha hell (by norm_num) P.alpha_nonneg
  have hc0 : 0 <= c := by norm_num [c]
  have hfSq : c ^ 2 <= P.f ^ 2 := by
    have hprod : 0 <= (P.f - c) * (P.f + c) :=
      mul_nonneg (sub_nonneg.mpr hfLower) (add_nonneg P.f_pos.le hc0)
    nlinarith
  have hrootTwoSq : Real.sqrt (2 : Real) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hrhs0 : 0 <= (5 / 4 : Real) * Real.sqrt 2 * P.f := by positivity
  have hsquare : P.alpha <=
      ((5 / 4 : Real) * Real.sqrt 2 * P.f) ^ 2 := by
    have haHalf := P.alpha_lt_half.le
    dsimp [c] at hfSq
    rw [show ((5 / 4 : Real) * Real.sqrt 2 * P.f) ^ 2 =
        (25 / 16 : Real) * Real.sqrt 2 ^ 2 * P.f ^ 2 by ring,
      hrootTwoSq]
    norm_num at hfSq ⊢
    nlinarith
  have hsqrt : Real.sqrt P.alpha <=
      (5 / 4 : Real) * Real.sqrt 2 * P.f := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hrhs0).mp
    rw [Real.sq_sqrt P.alpha_nonneg]
    exact hsquare
  have hden : 0 < 2 * Real.sqrt 2 * P.f := by positivity
  rw [div_le_iff₀ hden]
  nlinarith

lemma rho_le_smallC
    (he : P.e <= 1 / 60) (hxi : P.xi <= 1) (hR : 0 < P.R) :
    P.rho <= 25 / 64 := by
  have hAB := P.A_div_B_le_five_eighths he hxi hR
  have hscale := P.rho_scale_le_five_eighths he
  have hAB0 : 0 <= P.A / P.B := div_nonneg P.A_nonneg P.B_pos.le
  have hscale0 : 0 <= Real.sqrt P.alpha / (2 * Real.sqrt 2 * P.f) :=
    div_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) P.f_pos.le)
  unfold rho
  calc
    P.A / P.B * (Real.sqrt P.alpha / (2 * Real.sqrt 2 * P.f)) <=
        (5 / 8 : Real) *
          (Real.sqrt P.alpha / (2 * Real.sqrt 2 * P.f)) :=
      mul_le_mul_of_nonneg_right hAB hscale0
    _ <= (5 / 8 : Real) * (5 / 8) :=
      mul_le_mul_of_nonneg_left hscale (by norm_num)
    _ = 25 / 64 := by norm_num

lemma smallC_huber_gate
    (he : P.e <= 1 / 60) (hxi : P.xi <= 1) (hR : 0 < P.R) :
    2 * P.rho * P.xi <= 1 := by
  have hrho := P.rho_le_smallC he hxi hR
  have hmul := mul_le_mul hrho hxi P.xi_pos.le (by norm_num)
  nlinarith

lemma psi_ge_rho_xi_sq (hgate : 2 * P.rho * P.xi <= 1) :
    P.rho * P.xi ^ 2 <= psi P.xi P.rho := by
  let lambda : Real := 2 * P.rho * P.xi
  have hlambda0 : 0 <= lambda := by
    dsimp [lambda]
    exact mul_nonneg (mul_nonneg (by norm_num) P.rho_pos.le) P.xi_pos.le
  have hlambda1 : lambda <= 1 := by simpa [lambda] using hgate
  have hcert := huberDual_le_psi
    (xi := P.xi) (rho := P.rho) (lambda := lambda)
    P.rho_pos.le ⟨hlambda0, hlambda1⟩
  have hden : 0 < 1 + 2 * P.xi := by linarith [P.xi_pos]
  have hvalue :
      huberDual P.xi P.rho lambda =
        P.rho * P.xi ^ 2 * (1 + 4 * P.xi) / (1 + 2 * P.xi) := by
    dsimp [lambda]
    unfold huberDual
    field_simp [P.rho_pos.ne', hden.ne']
    ring
  have hratio : (1 : Real) <= (1 + 4 * P.xi) / (1 + 2 * P.xi) := by
    rw [le_div_iff₀ hden]
    linarith [P.xi_pos]
  have hbase : 0 <= P.rho * P.xi ^ 2 :=
    mul_nonneg P.rho_pos.le (sq_nonneg _)
  calc
    P.rho * P.xi ^ 2 <=
        P.rho * P.xi ^ 2 * ((1 + 4 * P.xi) / (1 + 2 * P.xi)) :=
      by simpa using mul_le_mul_of_nonneg_left hratio hbase
    _ = P.rho * P.xi ^ 2 * (1 + 4 * P.xi) / (1 + 2 * P.xi) := by ring
    _ = huberDual P.xi P.rho lambda := hvalue.symm
    _ <= psi P.xi P.rho := hcert

lemma C_mul_rho_mul_xi_sq :
    P.C * P.rho * P.xi ^ 2 = 2 * P.alpha ^ 3 * P.A * P.kappa ^ 2 := by
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
  have hB : P.B ≠ 0 := P.B_pos.ne'
  have hf : P.f ≠ 0 := P.f_pos.ne'
  unfold C rho xi kappa
  field_simp [he, ha, hB, hf, hrtPos.ne']
  ring_nf at hroot ⊢
  rw [hroot]

lemma A_lower_smallC
    (he : P.e <= 1 / 60) (hxi : P.xi <= 1) (hR : 0 < P.R) :
    (1 / 4 : Real) * (P.m : Real) * P.p ^ (P.m - 2) <= P.A := by
  have hxpow := P.x_pow_m_one_le_half he hxi hR
  have hxden : 0 < 1 + P.x := by linarith [P.x_pos]
  have hxle : P.x <= 1 := P.x_lt_one.le
  have hfrac :
      (1 / 4 : Real) <= (1 - P.x ^ (P.m - 1)) / (1 + P.x) := by
    rw [le_div_iff₀ hxden]
    nlinarith
  have hm0 : (0 : Real) <= P.m := by positivity
  have hpPow0 : 0 <= P.p ^ (P.m - 2) := pow_nonneg P.p_pos.le _
  have hscale0 : 0 <= (P.m : Real) * P.p ^ (P.m - 2) :=
    mul_nonneg hm0 hpPow0
  have hscaled := mul_le_mul_of_nonneg_left hfrac hscale0
  have hk :
      (1 / 4 : Real) * ((P.m : Real) * P.p ^ (P.m - 2)) <=
        (P.m : Real) * P.k P.alpha := by
    rw [P.k_alpha_formula]
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
  unfold A
  have htail : 0 <= 2 * P.L ^ (P.m - 2) :=
    mul_nonneg (by norm_num) (pow_nonneg P.L_nonneg _)
  nlinarith

lemma normalized_smallC_payment
    (he : P.e <= 1 / 60) (hxi : P.xi <= 1) (hR : 0 < P.R) :
    P.normalizationII * ((3 / 25 : Real) * P.kappa / P.e) <=
      P.C * (P.rho * P.xi ^ 2) := by
  have hA := P.A_lower_smallC he hxi hR
  have ha := P.alpha_ge_zoneA he
  have haSum : 0 <= P.alpha + 59 / 120 := by positivity
  have haSq : (59 / 120 : Real) ^ 2 <= P.alpha ^ 2 := by
    have hprod : 0 <= (P.alpha - 59 / 120) * (P.alpha + 59 / 120) :=
      mul_nonneg (sub_nonneg.mpr ha) haSum
    nlinarith
  have hcoef : (3 / 25 : Real) <= (1 / 2 : Real) * P.alpha ^ 2 := by
    nlinarith
  have hcommon0 :
      0 <= (P.m : Real) * P.alpha * P.p ^ (P.m - 2) * P.kappa ^ 2 := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) P.alpha_pos.le)
        (pow_nonneg P.p_pos.le _))
      (sq_nonneg _)
  have hcoefScaled := mul_le_mul_of_nonneg_right hcoef hcommon0
  have hA0 : 0 <= 2 * P.alpha ^ 3 * P.kappa ^ 2 := by positivity
  have hAScaled := mul_le_mul_of_nonneg_left hA hA0
  have hnorm :
      P.normalizationII * ((3 / 25 : Real) * P.kappa / P.e) =
        (3 / 25 : Real) *
          ((P.m : Real) * P.alpha * P.p ^ (P.m - 2) * P.kappa ^ 2) := by
    unfold normalizationII
    rw [show P.d = P.kappa * P.e by rw [P.kappa_mul_e]]
    field_simp [P.e_pos.ne']
  have hC :
      P.C * (P.rho * P.xi ^ 2) =
        2 * P.alpha ^ 3 * P.A * P.kappa ^ 2 := by
    rw [← mul_assoc, P.C_mul_rho_mul_xi_sq]
  rw [hnorm, hC]
  calc
    (3 / 25 : Real) *
          ((P.m : Real) * P.alpha * P.p ^ (P.m - 2) * P.kappa ^ 2) <=
        (1 / 2 : Real) * P.alpha ^ 2 *
          ((P.m : Real) * P.alpha * P.p ^ (P.m - 2) * P.kappa ^ 2) :=
      hcoefScaled
    _ = (2 * P.alpha ^ 3 * P.kappa ^ 2) *
          ((1 / 4 : Real) * (P.m : Real) * P.p ^ (P.m - 2)) := by ring
    _ <= (2 * P.alpha ^ 3 * P.kappa ^ 2) * P.A := hAScaled
    _ = 2 * P.alpha ^ 3 * P.A * P.kappa ^ 2 := by ring

theorem zoneC_small_bound
    (he : P.e <= 1 / 60) (hxi : P.xi <= 1) :
    P.R <= P.C * psi P.xi P.rho := by
  by_cases hR : 0 < P.R
  · have hred := P.reduced_sum_le_smallC he hxi hR
    have hpsi := P.psi_ge_rho_xi_sq (P.smallC_huber_gate he hxi hR)
    calc
      P.R <= P.defectUpperII := P.R_le_defectUpperII
      _ = P.normalizationII *
          (P.reducedBracketII + P.lambdaII) :=
        P.normalizationII_mul_reduced_sum.symm
      _ <= P.normalizationII *
          ((3 / 25 : Real) * P.kappa / P.e) :=
        mul_le_mul_of_nonneg_left hred P.normalizationII_pos.le
      _ <= P.C * (P.rho * P.xi ^ 2) :=
        P.normalized_smallC_payment he hxi hR
      _ <= P.C * psi P.xi P.rho :=
        mul_le_mul_of_nonneg_left hpsi P.C_pos.le
  · have hR0 : P.R <= 0 := le_of_not_gt hR
    have hpsi0 : 0 <= psi P.xi P.rho := psi_nonneg P.rho_pos.le
    exact hR0.trans (mul_nonneg P.C_pos.le hpsi0)

end AdmissibleParams
end OddCycleBound.RegionII.Scalar
