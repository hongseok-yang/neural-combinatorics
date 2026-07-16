import OddCycleBound.RegionII.Scalar.Payments

/-!
# The analytic Turan corner

This file proves the final sliver of moderate Zone C, where
`1 / 3 - 1 / 1000 < e < 1 / 3`.  The proof follows the corrected July 12b
argument, with one simplification: the already formalized frontier-gap bound
`f >= d + delta` gives the residual estimate directly.
-/

noncomputable section

namespace OddCycleBound.RegionII.Scalar

open Finset

/-- Upper secant estimate for an integral power on the nonnegative line. -/
lemma pow_sub_pow_le_nat_mul
    {a b : Real} {n : Nat} (hb : 0 <= b) (hab : b <= a) :
    a ^ n - b ^ n <= (n : Real) * (a - b) * a ^ (n - 1) := by
  have ha : 0 <= a := hb.trans hab
  have hsum :
      (∑ i ∈ range n, a ^ i * b ^ (n - 1 - i)) <=
        ∑ i ∈ range n, a ^ i * a ^ (n - 1 - i) := by
    apply sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hb hab _) (pow_nonneg ha _)
  have hdiff := geom_sum₂_mul_of_ge hab n
  rw [← hdiff]
  calc
    (∑ i ∈ range n, a ^ i * b ^ (n - 1 - i)) * (a - b) <=
        (∑ i ∈ range n, a ^ i * a ^ (n - 1 - i)) * (a - b) :=
      mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr hab)
    _ = (n : Real) * (a - b) * a ^ (n - 1) := by
      rw [geom_sum₂_self]
      ring

/-- Lower secant estimate for an integral power on the nonnegative line. -/
lemma nat_mul_pow_le_pow_sub_pow
    {a b : Real} {n : Nat} (hb : 0 <= b) (hab : b <= a) :
    (n : Real) * (a - b) * b ^ (n - 1) <= a ^ n - b ^ n := by
  have ha : 0 <= a := hb.trans hab
  have hsum :
      (∑ i ∈ range n, b ^ i * b ^ (n - 1 - i)) <=
        ∑ i ∈ range n, a ^ i * b ^ (n - 1 - i) := by
    apply sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hb hab _) (pow_nonneg hb _)
  have hdiff := geom_sum₂_mul_of_ge hab n
  rw [← hdiff]
  calc
    (n : Real) * (a - b) * b ^ (n - 1) =
        (∑ i ∈ range n, b ^ i * b ^ (n - 1 - i)) * (a - b) := by
      rw [geom_sum₂_self]
      ring
    _ <= (∑ i ∈ range n, a ^ i * b ^ (n - 1 - i)) * (a - b) :=
      mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr hab)

/-- The elementary decay step used at the Turan corner.  The deliberately
loose rational cutoff `50113 / 100000` makes the cubic factor harmless from
`n = 13` onward. -/
lemma cubic_power_decay_step
    {x : Real} (hx0 : 0 <= x) (hx : x <= 50113 / 100000)
    {n : Nat} (hn : 13 <= n) :
    (((n + 1 : Nat) : Real) ^ 3) * x ^ n <=
      (n : Real) ^ 3 * x ^ (n - 1) := by
  have hnReal : (13 : Real) <= n := by exact_mod_cast hn
  have hn0 : (0 : Real) <= n := by positivity
  have hratio : ((n + 1 : Nat) : Real) <= (14 / 13 : Real) * n := by
    push_cast
    linarith
  have hcube : (((n + 1 : Nat) : Real) ^ 3) <=
      ((14 / 13 : Real) * n) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hratio 3
  have hxScaled := mul_le_mul hcube hx (by positivity) (by positivity)
  have hcoefficient :
      ((14 / 13 : Real) * n) ^ 3 * (50113 / 100000 : Real) <=
        (n : Real) ^ 3 := by
    have : (50113 / 100000 : Real) * (14 / 13) ^ 3 <= 1 := by norm_num
    nlinarith [mul_nonneg (sq_nonneg (n : Real)) hn0]
  have hfactor :
      (((n + 1 : Nat) : Real) ^ 3) * x <= (n : Real) ^ 3 :=
    hxScaled.trans hcoefficient
  have hnOne : 1 <= n := le_trans (by norm_num) hn
  have hpow : x ^ n = x * x ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
    ring
  calc
    (((n + 1 : Nat) : Real) ^ 3) * x ^ n =
        ((((n + 1 : Nat) : Real) ^ 3) * x) * x ^ (n - 1) := by
      rw [hpow]
      ring
    _ <= (n : Real) ^ 3 * x ^ (n - 1) :=
      mul_le_mul_of_nonneg_right hfactor (pow_nonneg hx0 _)

/-- Iteration of `cubic_power_decay_step`, normalized at `n = 13`. -/
lemma cubic_power_decay
    {x : Real} (hx0 : 0 <= x) (hx : x <= 50113 / 100000)
    {n : Nat} (hn : 13 <= n) :
    (n : Real) ^ 3 * x ^ (n - 1) <= 13 ^ 3 * x ^ 12 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      exact (cubic_power_decay_step hx0 hx hn).trans ih

namespace AdmissibleParams

variable (P : AdmissibleParams)

def cornerDelta : Real := P.alpha - 1 / 3

def cornerN : Real :=
  P.d - (P.q - P.L) * P.ell ^ (P.m - 1)

lemma cornerDelta_pos : 0 < P.cornerDelta := by
  simpa [cornerDelta] using P.delta_pos

lemma d_lt_cornerDelta : P.d < P.cornerDelta := by
  simpa [cornerDelta] using P.d_lt_delta

lemma e_eq_cornerDelta : P.e = 1 / 3 - 2 * P.cornerDelta := by
  unfold e cornerDelta
  ring

lemma alpha_eq_cornerDelta : P.alpha = 1 / 3 + P.cornerDelta := by
  unfold cornerDelta
  ring

lemma cornerDelta_lt
    (he : 1 / 3 - 1 / 1000 < P.e) :
    P.cornerDelta < 1 / 2000 := by
  rw [P.e_eq_cornerDelta] at he
  linarith

lemma cornerDelta_le
    (he : 1 / 3 - 1 / 1000 < P.e) :
    P.cornerDelta <= 1 / 2000 := (P.cornerDelta_lt he).le

lemma alpha_le_corner
    (he : 1 / 3 - 1 / 1000 < P.e) :
    P.alpha <= 2003 / 6000 := by
  rw [P.alpha_eq_cornerDelta]
  linarith [P.cornerDelta_le he]

lemma e_ge_corner
    (he : 1 / 3 - 1 / 1000 < P.e) :
    997 / 3000 <= P.e := by
  norm_num at he ⊢
  exact he.le

lemma L_sq_sub_e_sq :
    P.L ^ 2 - P.e ^ 2 =
      P.cornerDelta - P.d / 3 - 6 * P.cornerDelta ^ 2 +
        2 * P.cornerDelta * P.d - P.d ^ 2 := by
  rw [P.L_sq]
  unfold p d e cornerDelta
  ring

lemma e_lt_L_corner
    (he : 1 / 3 - 1 / 1000 < P.e) :
    P.e < P.L := by
  have hdelta := P.cornerDelta_pos
  have hd0 := P.d_pos
  have hd := P.d_lt_cornerDelta
  have hdeltaUp := P.cornerDelta_le he
  have hdiff : 0 < P.L ^ 2 - P.e ^ 2 := by
    rw [P.L_sq_sub_e_sq]
    have hquad : 0 <= P.d * (P.cornerDelta - P.d) :=
      mul_nonneg hd0.le (sub_nonneg.mpr hd.le)
    have hrough :
        2 / 3 * P.cornerDelta - 6 * P.cornerDelta ^ 2 <=
          P.cornerDelta - P.d / 3 - 6 * P.cornerDelta ^ 2 +
            2 * P.cornerDelta * P.d - P.d ^ 2 := by
      nlinarith
    have hpositive :
        0 < 2 / 3 * P.cornerDelta - 6 * P.cornerDelta ^ 2 := by
      nlinarith
    linarith
  have he0 := P.e_pos.le
  have hL0 := P.L_nonneg
  nlinarith [sq_nonneg (P.L + P.e)]

lemma f_le_three_delta
    (he : 1 / 3 - 1 / 1000 < P.e) :
    P.f <= 3 * P.cornerDelta := by
  have hL := P.e_lt_L_corner he
  rw [P.e_eq_cornerDelta] at hL
  unfold f
  rw [P.alpha_eq_cornerDelta]
  linarith

lemma one_sub_ell_eq : 1 - P.ell = P.f / P.alpha := by
  unfold ell f
  field_simp [P.alpha_pos.ne']

lemma one_sub_ell_le
    (he : 1 / 3 - 1 / 1000 < P.e) :
    1 - P.ell <= 9 * P.cornerDelta := by
  rw [P.one_sub_ell_eq]
  apply (div_le_iff₀ P.alpha_pos).2
  have hf := P.f_le_three_delta he
  have hdelta := P.cornerDelta_pos
  have ha : 1 / 3 <= P.alpha := P.q_gt_third.le.trans P.alpha_gt_q.le
  nlinarith

lemma ell_le_one : P.ell <= 1 := by
  have hEq := P.one_sub_ell_eq
  have hnonneg : 0 <= P.f / P.alpha := div_nonneg P.f_pos.le P.alpha_pos.le
  linarith

lemma y_le_half_corner
    (he : 1 / 3 - 1 / 1000 < P.e) :
    P.y <= 1 / 2 := by
  unfold y
  apply (div_le_iff₀ P.p_pos).2
  have hqSq : P.q ^ 2 <= P.alpha ^ 2 :=
    pow_le_pow_left₀ P.q_nonneg P.alpha_gt_q.le 2
  have hsquare : (2 * P.L) ^ 2 <= P.p ^ 2 := by
    have hLsq := P.L_sq
    rw [P.p_eq_one_sub_q] at hLsq
    rw [P.p_eq_one_sub_q]
    nlinarith [hLsq, hqSq, sq_nonneg (1 - 3 * P.q)]
  have htwo : 2 * P.L <= P.p :=
    (sq_le_sq₀ (mul_nonneg (by norm_num) P.L_nonneg) P.p_pos.le).mp hsquare
  linarith

lemma x_lower_corner : 1 / 2 < P.x := by
  unfold x p
  apply (lt_div_iff₀ (by linarith [P.q_lt_half] : 0 < 1 - P.q)).2
  rw [show P.q = P.alpha - P.d by unfold d; ring,
    P.alpha_eq_cornerDelta]
  have hd : P.d < P.cornerDelta := P.d_lt_cornerDelta
  have hdelta : 0 < P.cornerDelta := P.cornerDelta_pos
  linarith

lemma x_upper_corner
    (he : 1 / 3 - 1 / 1000 < P.e) :
    P.x <= 50113 / 100000 := by
  unfold x p
  apply (div_le_iff₀ (by linarith [P.q_lt_half] : 0 < 1 - P.q)).2
  have hd := P.d_lt_cornerDelta
  have hdelta := P.cornerDelta_le he
  rw [show P.q = P.alpha - P.d by unfold d; ring,
    P.alpha_eq_cornerDelta]
  nlinarith [P.d_pos]

lemma x_pow_fourteen_corner
    (he : 1 / 3 - 1 / 1000 < P.e) :
    P.x ^ 14 < 1 / 15000 := by
  have hx0 : 0 <= P.x := (div_pos P.alpha_pos P.p_pos).le
  have hx := P.x_upper_corner he
  have hp := pow_le_pow_left₀ hx0 hx 14
  norm_num at hp ⊢
  exact hp.trans_lt (by norm_num)

def cornerT : Real := 1 - P.y / P.s

lemma cornerT_eq : P.cornerT = (P.q - P.L) / P.q := by
  unfold cornerT y s
  field_simp [P.p_pos.ne', P.q_pos.ne']

lemma cornerT_nonneg : 0 <= P.cornerT := by
  unfold cornerT
  linarith [P.y_div_s_lt_one]

lemma cornerT_le_one : P.cornerT <= 1 := by
  unfold cornerT
  linarith [P.y_div_s_nonneg]

lemma cornerT_lower
    (he : 1 / 3 - 1 / 1000 < P.e) :
    (299 / 100 : Real) * P.cornerDelta <= P.cornerT := by
  rw [P.cornerT_eq]
  have hgap := P.q_sub_L_ge_delta
  have hqUp : P.q <= 2003 / 6000 :=
    P.alpha_gt_q.le.trans (P.alpha_le_corner he)
  have hdelta := P.cornerDelta_pos
  have hscaled :
      (299 / 100 : Real) * P.cornerDelta * P.q <= P.cornerDelta := by
    have hmul := mul_le_mul_of_nonneg_left hqUp hdelta.le
    nlinarith
  apply (le_div_iff₀ P.q_pos).2
  exact hscaled.trans hgap

lemma cornerT_upper
    (he : 1 / 3 - 1 / 1000 < P.e) :
    P.cornerT <= 9 * P.cornerDelta := by
  rw [P.cornerT_eq]
  have hgapEq : P.q - P.L = P.f - P.d := by
    unfold f d
    ring
  have hgap : P.q - P.L <= 3 * P.cornerDelta := by
    rw [hgapEq]
    linarith [P.f_le_three_delta he, P.d_pos]
  apply (div_le_iff₀ P.q_pos).2
  have hdelta := P.cornerDelta_pos
  have hq := P.q_gt_third
  nlinarith

lemma ell_sq_ge_ninety_nine
    (he : 1 / 3 - 1 / 1000 < P.e) :
    (99 / 100 : Real) <= P.ell ^ 2 := by
  have hu := P.one_sub_ell_le he
  have hdelta := P.cornerDelta_le he
  have hell0 := P.ell_nonneg
  have hell : 1991 / 2000 <= P.ell := by
    linarith
  have hprod : 0 <= (P.ell - 1991 / 2000) *
      (P.ell + 1991 / 2000) := by
    exact mul_nonneg (sub_nonneg.mpr hell) (by positivity)
  nlinarith

lemma y_div_s_pow_twelve_lower
    (he : 1 / 3 - 1 / 1000 < P.e) :
    (47 / 50 : Real) <= (P.y / P.s) ^ 12 := by
  have hbern := one_add_mul_sub_le_pow
    (a := P.y / P.s) (by linarith [P.y_div_s_nonneg] : (-1 : Real) <= P.y / P.s) 12
  have ht := P.cornerT_upper he
  have hdelta := P.cornerDelta_le he
  unfold cornerT at ht
  norm_num at hbern
  nlinarith

lemma G2_lower_corner
    (he : 1 / 3 - 1 / 1000 < P.e) :
    36 * P.cornerDelta <= P.G2 := by
  let r : Real := P.y / P.s
  have hr0 : 0 <= r := by simpa [r] using P.y_div_s_nonneg
  have hr1 : r <= 1 := P.y_div_s_lt_one.le
  have ht0 : 0 <= P.cornerT := P.cornerT_nonneg
  have ht := P.cornerT_lower he
  have hr12 := P.y_div_s_pow_twelve_lower he
  have hpow := nat_mul_pow_le_pow_sub_pow
    (a := (1 : Real)) (b := r) (n := 13) hr0 hr1
  have hpow' : 13 * P.cornerT * r ^ 12 <= 1 - r ^ 13 := by
    simpa [r, cornerT, mul_assoc] using hpow
  have hleft :
      (13 : Real) * ((299 / 100 : Real) * P.cornerDelta) * (47 / 50) <=
        13 * P.cornerT * r ^ 12 := by
    have h13t := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : Real) <= 13)
    exact mul_le_mul h13t hr12 (by norm_num) (by positivity)
  have hell := P.ell_sq_ge_ninety_nine he
  have hsub0 : 0 <= 1 - r ^ 13 :=
    sub_nonneg.mpr (pow_le_one₀ hr0 hr1)
  have hcore :
      (99 / 100 : Real) *
          ((13 : Real) * ((299 / 100 : Real) * P.cornerDelta) * (47 / 50)) <=
        P.ell ^ 2 * (1 - r ^ 13) := by
    have hlow :
        (99 / 100 : Real) *
            ((13 : Real) * ((299 / 100 : Real) * P.cornerDelta) * (47 / 50)) <=
          (99 / 100 : Real) * (1 - r ^ 13) :=
      mul_le_mul_of_nonneg_left (hleft.trans hpow') (by norm_num)
    have hhigh :
        (99 / 100 : Real) * (1 - r ^ 13) <=
          P.ell ^ 2 * (1 - r ^ 13) :=
      mul_le_mul_of_nonneg_right hell hsub0
    exact hlow.trans hhigh
  unfold G2
  change 36 * P.cornerDelta <= P.ell ^ 2 * (1 - r ^ 13)
  calc
    36 * P.cornerDelta <=
        (99 / 100 : Real) *
          ((13 : Real) * ((299 / 100 : Real) * P.cornerDelta) * (47 / 50)) := by
      nlinarith [P.cornerDelta_pos]
    _ <= P.ell ^ 2 * (1 - r ^ 13) := hcore

lemma G2_upper_corner
    (he : 1 / 3 - 1 / 1000 < P.e) :
    P.G2 <= 117 * P.cornerDelta := by
  let r : Real := P.y / P.s
  have hr0 : 0 <= r := by simpa [r] using P.y_div_s_nonneg
  have hr1 : r <= 1 := P.y_div_s_lt_one.le
  have hpow := pow_sub_pow_le_nat_mul
    (a := (1 : Real)) (b := r) (n := 13) hr0 hr1
  have hpow' : 1 - r ^ 13 <= 13 * P.cornerT := by
    simpa [r, cornerT, mul_assoc] using hpow
  have hsub0 : 0 <= 1 - r ^ 13 :=
    sub_nonneg.mpr (pow_le_one₀ hr0 hr1)
  have hellSq : P.ell ^ 2 <= 1 := by
    have hell0 := P.ell_nonneg
    have hell1 := P.ell_le_one
    nlinarith [sq_nonneg (1 - P.ell)]
  unfold G2
  change P.ell ^ 2 * (1 - r ^ 13) <= 117 * P.cornerDelta
  calc
    P.ell ^ 2 * (1 - r ^ 13) <= 1 * (1 - r ^ 13) :=
      mul_le_mul_of_nonneg_right hellSq hsub0
    _ <= 13 * P.cornerT := by simpa using hpow'
    _ <= 13 * (9 * P.cornerDelta) :=
      mul_le_mul_of_nonneg_left (P.cornerT_upper he) (by norm_num)
    _ = 117 * P.cornerDelta := by ring

lemma G2_le_three_fiftieths
    (he : 1 / 3 - 1 / 1000 < P.e) :
    P.G2 <= 3 / 50 := by
  have hG := P.G2_upper_corner he
  have hd := P.cornerDelta_le he
  nlinarith

lemma corner_forcing
    (he : 1 / 3 - 1 / 1000 < P.e) (hR : 0 < P.R) :
    11 * P.cornerDelta < ((P.m - 2 : Nat) : Real) * P.d := by
  have hG0 := P.G2_nonneg
  have hGlo := P.G2_lower_corner he
  have hGup := P.G2_le_three_fiftieths he
  have hden : 0 < P.G2 + 2 := by linarith
  have hlogBase := Real.le_log_one_add_of_nonneg hG0
  have hratio : 34 * P.cornerDelta <= 2 * P.G2 / (P.G2 + 2) := by
    apply (le_div_iff₀ hden).2
    have hdelta := P.cornerDelta_pos
    nlinarith
  have hgateData := P.secant_gate hR
  have hgate : Real.log (1 + P.G2) <
      ((P.m - 2 : Nat) : Real) * P.d / P.q :=
    hgateData.1.trans_le hgateData.2
  have hmain : 34 * P.cornerDelta <
      ((P.m - 2 : Nat) : Real) * P.d / P.q := by
    exact hratio.trans_lt (hlogBase.trans_lt hgate)
  have hmul : 34 * P.cornerDelta * P.q <
      ((P.m - 2 : Nat) : Real) * P.d := by
    exact (lt_div_iff₀ P.q_pos).mp (by simpa [mul_assoc] using hmain)
  have hdelta := P.cornerDelta_pos
  have hq := P.q_gt_third
  nlinarith

lemma q_sub_L_eq_f_sub_d : P.q - P.L = P.f - P.d := by
  unfold f d
  ring

lemma y_eq_ell_mul_x : P.y = P.ell * P.x := by
  unfold y ell x
  field_simp [P.alpha_pos.ne', P.p_pos.ne']

lemma x_sub_s_eq : P.x - P.s = P.d / P.p := by
  unfold x s d
  field_simp [P.p_pos.ne']

lemma s_sub_y_eq : P.s - P.y = (P.q - P.L) / P.p := by
  unfold s y
  field_simp [P.p_pos.ne']

lemma cornerN_le_delta_one_sub_pow :
    P.cornerN <=
      P.cornerDelta * (1 - P.ell ^ (P.m - 1)) := by
  have hgap : P.cornerDelta <= P.q - P.L := by
    simpa [cornerDelta] using P.q_sub_L_ge_delta
  have hd := P.d_lt_cornerDelta.le
  have hellPow0 : 0 <= P.ell ^ (P.m - 1) := pow_nonneg P.ell_nonneg _
  unfold cornerN
  have hmul := mul_le_mul_of_nonneg_right hgap hellPow0
  nlinarith

lemma one_sub_ell_pow_le
    (he : 1 / 3 - 1 / 1000 < P.e) :
    1 - P.ell ^ (P.m - 1) <=
      9 * (P.m : Real) * P.cornerDelta := by
  have hpow := pow_sub_pow_le_nat_mul
    (a := (1 : Real)) (b := P.ell) (n := P.m - 1)
    P.ell_nonneg P.ell_le_one
  have hcast : (((P.m - 1 : Nat) : Real)) <= (P.m : Real) := by
    exact_mod_cast Nat.sub_le P.m 1
  have hu0 : 0 <= 1 - P.ell := sub_nonneg.mpr P.ell_le_one
  have hscale := mul_le_mul_of_nonneg_right hcast hu0
  have hu := P.one_sub_ell_le he
  calc
    1 - P.ell ^ (P.m - 1) <=
        ((P.m - 1 : Nat) : Real) * (1 - P.ell) := by
      simpa [mul_assoc] using hpow
    _ <= (P.m : Real) * (1 - P.ell) := by
      simpa [mul_comm] using hscale
    _ <= (P.m : Real) * (9 * P.cornerDelta) :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = 9 * (P.m : Real) * P.cornerDelta := by ring

lemma cornerN_upper
    (he : 1 / 3 - 1 / 1000 < P.e) :
    P.cornerN <= 9 * (P.m : Real) * P.cornerDelta ^ 2 := by
  have hfirst := P.cornerN_le_delta_one_sub_pow
  have hsecond := mul_le_mul_of_nonneg_left
    (P.one_sub_ell_pow_le he) P.cornerDelta_pos.le
  calc
    P.cornerN <= P.cornerDelta * (1 - P.ell ^ (P.m - 1)) := hfirst
    _ <= P.cornerDelta * (9 * (P.m : Real) * P.cornerDelta) := hsecond
    _ = 9 * (P.m : Real) * P.cornerDelta ^ 2 := by ring

lemma normalized_R_difference :
    P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) =
      (P.x ^ (P.m - 2) - P.s ^ (P.m - 2) -
        P.ell ^ 2 * (P.s ^ (P.m - 2) - P.y ^ (P.m - 2))) /
          P.alpha := by
  rw [P.R_three_geometric, P.three_geometric_coefficient]
  field_simp [P.alpha_pos.ne']
  ring

lemma corner_secant_identity :
    (((P.m - 2 : Nat) : Real) * (P.x - P.s) *
          P.x ^ (P.m - 2 - 1) -
        P.ell ^ 2 * (((P.m - 2 : Nat) : Real) * (P.s - P.y) *
          P.y ^ (P.m - 2 - 1))) /
        P.alpha =
      ((P.m - 2 : Nat) : Real) * P.x ^ (P.m - 3) * P.cornerN /
        (P.alpha * P.p) := by
  have hm : 15 <= P.m := P.m_ge_fifteen
  have hexp : P.m - 2 - 1 = P.m - 3 := by omega
  have hpow :
      P.y ^ (P.m - 3) =
        P.ell ^ (P.m - 3) * P.x ^ (P.m - 3) := by
    rw [P.y_eq_ell_mul_x, mul_pow]
  have hell :
      P.ell ^ 2 * P.ell ^ (P.m - 3) = P.ell ^ (P.m - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hexp, P.x_sub_s_eq, P.s_sub_y_eq, hpow]
  unfold cornerN
  field_simp [P.alpha_pos.ne', P.p_pos.ne']
  have hcombine :
      P.ell ^ 2 * (P.q - P.L) * P.ell ^ (P.m - 3) =
        (P.q - P.L) * P.ell ^ (P.m - 1) := by
    calc
      P.ell ^ 2 * (P.q - P.L) * P.ell ^ (P.m - 3) =
          (P.q - P.L) * (P.ell ^ 2 * P.ell ^ (P.m - 3)) := by ring
      _ = (P.q - P.L) * P.ell ^ (P.m - 1) := by rw [hell]
  rw [hcombine]

lemma normalized_R_le_cornerN :
    P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) <=
      ((P.m - 2 : Nat) : Real) * P.x ^ (P.m - 3) * P.cornerN /
        (P.alpha * P.p) := by
  let n := P.m - 2
  have hxs := pow_sub_pow_le_nat_mul
    (a := P.x) (b := P.s) (n := n) P.s_pos.le P.s_lt_x.le
  have hsy := nat_mul_pow_le_pow_sub_pow
    (a := P.s) (b := P.y) (n := n) P.y_nonneg P.y_lt_s.le
  have hsaf := mul_le_mul_of_nonneg_left hsy (sq_nonneg P.ell)
  rw [P.normalized_R_difference]
  have hdiff :
      P.x ^ n - P.s ^ n - P.ell ^ 2 * (P.s ^ n - P.y ^ n) <=
        (n : Real) * (P.x - P.s) * P.x ^ (n - 1) -
          P.ell ^ 2 * ((n : Real) * (P.s - P.y) * P.y ^ (n - 1)) :=
    sub_le_sub hxs hsaf
  have hdiv := (div_le_div_iff_of_pos_right P.alpha_pos).2 hdiff
  dsimp [n] at hdiv
  exact hdiv.trans_eq P.corner_secant_identity

lemma alpha_mul_p_ge_sixth : 1 / 6 <= P.alpha * P.p := by
  have ha : 1 / 3 <= P.alpha := P.q_gt_third.le.trans P.alpha_gt_q.le
  have hp : 1 / 2 <= P.p := by
    unfold p
    linarith [P.q_lt_half]
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hp)]

lemma normalized_R_corner_upper
    (he : 1 / 3 - 1 / 1000 < P.e) :
    P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) <=
      54 * (P.m : Real) * ((P.m - 2 : Nat) : Real) *
        P.cornerDelta ^ 2 * P.x ^ (P.m - 3) := by
  have hN := P.cornerN_upper he
  have hn0 : 0 <= ((P.m - 2 : Nat) : Real) := by positivity
  have hxpow0 : 0 <= P.x ^ (P.m - 3) :=
    pow_nonneg (div_nonneg P.alpha_nonneg P.p_pos.le) _
  have hscale0 : 0 <= ((P.m - 2 : Nat) : Real) * P.x ^ (P.m - 3) :=
    mul_nonneg hn0 hxpow0
  have hscaled := mul_le_mul_of_nonneg_left hN hscale0
  have hden : 0 < P.alpha * P.p := mul_pos P.alpha_pos P.p_pos
  have hdenInv : 1 / (P.alpha * P.p) <= 6 := by
    rw [div_le_iff₀ hden]
    nlinarith [P.alpha_mul_p_ge_sixth]
  have hnum0 :
      0 <= ((P.m - 2 : Nat) : Real) * P.x ^ (P.m - 3) *
        (9 * (P.m : Real) * P.cornerDelta ^ 2) := by positivity
  calc
    P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) <=
        ((P.m - 2 : Nat) : Real) * P.x ^ (P.m - 3) * P.cornerN /
          (P.alpha * P.p) := P.normalized_R_le_cornerN
    _ <= (((P.m - 2 : Nat) : Real) * P.x ^ (P.m - 3) *
          (9 * (P.m : Real) * P.cornerDelta ^ 2)) /
          (P.alpha * P.p) :=
      div_le_div_of_nonneg_right hscaled hden.le
    _ = (((P.m - 2 : Nat) : Real) * P.x ^ (P.m - 3) *
          (9 * (P.m : Real) * P.cornerDelta ^ 2)) *
          (1 / (P.alpha * P.p)) := by ring
    _ <= (((P.m - 2 : Nat) : Real) * P.x ^ (P.m - 3) *
          (9 * (P.m : Real) * P.cornerDelta ^ 2)) * 6 :=
      mul_le_mul_of_nonneg_left hdenInv hnum0
    _ = 54 * (P.m : Real) * ((P.m - 2 : Nat) : Real) *
        P.cornerDelta ^ 2 * P.x ^ (P.m - 3) := by ring

lemma xi_lt_one_corner
    (he : 1 / 3 - 1 / 1000 < P.e) :
    P.xi < 1 := by
  have ha := P.alpha_le_corner he
  have heLo := P.e_ge_corner he
  have hd := P.d_lt_cornerDelta
  have hdelta := P.cornerDelta_le he
  have hePos := P.e_pos
  have hratio : P.alpha / P.e <= 2003 / 1994 := by
    apply (div_le_iff₀ hePos).2
    nlinarith
  have hratio0 : 0 <= P.alpha / P.e :=
    div_nonneg P.alpha_nonneg P.e_pos.le
  have hratioSq : (P.alpha / P.e) ^ 2 <= (2003 / 1994 : Real) ^ 2 :=
    pow_le_pow_left₀ hratio0 hratio 2
  have hdUp : P.d < 1 / 2000 := hd.trans_le hdelta
  unfold xi
  have heNe := P.e_pos.ne'
  rw [show 4 * P.alpha ^ 2 * P.d / P.e ^ 2 =
      4 * (P.alpha / P.e) ^ 2 * P.d by field_simp [heNe]]
  calc
    4 * (P.alpha / P.e) ^ 2 * P.d <=
        4 * (2003 / 1994 : Real) ^ 2 * P.d :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratioSq (by norm_num)) P.d_pos.le
    _ < 4 * (2003 / 1994 : Real) ^ 2 * (1 / 2000) :=
      mul_lt_mul_of_pos_left hdUp (by positivity)
    _ < 1 := by norm_num

lemma y_pow_corner_upper
    (he : 1 / 3 - 1 / 1000 < P.e) :
    P.y ^ (P.m - 1) <= (1 / 2 : Real) ^ 14 := by
  have hm := P.m_ge_fifteen
  have hm14 : 14 <= P.m - 1 := by omega
  have hyHalf := P.y_le_half_corner he
  have hyPow : P.y ^ (P.m - 1) <= (1 / 2 : Real) ^ (P.m - 1) :=
    pow_le_pow_left₀ P.y_nonneg hyHalf _
  have hhalf0 : (0 : Real) <= 1 / 2 := by norm_num
  have hhalf1 : (1 / 2 : Real) <= 1 := by norm_num
  exact hyPow.trans (pow_le_pow_of_le_one hhalf0 hhalf1 hm14)

lemma one_sub_y_pow_corner
    (he : 1 / 3 - 1 / 1000 < P.e) :
    (9 / 10 : Real) <= 1 - P.y ^ (P.m - 1) := by
  have hy := P.y_pow_corner_upper he
  norm_num at hy ⊢
  linarith

lemma kappa_gt_three_d : 3 * P.d < P.kappa := by
  unfold kappa
  apply (lt_div_iff₀ P.e_pos).2
  have hd := P.d_pos
  have he := P.e_lt_third
  nlinarith

lemma nine_d_sq_le_kappa_sq : 9 * P.d ^ 2 <= P.kappa ^ 2 := by
  have hk := P.kappa_gt_three_d.le
  calc
    9 * P.d ^ 2 = (3 * P.d) ^ 2 := by ring
    _ <= P.kappa ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by norm_num) P.d_pos.le) hk 2

lemma paymentCoeffI_corner_lower
    (he : 1 / 3 - 1 / 1000 < P.e) :
    4 * P.d ^ 2 <= P.paymentCoeffI := by
  have hxsub : (9 / 10 : Real) <= 1 - P.x ^ 14 := by
    linarith [P.x_pow_fourteen_corner he]
  have hysub := P.one_sub_y_pow_corner he
  have hxsub0 : 0 <= 1 - P.x ^ 14 := by linarith
  have hysub0 : 0 <= 1 - P.y ^ (P.m - 1) := by linarith
  have hxyFirst :
      (9 / 10 : Real) * (9 / 10) <=
        (1 - P.x ^ 14) * (1 - P.y ^ (P.m - 1)) := by
    calc
      (9 / 10 : Real) * (9 / 10) <=
          (1 - P.x ^ 14) * (9 / 10) :=
        mul_le_mul_of_nonneg_right hxsub (by norm_num)
      _ <= (1 - P.x ^ 14) * (1 - P.y ^ (P.m - 1)) :=
        mul_le_mul_of_nonneg_left hysub hxsub0
  have hkSq := P.nine_d_sq_le_kappa_sq
  have hxy0 : 0 <= (1 - P.x ^ 14) * (1 - P.y ^ (P.m - 1)) :=
    mul_nonneg hxsub0 hysub0
  have hcore :
      (729 / 100 : Real) * P.d ^ 2 <=
        (1 - P.x ^ 14) * (1 - P.y ^ (P.m - 1)) * P.kappa ^ 2 := by
    calc
      (729 / 100 : Real) * P.d ^ 2 =
          ((9 / 10 : Real) * (9 / 10)) * (9 * P.d ^ 2) := by ring
      _ <= ((1 - P.x ^ 14) * (1 - P.y ^ (P.m - 1))) *
          P.kappa ^ 2 :=
        mul_le_mul hxyFirst hkSq (by positivity) hxy0
  have hfront :
      12 * P.d ^ 2 <=
        2 * (1 - P.x ^ 14) * (1 - P.y ^ (P.m - 1)) * P.kappa ^ 2 := by
    nlinarith
  have hxden : 0 < 1 + P.x := by
    have hx0 : 0 <= P.x := div_nonneg P.alpha_nonneg P.p_pos.le
    linarith
  have hyden : 0 < 1 + P.y := by linarith [P.y_nonneg]
  have hxBase : (1 + P.x) * (1 + P.y) <= 3 := by
    have hx1 := P.x_lt_one.le
    have hy := P.y_le_half_corner he
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy)]
  have hxi0 := P.xi_pos.le
  have hxiDen : 0 < 1 + 2 * P.xi := by positivity
  have hden : 0 < (1 + P.x) * (1 + P.y) * (1 + 2 * P.xi) := by positivity
  have hdenUpper :
      (1 + P.x) * (1 + P.y) * (1 + 2 * P.xi) <=
        3 * (1 + 4 * P.xi) := by
    calc
      (1 + P.x) * (1 + P.y) * (1 + 2 * P.xi) <=
          3 * (1 + 2 * P.xi) :=
        mul_le_mul_of_nonneg_right hxBase hxiDen.le
      _ <= 3 * (1 + 4 * P.xi) := by nlinarith
  unfold paymentCoeffI
  apply (le_div_iff₀ hden).2
  calc
    4 * P.d ^ 2 * ((1 + P.x) * (1 + P.y) * (1 + 2 * P.xi)) <=
        4 * P.d ^ 2 * (3 * (1 + 4 * P.xi)) :=
      mul_le_mul_of_nonneg_left hdenUpper (by positivity)
    _ = 12 * P.d ^ 2 * (1 + 4 * P.xi) := by ring
    _ <= (2 * (1 - P.x ^ 14) * (1 - P.y ^ (P.m - 1)) * P.kappa ^ 2) *
        (1 + 4 * P.xi) :=
      mul_le_mul_of_nonneg_right hfront (by positivity)
    _ = 2 * (1 - P.x ^ 14) * (1 - P.y ^ (P.m - 1)) * P.kappa ^ 2 *
        (1 + 4 * P.xi) := by ring

lemma sqrt_two_alpha_corner_lower :
    (4 / 5 : Real) <= Real.sqrt (2 * P.alpha) := by
  have hleft : (0 : Real) <= 4 / 5 := by norm_num
  have hright : 0 <= 2 * P.alpha :=
    mul_nonneg (by norm_num) P.alpha_nonneg
  apply (Real.le_sqrt hleft hright).2
  nlinarith [P.q_gt_third, P.alpha_gt_q]

lemma alpha_cube_le_eighth : P.alpha ^ 3 <= 1 / 8 := by
  have ha0 := P.alpha_nonneg
  have ha := P.alpha_lt_half.le
  have hpow := pow_le_pow_left₀ ha0 ha 3
  norm_num at hpow ⊢
  exact hpow

lemma paymentCoeffII_corner_lower
    (he : 1 / 3 - 1 / 1000 < P.e) :
    P.cornerDelta * P.d <= P.paymentCoeffII := by
  have hroot := P.sqrt_two_alpha_corner_lower
  have hysub := P.one_sub_y_pow_corner he
  have hysub0 : 0 <= 1 - P.y ^ (P.m - 1) := by linarith
  have hf : P.cornerDelta <= P.f := by
    have hgap : P.d + P.cornerDelta <= P.f := by
      simpa [cornerDelta] using P.f_ge_d_add_delta
    linarith [P.d_pos]
  have hroot0 : 0 <= Real.sqrt (2 * P.alpha) := Real.sqrt_nonneg _
  have hrootY :
      (4 / 5 : Real) * (9 / 10) <=
        Real.sqrt (2 * P.alpha) * (1 - P.y ^ (P.m - 1)) := by
    calc
      (4 / 5 : Real) * (9 / 10) <=
          Real.sqrt (2 * P.alpha) * (9 / 10) :=
        mul_le_mul_of_nonneg_right hroot (by norm_num)
      _ <= Real.sqrt (2 * P.alpha) * (1 - P.y ^ (P.m - 1)) :=
        mul_le_mul_of_nonneg_left hysub hroot0
  have hrootY0 :
      0 <= Real.sqrt (2 * P.alpha) * (1 - P.y ^ (P.m - 1)) :=
    mul_nonneg hroot0 hysub0
  have hcore :
      (18 / 25 : Real) * P.cornerDelta * P.d <=
        Real.sqrt (2 * P.alpha) * (1 - P.y ^ (P.m - 1)) * P.f * P.d := by
    have hfScaled := mul_le_mul hrootY hf P.cornerDelta_pos.le hrootY0
    have hdScaled := mul_le_mul_of_nonneg_right hfScaled P.d_pos.le
    have hcoef : (18 / 25 : Real) = (4 / 5) * (9 / 10) := by norm_num
    rw [hcoef]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hdScaled
  have hyden : 0 < 1 + P.y := by linarith [P.y_nonneg]
  have hbase : P.alpha ^ 3 * (1 + P.y) <= 3 / 16 := by
    have ha3 := P.alpha_cube_le_eighth
    have hy := P.y_le_half_corner he
    have hyBound : 1 + P.y <= 3 / 2 := by linarith
    calc
      P.alpha ^ 3 * (1 + P.y) <= (1 / 8 : Real) * (1 + P.y) :=
        mul_le_mul_of_nonneg_right ha3 (by linarith [P.y_nonneg])
      _ <= (1 / 8 : Real) * (3 / 2) :=
        mul_le_mul_of_nonneg_left hyBound (by norm_num)
      _ = 3 / 16 := by norm_num
  have hxiNum : 0 < 4 * P.xi + 1 := by linarith [P.xi_pos]
  have hxiDen : 0 < 4 * P.xi + 2 := by linarith [P.xi_pos]
  have hxiFactor : 4 * P.xi + 2 <= 2 * (4 * P.xi + 1) := by
    nlinarith [P.xi_pos]
  have hden : 0 < P.alpha ^ 3 * (1 + P.y) * (4 * P.xi + 2) := by
    exact mul_pos (mul_pos (pow_pos P.alpha_pos 3) hyden) hxiDen
  unfold paymentCoeffII
  apply (le_div_iff₀ hden).2
  calc
    P.cornerDelta * P.d *
        (P.alpha ^ 3 * (1 + P.y) * (4 * P.xi + 2)) <=
      P.cornerDelta * P.d *
        ((3 / 16 : Real) * (2 * (4 * P.xi + 1))) := by
      apply mul_le_mul_of_nonneg_left
      · calc
          P.alpha ^ 3 * (1 + P.y) * (4 * P.xi + 2) <=
              (3 / 16 : Real) * (4 * P.xi + 2) :=
            mul_le_mul_of_nonneg_right hbase hxiDen.le
          _ <= (3 / 16 : Real) * (2 * (4 * P.xi + 1)) :=
            mul_le_mul_of_nonneg_left hxiFactor (by norm_num)
      · exact mul_nonneg P.cornerDelta_pos.le P.d_pos.le
    _ = (3 / 8 : Real) * P.cornerDelta * P.d * (4 * P.xi + 1) := by ring
    _ <= (18 / 25 : Real) * P.cornerDelta * P.d * (4 * P.xi + 1) := by
      have hcoef :
          (3 / 8 : Real) * (P.cornerDelta * P.d) <=
            (18 / 25 : Real) * (P.cornerDelta * P.d) :=
        mul_le_mul_of_nonneg_right (by norm_num)
          (mul_nonneg P.cornerDelta_pos.le P.d_pos.le)
      exact mul_le_mul_of_nonneg_right (by simpa [mul_assoc] using hcoef) hxiNum.le
    _ <= (Real.sqrt (2 * P.alpha) * (1 - P.y ^ (P.m - 1)) * P.f * P.d) *
        (4 * P.xi + 1) :=
      mul_le_mul_of_nonneg_right hcore hxiNum.le
    _ = Real.sqrt (2 * P.alpha) * (1 - P.y ^ (P.m - 1)) * P.f * P.d *
        (4 * P.xi + 1) := by ring

/-- The cubic polynomial loss in the corner estimate is dominated by the
geometric decay. -/
lemma corner_cubic_decay
    (he : 1 / 3 - 1 / 1000 < P.e) :
    ((P.m - 2 : Nat) : Real) ^ 3 * P.x ^ (P.m - 3) <= 1 := by
  have hm : 15 <= P.m := P.m_ge_fifteen
  have hn : 13 <= P.m - 2 := by omega
  have hx0 : 0 <= P.x := (div_pos P.alpha_pos P.p_pos).le
  have hx := P.x_upper_corner he
  have hdecay := cubic_power_decay hx0 hx hn
  have hexp : P.m - 2 - 1 = P.m - 3 := by omega
  rw [hexp] at hdecay
  have hxpow : P.x ^ 12 <= (50113 / 100000 : Real) ^ 12 :=
    pow_le_pow_left₀ hx0 hx 12
  calc
    ((P.m - 2 : Nat) : Real) ^ 3 * P.x ^ (P.m - 3) <=
        13 ^ 3 * P.x ^ 12 := hdecay
    _ <= 13 ^ 3 * (50113 / 100000 : Real) ^ 12 :=
      mul_le_mul_of_nonneg_left hxpow (by norm_num)
    _ <= 1 := by norm_num

lemma normalized_R_le_corner_paymentI
    (he : 1 / 3 - 1 / 1000 < P.e) (hR : 0 < P.R) :
    P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) <=
      (P.m : Real) * P.paymentCoeffI := by
  let n : Real := ((P.m - 2 : Nat) : Real)
  have hm : 15 <= P.m := P.m_ge_fifteen
  have hnNat : 13 <= P.m - 2 := by omega
  have hn : (13 : Real) <= n := by
    change (13 : Real) <= ((P.m - 2 : Nat) : Real)
    exact_mod_cast hnNat
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnSqPos : 0 < n ^ 2 := sq_pos_of_pos hnPos
  have hdelta0 : 0 <= P.cornerDelta := P.cornerDelta_pos.le
  have hxpow0 : 0 <= P.x ^ (P.m - 3) :=
    pow_nonneg (div_nonneg P.alpha_nonneg P.p_pos.le) _
  have hdecay := P.corner_cubic_decay he
  change n ^ 3 * P.x ^ (P.m - 3) <= 1 at hdecay
  have hpoly :
      54 * n * P.x ^ (P.m - 3) <= 484 / n ^ 2 := by
    apply (le_div_iff₀ hnSqPos).2
    calc
      (54 * n * P.x ^ (P.m - 3)) * n ^ 2 =
          54 * (n ^ 3 * P.x ^ (P.m - 3)) := by ring
      _ <= 54 * 1 := mul_le_mul_of_nonneg_left hdecay (by norm_num)
      _ <= 484 := by norm_num
  have hforce := P.corner_forcing he hR
  change 11 * P.cornerDelta < n * P.d at hforce
  have hforceSq : 121 * P.cornerDelta ^ 2 <= n ^ 2 * P.d ^ 2 := by
    have hsquare := pow_le_pow_left₀
      (mul_nonneg (by norm_num) hdelta0) hforce.le 2
    nlinarith
  have hforceDiv : 121 * P.cornerDelta ^ 2 / n ^ 2 <= P.d ^ 2 := by
    apply (div_le_iff₀ hnSqPos).2
    nlinarith
  have hcore :
      54 * n * P.cornerDelta ^ 2 * P.x ^ (P.m - 3) <= 4 * P.d ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_right hpoly (sq_nonneg P.cornerDelta)
    calc
      54 * n * P.cornerDelta ^ 2 * P.x ^ (P.m - 3) =
          (54 * n * P.x ^ (P.m - 3)) * P.cornerDelta ^ 2 := by ring
      _ <= (484 / n ^ 2) * P.cornerDelta ^ 2 := hscaled
      _ = 4 * (121 * P.cornerDelta ^ 2 / n ^ 2) := by ring
      _ <= 4 * P.d ^ 2 := mul_le_mul_of_nonneg_left hforceDiv (by norm_num)
  have hm0 : 0 <= (P.m : Real) := by positivity
  have hupper := P.normalized_R_corner_upper he
  change P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) <=
      54 * (P.m : Real) * n * P.cornerDelta ^ 2 * P.x ^ (P.m - 3) at hupper
  calc
    P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) <=
        54 * (P.m : Real) * n * P.cornerDelta ^ 2 * P.x ^ (P.m - 3) := hupper
    _ <= (P.m : Real) * (4 * P.d ^ 2) := by
      have := mul_le_mul_of_nonneg_left hcore hm0
      nlinarith
    _ <= (P.m : Real) * P.paymentCoeffI :=
      mul_le_mul_of_nonneg_left (P.paymentCoeffI_corner_lower he) hm0

lemma normalized_R_le_corner_paymentII
    (he : 1 / 3 - 1 / 1000 < P.e) (hR : 0 < P.R) :
    P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) <=
      (P.m : Real) * P.paymentCoeffII := by
  let n : Real := ((P.m - 2 : Nat) : Real)
  have hm : 15 <= P.m := P.m_ge_fifteen
  have hnNat : 13 <= P.m - 2 := by omega
  have hn : (13 : Real) <= n := by
    change (13 : Real) <= ((P.m - 2 : Nat) : Real)
    exact_mod_cast hnNat
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hdelta0 : 0 <= P.cornerDelta := P.cornerDelta_pos.le
  have hxpow0 : 0 <= P.x ^ (P.m - 3) :=
    pow_nonneg (div_nonneg P.alpha_nonneg P.p_pos.le) _
  have hz0 : 0 <= n ^ 2 * P.x ^ (P.m - 3) :=
    mul_nonneg (sq_nonneg n) hxpow0
  have hdecay := P.corner_cubic_decay he
  change n ^ 3 * P.x ^ (P.m - 3) <= 1 at hdecay
  have hthirteen : 13 * (n ^ 2 * P.x ^ (P.m - 3)) <= 1 := by
    calc
      13 * (n ^ 2 * P.x ^ (P.m - 3)) <=
          n * (n ^ 2 * P.x ^ (P.m - 3)) :=
        mul_le_mul_of_nonneg_right hn hz0
      _ = n ^ 3 * P.x ^ (P.m - 3) := by ring
      _ <= 1 := hdecay
  have hpoly : 54 * n ^ 2 * P.x ^ (P.m - 3) <= 11 := by
    nlinarith
  have hforce := P.corner_forcing he hR
  change 11 * P.cornerDelta < n * P.d at hforce
  have hforceScaled : 11 * P.cornerDelta ^ 2 <= n * (P.cornerDelta * P.d) := by
    have := mul_le_mul_of_nonneg_left hforce.le hdelta0
    nlinarith
  have hcore :
      54 * n * P.cornerDelta ^ 2 * P.x ^ (P.m - 3) <=
        P.cornerDelta * P.d := by
    have hpolyScaled := mul_le_mul_of_nonneg_right hpoly (sq_nonneg P.cornerDelta)
    have hmul :
        (54 * n * P.cornerDelta ^ 2 * P.x ^ (P.m - 3)) * n <=
          (P.cornerDelta * P.d) * n := by
      calc
        (54 * n * P.cornerDelta ^ 2 * P.x ^ (P.m - 3)) * n =
            (54 * n ^ 2 * P.x ^ (P.m - 3)) * P.cornerDelta ^ 2 := by ring
        _ <= 11 * P.cornerDelta ^ 2 := hpolyScaled
        _ <= n * (P.cornerDelta * P.d) := hforceScaled
        _ = (P.cornerDelta * P.d) * n := by ring
    exact le_of_mul_le_mul_right hmul hnPos
  have hm0 : 0 <= (P.m : Real) := by positivity
  have hupper := P.normalized_R_corner_upper he
  change P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) <=
      54 * (P.m : Real) * n * P.cornerDelta ^ 2 * P.x ^ (P.m - 3) at hupper
  calc
    P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) <=
        54 * (P.m : Real) * n * P.cornerDelta ^ 2 * P.x ^ (P.m - 3) := hupper
    _ <= (P.m : Real) * (P.cornerDelta * P.d) := by
      have := mul_le_mul_of_nonneg_left hcore hm0
      nlinarith
    _ <= (P.m : Real) * P.paymentCoeffII :=
      mul_le_mul_of_nonneg_left (P.paymentCoeffII_corner_lower he) hm0

/-- Headline analytic estimate for the Turan-corner sliver of Zone C. -/
theorem turan_corner_bound
    (he : 1 / 3 - 1 / 1000 < P.e) :
    P.R <= P.C * psi P.xi P.rho := by
  by_cases hR : 0 < P.R
  · have hnormalized :
        P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) <=
          P.C * psi P.xi P.rho /
            (P.alpha ^ 3 * P.p ^ (P.m - 2)) := by
      by_cases hgate : 2 * P.rhoLo * P.xi <= 1
      · exact (P.normalized_R_le_corner_paymentI he hR).trans
          (P.paymentCoeffI_le_normalized_psi hgate)
      · have hgate' : 1 < 2 * P.rhoLo * P.xi := lt_of_not_ge hgate
        exact (P.normalized_R_le_corner_paymentII he hR).trans
          (P.paymentCoeffII_le_normalized_psi hgate')
    exact (div_le_div_iff_of_pos_right P.normalized_payment_pos).mp hnormalized
  · have hR0 : P.R <= 0 := le_of_not_gt hR
    have hpsi0 : 0 <= psi P.xi P.rho := psi_nonneg P.rho_pos.le
    exact hR0.trans (mul_nonneg P.C_pos.le hpsi0)

end AdmissibleParams
end OddCycleBound.RegionII.Scalar
