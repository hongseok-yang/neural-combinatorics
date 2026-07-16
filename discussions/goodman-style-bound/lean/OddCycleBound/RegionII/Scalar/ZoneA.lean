import OddCycleBound.RegionII.Scalar.ZoneBReduction

/-!
# Zone A

The analytic small-`e`, `xi >= 1` part of the corrected Region-II proof.
The defect and payment normalization is imported from `ZoneBReduction`; it
is domain-free and is shared by both zones.
-/

noncomputable section

namespace OddCycleBound.RegionII.Scalar

def sigmaA (e : Real) : Real := ((51 / 25 : Real) * e) ^ 6

def gammaA (ell eps e : Real) : Real :=
  2 * ell + eps + (51 / 100 : Real) * e + sigmaA e

def a0A (e : Real) : Real :=
  (28527 / 10000 : Real) * Real.sqrt e +
    (51 / 100 : Real) * e + sigmaA e

/-- The quadratic truncation of Bernoulli's inequality, with a real
coefficient chosen to make successor algebra transparent. -/
lemma quadratic_bernoulli {u : Real} (hu : 0 <= u) (n : Nat) :
    1 + (n : Real) * u + ((n : Real) * ((n : Real) - 1) / 2) * u ^ 2 <=
      (1 + u) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hone : 0 <= 1 + u := by linarith
      have hmul := mul_le_mul_of_nonneg_right ih hone
      have hcoef : 0 <= (n : Real) * ((n : Real) - 1) / 2 := by
        cases n with
        | zero => norm_num
        | succ k =>
            have hk : (0 : Real) <= k := by positivity
            push_cast
            nlinarith
      have hcubic : 0 <=
          ((n : Real) * ((n : Real) - 1) / 2) * u ^ 3 :=
        mul_nonneg hcoef (pow_nonneg hu 3)
      have halg :
          (1 + ((n + 1 : Nat) : Real) * u +
              (((n + 1 : Nat) : Real) * (((n + 1 : Nat) : Real) - 1) / 2) *
                u ^ 2) +
              ((n : Real) * ((n : Real) - 1) / 2) * u ^ 3 =
            (1 + (n : Real) * u +
              ((n : Real) * ((n : Real) - 1) / 2) * u ^ 2) * (1 + u) := by
        push_cast
        ring
      rw [← halg] at hmul
      exact (le_add_of_nonneg_right hcubic).trans hmul

namespace AdmissibleParams

variable (P : AdmissibleParams)

def uA : Real := 1 - P.x

def zA : Real := ((P.m - 2 : Nat) : Real) * P.uA

lemma sigmaA_nonneg : 0 <= sigmaA P.e := by
  unfold sigmaA
  positivity

lemma alpha_ge_zoneA (he : P.e <= 1 / 60) :
    59 / 120 <= P.alpha := by
  rw [P.alpha_eq_chart]
  unfold chartAlpha
  linarith

lemma kappa_le_one : P.kappa <= 1 := by
  have hk := P.kappa_le_max
  have hden : 0 < 1 + P.e := by linarith [P.e_pos]
  unfold kappaMax at hk
  exact hk.trans ((div_le_one hden).2 (by linarith [P.e_pos]))

lemma p_le_zoneA (he : P.e <= 1 / 60) :
    P.p <= 21 / 40 := by
  rw [P.p_eq_chart]
  unfold chartP chartAlpha
  have hk := P.kappa_le_one
  have he0 := P.e_pos.le
  nlinarith [mul_le_mul_of_nonneg_right hk he0]

lemma x_ge_zoneA (he : P.e <= 1 / 60) :
    59 / 63 <= P.x := by
  unfold x
  apply (le_div_iff₀ P.p_pos).2
  have ha := P.alpha_ge_zoneA he
  have hp := P.p_le_zoneA he
  nlinarith

lemma e_div_alpha_le_zoneA (he : P.e <= 1 / 60) :
    P.e / P.alpha <= (51 / 25 : Real) * P.e := by
  have ha := P.alpha_ge_zoneA he
  have he0 := P.e_pos.le
  rw [div_le_iff₀ P.alpha_pos]
  nlinarith [mul_le_mul_of_nonneg_right ha he0]

lemma ratio_zoneA_nonneg : 0 <= P.e / P.alpha :=
  div_nonneg P.e_pos.le P.alpha_pos.le

lemma ratio_zoneA_le_one : P.e / P.alpha <= 1 :=
  (div_le_one P.alpha_pos).2 P.e_lt_alpha.le

lemma lambdaII_le_zoneA_tail (he : P.e <= 1 / 60) :
    P.lambdaII <=
      P.x ^ (P.m - 2) * sigmaA P.e /
        ((P.m : Real) * P.kappa) := by
  let r := P.m / 2
  let z := P.e / P.alpha
  let t := Real.sqrt z
  have hm : 2 * r + 1 = P.m := by
    simpa [r] using Nat.two_mul_div_two_add_one_of_odd P.m_odd
  have hm15 := P.m_ge_fifteen
  have hr6 : 6 <= r - 1 := by omega
  have hz0 : 0 <= z := by simpa [z] using P.ratio_zoneA_nonneg
  have hz1 : z <= 1 := by simpa [z] using P.ratio_zoneA_le_one
  have ht0 : 0 <= t := Real.sqrt_nonneg _
  have ht1 : t <= 1 := Real.sqrt_le_one.mpr hz1
  have hzpow : z ^ (r - 1) <= z ^ 6 :=
    pow_le_pow_of_le_one hz0 hz1 hr6
  have hsmall0 : 0 <= (51 / 25 : Real) * P.e :=
    mul_nonneg (by norm_num) P.e_pos.le
  have hzsmall : z <= (51 / 25 : Real) * P.e := by
    simpa [z] using P.e_div_alpha_le_zoneA he
  have hz6 : z ^ 6 <= sigmaA P.e := by
    unfold sigmaA
    exact pow_le_pow_left₀ hz0 hzsmall 6
  have htail : z ^ (r - 1) * t <= sigmaA P.e := by
    calc
      z ^ (r - 1) * t <= z ^ 6 * 1 :=
        mul_le_mul hzpow ht1 ht0 (pow_nonneg hz0 _)
      _ = z ^ 6 := by ring
      _ <= sigmaA P.e := hz6
  have hmpos : (0 : Real) < P.m := by exact_mod_cast (show 0 < P.m by omega)
  have hden : 0 <= (P.m : Real) * P.kappa :=
    (mul_pos hmpos P.kappa_pos).le
  rw [P.lambdaII_normalized]
  change P.x ^ (P.m - 2) * z ^ (r - 1) * t /
      ((P.m : Real) * P.kappa) <= _
  apply div_le_div_of_nonneg_right _ hden
  simpa [mul_assoc] using
    mul_le_mul_of_nonneg_left htail (pow_nonneg P.x_pos.le (P.m - 2))

lemma reduced_sum_pos_of_R_pos (hR : 0 < P.R) :
    0 < P.reducedBracketII + P.lambdaII := by
  have hupper : 0 < P.defectUpperII := hR.trans_le P.R_le_defectUpperII
  have hprod : 0 < P.normalizationII *
      (P.reducedBracketII + P.lambdaII) := by
    rw [P.normalizationII_mul_reduced_sum]
    exact hupper
  rcases (mul_pos_iff.mp hprod) with h | h
  · exact h.2
  · exact False.elim ((not_lt_of_ge P.normalizationII_pos.le) h.1)

lemma zoneA_positive_threshold
    (he : P.e <= 1 / 60) (hR : 0 < P.R) :
    P.x * (1 + P.kappa) - sigmaA P.e <
      P.kappa * ((P.m - 1 : Nat) : Real) := by
  have hsum := P.reduced_sum_pos_of_R_pos hR
  have htail := P.lambdaII_le_zoneA_tail he
  have hupper : 0 < P.reducedBracketII +
      P.x ^ (P.m - 2) * sigmaA P.e /
        ((P.m : Real) * P.kappa) := by
    linarith
  let pref := P.x ^ (P.m - 2) /
    ((P.m : Real) * P.kappa * P.x)
  let bracket := P.kappa * ((P.m - 1 : Nat) : Real) -
    P.x * (P.kappa + 1) + P.x * sigmaA P.e
  have hm0 : (P.m : Real) ≠ 0 := by
    have hm15 := P.m_ge_fifteen
    exact_mod_cast (show P.m ≠ 0 by omega)
  have hfac : P.reducedBracketII +
      P.x ^ (P.m - 2) * sigmaA P.e /
        ((P.m : Real) * P.kappa) = pref * bracket := by
    dsimp [pref, bracket]
    unfold reducedBracketII
    field_simp [hm0, P.kappa_pos.ne', P.x_pos.ne']
  have hpref : 0 < pref := by
    dsimp [pref]
    have hm15 := P.m_ge_fifteen
    have hmpos : (0 : Real) < P.m := by
      exact_mod_cast (show 0 < P.m by omega)
    exact div_pos (pow_pos P.x_pos _) <|
      mul_pos (mul_pos hmpos P.kappa_pos)
        P.x_pos
  have hbracket : 0 < bracket := by
    rw [hfac] at hupper
    rcases (mul_pos_iff.mp hupper) with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge hpref.le) h.1)
  have hx1 := P.x_lt_one.le
  have hsigma0 := P.sigmaA_nonneg
  dsimp [bracket] at hbracket
  have hxsigma : P.x * sigmaA P.e <= sigmaA P.e :=
    mul_le_of_le_one_left hsigma0 hx1
  linarith

lemma sigmaA_lt_zoneA_margin (he : P.e <= 1 / 60) :
    sigmaA P.e < 13 / 2000 := by
  have hbase : (51 / 25 : Real) * P.e <= 17 / 500 := by
    nlinarith
  have hbase0 : 0 <= (51 / 25 : Real) * P.e :=
    mul_nonneg (by norm_num) P.e_pos.le
  have hpow : sigmaA P.e <= (17 / 500 : Real) ^ 6 := by
    unfold sigmaA
    exact pow_le_pow_left₀ hbase0 hbase 6
  norm_num at hpow ⊢
  linarith

lemma zoneA_kappa_threshold
    (he : P.e <= 1 / 60) (hR : 0 < P.R) :
    93 / 100 / (((P.m - 1 : Nat) : Real)) <= P.kappa := by
  have hfirst := P.zoneA_positive_threshold he hR
  have hx := P.x_ge_zoneA he
  have hsigma := P.sigmaA_lt_zoneA_margin he
  have hxterm : P.x <= P.x * (1 + P.kappa) := by
    nlinarith [mul_pos P.x_pos P.kappa_pos]
  have hprod : 93 / 100 <
      P.kappa * ((P.m - 1 : Nat) : Real) := by
    nlinarith
  have hm15 := P.m_ge_fifteen
  have hm1 : (0 : Real) < ((P.m - 1 : Nat) : Real) := by
    exact_mod_cast (show 0 < P.m - 1 by omega)
  exact (div_le_iff₀ hm1).2 hprod.le

lemma epsII_le_zoneA_linear
    (he : P.e <= 1 / 60) (hR : 0 < P.R) :
    P.epsII <= (2781 / 10000 : Real) * P.m * P.e := by
  have hk := P.zoneA_kappa_threshold he hR
  have hm15 := P.m_ge_fifteen
  have hm1Nat : P.m - 1 <= P.m := Nat.sub_le _ _
  have hm1 : (((P.m - 1 : Nat) : Real)) <= (P.m : Real) := by
    exact_mod_cast hm1Nat
  have hk0 := P.kappa_pos.le
  have hmk : 93 / 100 <= (P.m : Real) * P.kappa := by
    have hden : (0 : Real) < ((P.m - 1 : Nat) : Real) := by
      exact_mod_cast (show 0 < P.m - 1 by omega)
    have hbase : 93 / 100 <=
        P.kappa * ((P.m - 1 : Nat) : Real) := by
      exact (div_le_iff₀ hden).mp hk
    calc
      93 / 100 <= P.kappa * ((P.m - 1 : Nat) : Real) := hbase
      _ <= P.kappa * (P.m : Real) :=
        mul_le_mul_of_nonneg_left hm1 hk0
      _ = (P.m : Real) * P.kappa := by ring
  have hone : (1 : Real) <= 1 + P.rho := by linarith [P.rho_pos]
  have hebase : 59 / 60 <= 1 - P.e := by linarith
  have hsq : (59 / 60 : Real) ^ 2 <= (1 - P.e) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hebase 2
  have hfactor :
      4 * (59 / 60 : Real) ^ 2 * 1 * (93 / 100) <=
        4 * (1 - P.e) ^ 2 * (1 + P.rho) *
          ((P.m : Real) * P.kappa) := by
    exact mul_le_mul
      (mul_le_mul
        (mul_le_mul (le_refl (4 : Real)) hsq (by positivity) (by norm_num))
        hone (by norm_num)
        (mul_nonneg (by norm_num) (sq_nonneg _)))
      hmk (by norm_num)
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _))
        (by linarith [P.rho_pos]))
  have hconstant :
      1 <= (2781 / 10000 : Real) *
        (4 * (59 / 60 : Real) ^ 2 * 1 * (93 / 100)) := by
    norm_num
  have htotal :
      1 <= (2781 / 10000 : Real) *
        (4 * (1 - P.e) ^ 2 * (1 + P.rho) *
          ((P.m : Real) * P.kappa)) :=
    hconstant.trans (mul_le_mul_of_nonneg_left hfactor (by norm_num))
  have hden : 0 < 4 * (1 - P.e) ^ 2 * (1 + P.rho) * P.kappa := by
    exact mul_pos
      (mul_pos
        (mul_pos (by norm_num) (sq_pos_of_pos P.one_sub_e_pos))
        P.one_add_rho_pos)
      P.kappa_pos
  unfold epsII
  rw [div_le_iff₀ hden]
  have he0 := P.e_pos.le
  nlinarith [mul_le_mul_of_nonneg_right htotal he0]

lemma uA_pos : 0 < P.uA := by
  unfold uA
  exact sub_pos.mpr P.x_lt_one

lemma uA_nonneg : 0 <= P.uA := P.uA_pos.le

lemma uA_lt_one : P.uA < 1 := by
  unfold uA
  linarith [P.x_pos]

lemma zA_pos : 0 < P.zA := by
  unfold zA
  have hm15 := P.m_ge_fifteen
  have hn : (0 : Real) < ((P.m - 2 : Nat) : Real) := by
    exact_mod_cast (show 0 < P.m - 2 by omega)
  exact mul_pos hn P.uA_pos

lemma x_pow_le_zoneA_rational :
    P.x ^ (P.m - 2) <=
      1 / (1 + P.zA + (6 / 13 : Real) * P.zA ^ 2) := by
  let n := P.m - 2
  let u := P.uA
  have hm15 := P.m_ge_fifteen
  have hn13 : 13 <= n := by dsimp [n]; omega
  have hu0 : 0 <= u := by simpa [u] using P.uA_nonneg
  have hx0 : 0 <= P.x := P.x_pos.le
  have hxu : P.x + u = 1 := by dsimp [u, uA]; ring
  have hinvBase : 1 + u <= 1 / P.x := by
    rw [le_div_iff₀ P.x_pos]
    dsimp [u, uA]
    nlinarith [sq_nonneg (1 - P.x)]
  have hpowMono : (1 + u) ^ n <= (1 / P.x) ^ n :=
    pow_le_pow_left₀ (by linarith) hinvBase n
  have hquad := quadratic_bernoulli hu0 n
  have hnR : (13 : Real) <= n := by exact_mod_cast hn13
  have hcoef : (6 / 13 : Real) * (n : Real) ^ 2 <=
      (n : Real) * ((n : Real) - 1) / 2 := by
    nlinarith [mul_nonneg (by norm_num : (0 : Real) <= 1 / 26)
      (sub_nonneg.mpr hnR)]
  have hdesired :
      1 + (n : Real) * u +
          (6 / 13 : Real) * ((n : Real) * u) ^ 2 <=
        (1 / P.x) ^ n := by
    calc
      1 + (n : Real) * u +
          (6 / 13 : Real) * ((n : Real) * u) ^ 2 <=
          1 + (n : Real) * u +
            ((n : Real) * ((n : Real) - 1) / 2) * u ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg u)]
      _ <= (1 + u) ^ n := hquad
      _ <= (1 / P.x) ^ n := hpowMono
  let D := 1 + (n : Real) * u +
    (6 / 13 : Real) * ((n : Real) * u) ^ 2
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hcancel : (1 / P.x) ^ n * P.x ^ n = 1 := by
    rw [← mul_pow]
    field_simp [P.x_pos.ne']
    simp
  have hprod := mul_le_mul_of_nonneg_right hdesired (pow_nonneg hx0 n)
  rw [hcancel] at hprod
  have hxdiv : P.x ^ n <= 1 / D := by
    rw [le_div_iff₀ hDpos]
    simpa [mul_comm, D] using hprod
  simpa [zA, n, u] using hxdiv

lemma ell_le_zoneA_sqrt (he : P.e <= 1 / 60) :
    P.ell <= (7131 / 5000 : Real) * Real.sqrt P.e := by
  have hsharp : P.e / P.alpha <= (120 / 59 : Real) * P.e := by
    rw [div_le_iff₀ P.alpha_pos]
    have ha := P.alpha_ge_zoneA he
    nlinarith [mul_le_mul_of_nonneg_right ha P.e_pos.le]
  have hchart : P.ell ^ 2 <= P.e / P.alpha := by
    have hs := P.ell_sq_le_chart
    rw [P.one_sub_e_eq_two_alpha] at hs
    field_simp [P.alpha_pos.ne'] at hs
    exact hs
  have hellSq : P.ell ^ 2 <= (120 / 59 : Real) * P.e :=
    hchart.trans hsharp
  have hsqrtSq : Real.sqrt P.e ^ 2 = P.e :=
    Real.sq_sqrt P.e_pos.le
  have hcoef : (120 / 59 : Real) <= (7131 / 5000 : Real) ^ 2 := by
    norm_num
  have hright0 : 0 <= (7131 / 5000 : Real) * Real.sqrt P.e := by
    positivity
  apply (sq_le_sq₀ P.ell_nonneg hright0).mp
  rw [mul_pow, hsqrtSq]
  nlinarith [mul_le_mul_of_nonneg_right hcoef P.e_pos.le]

lemma ell_le_zoneA_decimal (he : P.e <= 1 / 60) :
    P.ell <= 921 / 5000 := by
  have hell := P.ell_le_zoneA_sqrt he
  have hsqrt : Real.sqrt P.e <= 1291 / 10000 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · nlinarith
  nlinarith

lemma y_pow_le_sigmaA (he : P.e <= 1 / 60) :
    P.y ^ (P.m - 1) <= sigmaA P.e := by
  have hm15 := P.m_ge_fifteen
  have hm14 : 14 <= P.m - 1 := by omega
  have hyell : P.y <= P.ell := P.y_le_ell
  have hell1 : P.ell <= 1 := (P.ell_le_zoneA_decimal he).trans (by norm_num)
  have hfirst : P.y ^ (P.m - 1) <= P.ell ^ 14 := by
    calc
      P.y ^ (P.m - 1) <= P.y ^ 14 :=
        pow_le_pow_of_le_one P.y_nonneg
          (P.y_le_ell.trans hell1) hm14
      _ <= P.ell ^ 14 := pow_le_pow_left₀ P.y_nonneg hyell 14
  have hchart : P.ell ^ 2 <= P.e / P.alpha := by
    have hs := P.ell_sq_le_chart
    rw [P.one_sub_e_eq_two_alpha] at hs
    field_simp [P.alpha_pos.ne'] at hs
    exact hs
  have hratio : P.ell ^ 2 <= (51 / 25 : Real) * P.e :=
    hchart.trans (P.e_div_alpha_le_zoneA he)
  have hbase0 : 0 <= (51 / 25 : Real) * P.e :=
    mul_nonneg (by norm_num) P.e_pos.le
  have hbase1 : (51 / 25 : Real) * P.e <= 1 := by
    nlinarith
  have hpow7 : (P.ell ^ 2) ^ 7 <=
      ((51 / 25 : Real) * P.e) ^ 7 :=
    pow_le_pow_left₀ (sq_nonneg _) hratio 7
  have h76 : ((51 / 25 : Real) * P.e) ^ 7 <= sigmaA P.e := by
    unfold sigmaA
    exact pow_le_pow_of_le_one hbase0 hbase1 (by norm_num)
  calc
    P.y ^ (P.m - 1) <= P.ell ^ 14 := hfirst
    _ = (P.ell ^ 2) ^ 7 := by ring
    _ <= ((51 / 25 : Real) * P.e) ^ 7 := hpow7
    _ <= sigmaA P.e := h76

lemma sqrt_one_sub_e_lower (he : P.e <= 1 / 60) :
    1 - (51 / 100 : Real) * P.e <= Real.sqrt (1 - P.e) := by
  have hleft : 0 <= 1 - (51 / 100 : Real) * P.e := by
    nlinarith [P.e_pos]
  apply (Real.le_sqrt hleft P.one_sub_e_pos.le).2
  have hfactor : 0 <= 1 / 50 - (2601 / 10000 : Real) * P.e := by
    nlinarith
  have hprod := mul_nonneg P.e_pos.le hfactor
  nlinarith

lemma ell_lt_one_global : P.ell < 1 := by
  unfold ell
  exact (div_lt_one P.alpha_pos).2 P.L_lt_alpha

lemma ratio_one_sub_ell_lower :
    1 - 2 * P.ell <= (1 - P.ell) / (1 + P.y) := by
  rw [le_div_iff₀ P.one_add_y_pos]
  have hy := P.y_le_ell
  have hell0 := P.ell_nonneg
  have hell1 := P.ell_lt_one_global.le
  have hy0 := P.y_nonneg
  nlinarith [mul_nonneg hell0 hy0]

lemma piII_lower_gamma
    (he : P.e <= 1 / 60) (hxi : 1 <= P.xi) :
    1 - gammaA P.ell P.epsII P.e <= P.piII := by
  let a := (51 / 100 : Real) * P.e
  let b := 2 * P.ell
  let c := sigmaA P.e
  let d := P.epsII
  have ha0 : 0 <= a := by
    dsimp [a]
    exact mul_nonneg (by norm_num) P.e_pos.le
  have hb0 : 0 <= b := by
    dsimp [b]
    exact mul_nonneg (by norm_num) P.ell_nonneg
  have hc0 : 0 <= c := by simpa [c] using P.sigmaA_nonneg
  have hd0 : 0 <= d := by
    dsimp [d, epsII]
    exact div_nonneg P.e_pos.le <| mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _)) P.one_add_rho_pos.le)
      P.kappa_pos.le
  have ha1 : a <= 1 := by dsimp [a]; nlinarith
  have hb1 : b <= 1 := by
    dsimp [b]
    nlinarith [P.ell_le_zoneA_decimal he]
  have hc1 : c <= 1 := by
    dsimp [c]
    exact (P.sigmaA_lt_zoneA_margin he).le.trans (by norm_num)
  have hd1 : d <= 1 := by
    dsimp [d]
    exact (P.epsII_le_quarter hxi).trans (by norm_num)
  have hsqrt : 1 - a <= Real.sqrt (1 - P.e) := by
    simpa [a] using P.sqrt_one_sub_e_lower he
  have hratio : 1 - b <= (1 - P.ell) / (1 + P.y) := by
    simpa [b] using P.ratio_one_sub_ell_lower
  have hypow : 1 - c <= 1 - P.y ^ (P.m - 1) := by
    dsimp [c]
    linarith [P.y_pow_le_sigmaA he]
  have heps : 1 - d = 1 - P.epsII := by rfl
  have hratio0 : 0 <= (1 - P.ell) / (1 + P.y) :=
    div_nonneg (sub_nonneg.mpr P.ell_lt_one_global.le) P.one_add_y_pos.le
  have hpow0 : 0 <= 1 - P.y ^ (P.m - 1) := P.one_sub_y_pow_pos.le
  have heps0 : 0 <= 1 - P.epsII := by linarith
  have hact12 : 0 <= Real.sqrt (1 - P.e) *
      ((1 - P.ell) / (1 + P.y)) :=
    mul_nonneg (Real.sqrt_nonneg _) hratio0
  have hact123 : 0 <= Real.sqrt (1 - P.e) *
      ((1 - P.ell) / (1 + P.y)) *
        (1 - P.y ^ (P.m - 1)) := mul_nonneg hact12 hpow0
  have hlower :
      (1 - a) * (1 - b) * (1 - c) * (1 - d) <=
        Real.sqrt (1 - P.e) * ((1 - P.ell) / (1 + P.y)) *
          (1 - P.y ^ (P.m - 1)) * (1 - P.epsII) := by
    have h12 := mul_le_mul hsqrt hratio (by linarith : 0 <= 1 - b)
      (Real.sqrt_nonneg (1 - P.e))
    have h123 := mul_le_mul h12 hypow (by linarith : 0 <= 1 - c) hact12
    exact mul_le_mul h123 (le_refl _) (by linarith : 0 <= 1 - d) hact123
  have h2 : 1 - (a + b) <= (1 - a) * (1 - b) := by
    nlinarith [mul_nonneg ha0 hb0]
  have h3 : 1 - (a + b + c) <= (1 - a) * (1 - b) * (1 - c) := by
    have hm := mul_le_mul_of_nonneg_right h2 (by linarith : 0 <= 1 - c)
    nlinarith [mul_nonneg (add_nonneg ha0 hb0) hc0]
  have h4 : 1 - (a + b + c + d) <=
      (1 - a) * (1 - b) * (1 - c) * (1 - d) := by
    have hm := mul_le_mul_of_nonneg_right h3 (by linarith : 0 <= 1 - d)
    nlinarith [mul_nonneg (add_nonneg (add_nonneg ha0 hb0) hc0) hd0]
  unfold piII
  have hreassoc :
      Real.sqrt (1 - P.e) * (1 - P.ell) *
          (1 - P.y ^ (P.m - 1)) * (1 - P.epsII) / (1 + P.y) =
        Real.sqrt (1 - P.e) * ((1 - P.ell) / (1 + P.y)) *
          (1 - P.y ^ (P.m - 1)) * (1 - P.epsII) := by ring
  rw [hreassoc]
  change 1 - (b + d + a + c) <= _
  linarith [h4.trans hlower]

lemma uA_lower_zoneA (he : P.e <= 1 / 60) :
    (40 / 21 : Real) * (1 + P.kappa) * P.e <= P.uA := by
  have hk := P.kappa_le_one
  have hden0 : 0 < 1 + P.e + 2 * P.kappa * P.e := by
    have hterm : 0 <= 2 * P.kappa * P.e :=
      mul_nonneg (mul_nonneg (by norm_num) P.kappa_pos.le) P.e_pos.le
    linarith [P.e_pos]
  have hden : 1 + P.e + 2 * P.kappa * P.e <= 21 / 20 := by
    have hmul := mul_le_mul_of_nonneg_right hk P.e_pos.le
    nlinarith
  have hcoef : (40 / 21 : Real) *
      (1 + P.e + 2 * P.kappa * P.e) <= 2 := by
    nlinarith
  have hcommon : 0 <= (1 + P.kappa) * P.e :=
    mul_nonneg (by linarith [P.kappa_pos]) P.e_pos.le
  unfold uA
  rw [P.one_sub_x_chart]
  rw [le_div_iff₀ hden0]
  have hmul := mul_le_mul_of_nonneg_right hcoef hcommon
  nlinarith

lemma m_mul_e_le_zA (he : P.e <= 1 / 60) :
    (P.m : Real) * P.e <= (3029 / 5000 : Real) * P.zA := by
  let n := P.m - 2
  have hm15 := P.m_ge_fifteen
  have hn13 : 13 <= n := by dsimp [n]; omega
  have hnR : (13 : Real) <= n := by exact_mod_cast hn13
  have hmEq : ((n : Nat) : Real) + 2 = (P.m : Real) := by
    dsimp [n]
    exact_mod_cast (show P.m - 2 + 2 = P.m by omega)
  have hu := P.uA_lower_zoneA he
  have hk1 : (1 : Real) <= 1 + P.kappa := by linarith [P.kappa_pos]
  have hlower : (40 / 21 : Real) * P.e <= P.uA := by
    have h := (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk1 (by norm_num)) P.e_pos.le).trans hu
    simpa [mul_assoc] using h
  have hz : (n : Real) * ((40 / 21 : Real) * P.e) <= P.zA := by
    unfold zA
    exact mul_le_mul_of_nonneg_left hlower (by positivity)
  have hcoef : (n : Real) + 2 <=
      (3029 / 5000 : Real) * (n : Real) * (40 / 21 : Real) := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hcoef P.e_pos.le
  rw [hmEq] at hscaled
  calc
    (P.m : Real) * P.e <=
        (3029 / 5000 : Real) *
          ((n : Real) * ((40 / 21 : Real) * P.e)) := by
      nlinarith
    _ <= (3029 / 5000 : Real) * P.zA :=
      mul_le_mul_of_nonneg_left hz (by norm_num)

lemma epsII_le_zoneA_z
    (he : P.e <= 1 / 60) (hR : 0 < P.R) :
    P.epsII <= (843 / 5000 : Real) * P.zA := by
  have heps := P.epsII_le_zoneA_linear he hR
  have hT := P.m_mul_e_le_zA he
  calc
    P.epsII <= (2781 / 10000 : Real) * ((P.m : Real) * P.e) := by
      simpa [mul_assoc] using heps
    _ <= (2781 / 10000 : Real) *
        ((3029 / 5000 : Real) * P.zA) :=
      mul_le_mul_of_nonneg_left hT (by norm_num)
    _ <= (843 / 5000 : Real) * P.zA := by
      have hz := P.zA_pos.le
      nlinarith

lemma one_div_x_upper_zoneA (he : P.e <= 1 / 60) :
    1 / P.x <=
      1 + (1017 / 500 : Real) * (1 + P.kappa) * P.e := by
  have hden : 59 / 60 <= 1 - P.e := by linarith
  have hcoef : 2 / (1 - P.e) <= (1017 / 500 : Real) := by
    rw [div_le_iff₀ P.one_sub_e_pos]
    nlinarith
  have hcommon : 0 <= (1 + P.kappa) * P.e :=
    mul_nonneg (by linarith [P.kappa_pos]) P.e_pos.le
  have hmul := mul_le_mul_of_nonneg_right hcoef hcommon
  calc
    1 / P.x = 1 + (2 / (1 - P.e)) *
        ((1 + P.kappa) * P.e) := by
      rw [P.one_div_x_chart]
      ring
    _ <= 1 + (1017 / 500 : Real) *
        ((1 + P.kappa) * P.e) := by linarith
    _ = 1 + (1017 / 500 : Real) * (1 + P.kappa) * P.e := by ring

lemma reciprocal_error_le_zA (he : P.e <= 1 / 60) :
    (1017 / 500 : Real) * (1 + P.kappa) * P.e <=
      (411 / 5000 : Real) * P.zA := by
  let n := P.m - 2
  have hm15 := P.m_ge_fifteen
  have hn13 : 13 <= n := by dsimp [n]; omega
  have hu := P.uA_lower_zoneA he
  have hz : (n : Real) *
      ((40 / 21 : Real) * (1 + P.kappa) * P.e) <= P.zA := by
    unfold zA
    exact mul_le_mul_of_nonneg_left hu (by positivity)
  have hcoef : (1017 / 500 : Real) <=
      (411 / 5000 : Real) * (n : Real) * (40 / 21 : Real) := by
    have hnR : (13 : Real) <= n := by exact_mod_cast hn13
    nlinarith
  have hcommon : 0 <= (1 + P.kappa) * P.e :=
    mul_nonneg (by linarith [P.kappa_pos]) P.e_pos.le
  have hscaled := mul_le_mul_of_nonneg_right hcoef hcommon
  calc
    (1017 / 500 : Real) * (1 + P.kappa) * P.e <=
        (411 / 5000 : Real) *
          ((n : Real) * ((40 / 21 : Real) *
            (1 + P.kappa) * P.e)) := by
      nlinarith
    _ <= (411 / 5000 : Real) * P.zA :=
      mul_le_mul_of_nonneg_left hz (by norm_num)

lemma gammaA_upper
    (he : P.e <= 1 / 60) (hxi : 1 <= P.xi) (hR : 0 < P.R) :
    gammaA P.ell P.epsII P.e <=
      a0A P.e + min (1 / 4) ((843 / 5000 : Real) * P.zA) := by
  have hell := P.ell_le_zoneA_sqrt he
  have hepsQuarter := P.epsII_le_quarter hxi
  have hepsZ := P.epsII_le_zoneA_z he hR
  have heps : P.epsII <=
      min (1 / 4) ((843 / 5000 : Real) * P.zA) :=
    le_min hepsQuarter hepsZ
  have hell2 : 2 * P.ell <=
      (28527 / 10000 : Real) * Real.sqrt P.e := by
    nlinarith [Real.sqrt_nonneg P.e]
  unfold gammaA a0A
  linarith

lemma m_mul_kappa_lower_zoneA
    (he : P.e <= 1 / 60) (hR : 0 < P.R) :
    93 / 100 <= (P.m : Real) * P.kappa := by
  have hk := P.zoneA_kappa_threshold he hR
  have hm15 := P.m_ge_fifteen
  have hm1pos : (0 : Real) < ((P.m - 1 : Nat) : Real) := by
    exact_mod_cast (show 0 < P.m - 1 by omega)
  have hbase : 93 / 100 <=
      P.kappa * ((P.m - 1 : Nat) : Real) :=
    (div_le_iff₀ hm1pos).mp hk
  have hmcast : (((P.m - 1 : Nat) : Real)) <= (P.m : Real) := by
    exact_mod_cast (Nat.sub_le P.m 1)
  calc
    93 / 100 <= P.kappa * ((P.m - 1 : Nat) : Real) := hbase
    _ <= P.kappa * (P.m : Real) :=
      mul_le_mul_of_nonneg_left hmcast P.kappa_pos.le
    _ = (P.m : Real) * P.kappa := by ring

lemma lambdaII_le_sigma_mul_xpow
    (he : P.e <= 1 / 60) (hR : 0 < P.R) :
    P.lambdaII <= sigmaA P.e * P.x ^ (P.m - 2) := by
  let r := P.m / 2
  let z := P.e / P.alpha
  let t := Real.sqrt z
  have hm : 2 * r + 1 = P.m := by
    simpa [r] using Nat.two_mul_div_two_add_one_of_odd P.m_odd
  have hm15 := P.m_ge_fifteen
  have hr6 : 6 <= r - 1 := by omega
  have hz0 : 0 <= z := by simpa [z] using P.ratio_zoneA_nonneg
  have hz1 : z <= 1 := by simpa [z] using P.ratio_zoneA_le_one
  have hzsmall : z <= (51 / 25 : Real) * P.e := by
    simpa [z] using P.e_div_alpha_le_zoneA he
  have hsmall : (51 / 25 : Real) * P.e <= 17 / 500 := by nlinarith
  have ht0 : 0 <= t := Real.sqrt_nonneg _
  have ht19 : t <= 19 / 100 := by
    dsimp [t]
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · exact hzsmall.trans hsmall |>.trans (by norm_num)
  have hzpow : z ^ (r - 1) <= z ^ 6 :=
    pow_le_pow_of_le_one hz0 hz1 hr6
  have hz6 : z ^ 6 <= sigmaA P.e := by
    unfold sigmaA
    exact pow_le_pow_left₀ hz0 hzsmall 6
  have hnum : z ^ (r - 1) * t <= sigmaA P.e * (19 / 100) :=
    mul_le_mul (hzpow.trans hz6) ht19 ht0 (P.sigmaA_nonneg)
  have hmk := P.m_mul_kappa_lower_zoneA he hR
  have hmkpos : 0 < (P.m : Real) * P.kappa := by
    have hmpos : (0 : Real) < P.m := by exact_mod_cast (show 0 < P.m by omega)
    exact mul_pos hmpos P.kappa_pos
  have hratio : z ^ (r - 1) * t /
      ((P.m : Real) * P.kappa) <= sigmaA P.e := by
    rw [div_le_iff₀ hmkpos]
    calc
      z ^ (r - 1) * t <= sigmaA P.e * (19 / 100) := hnum
      _ <= sigmaA P.e * ((P.m : Real) * P.kappa) :=
        mul_le_mul_of_nonneg_left
          ((by norm_num : (19 / 100 : Real) <= 93 / 100).trans hmk)
          P.sigmaA_nonneg
  rw [P.lambdaII_normalized]
  change P.x ^ (P.m - 2) * z ^ (r - 1) * t /
      ((P.m : Real) * P.kappa) <= _
  calc
    P.x ^ (P.m - 2) * z ^ (r - 1) * t /
        ((P.m : Real) * P.kappa) =
      P.x ^ (P.m - 2) *
        (z ^ (r - 1) * t / ((P.m : Real) * P.kappa)) := by ring
    _ <= P.x ^ (P.m - 2) * sigmaA P.e :=
      mul_le_mul_of_nonneg_left hratio (pow_nonneg P.x_pos.le _)
    _ = sigmaA P.e * P.x ^ (P.m - 2) := by ring

lemma zoneA_product_lower :
    (14571 / 2500 : Real) <=
      (1 + P.kappa) * (2 + 1 / P.kappa) := by
  have hk := P.kappa_pos
  have hsq := sq_nonneg (P.kappa - (7071 / 10000 : Real))
  have hpoly : (14571 / 2500 : Real) * P.kappa <=
      (1 + P.kappa) * (2 * P.kappa + 1) := by
    nlinarith
  have hre : (1 + P.kappa) * (2 + 1 / P.kappa) =
      ((1 + P.kappa) * (2 * P.kappa + 1)) / P.kappa := by
    field_simp [P.kappa_pos.ne']
  rw [hre, le_div_iff₀ P.kappa_pos]
  exact hpoly

lemma reciprocal_gap_lower_zoneA (he : P.e <= 1 / 60) :
    (277 / 25 : Real) * P.e /
        (P.zA + (39 / 5 : Real) * P.e) <=
      (2 + 1 / P.kappa) / (P.m : Real) := by
  let n := P.m - 2
  let A := 2 + 1 / P.kappa
  have hm15 := P.m_ge_fifteen
  have hn13 : 13 <= n := by dsimp [n]; omega
  have hn0 : (0 : Real) <= n := by positivity
  have hmpos : (0 : Real) < P.m := by exact_mod_cast (show 0 < P.m by omega)
  have hA : 3 <= A := by
    dsimp [A]
    have hinv : 1 <= 1 / P.kappa := by
      rw [le_div_iff₀ P.kappa_pos]
      simpa using P.kappa_le_one
    linarith
  have hA0 : 0 <= A := by linarith
  have hu := P.uA_lower_zoneA he
  have hu' : (19047 / 10000 : Real) * (1 + P.kappa) * P.e <= P.uA := by
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num :
        (19047 / 10000 : Real) <= 40 / 21)
        (by linarith [P.kappa_pos] : 0 <= 1 + P.kappa)) P.e_pos.le).trans hu
  have hz : (19047 / 10000 : Real) * (n : Real) *
      (1 + P.kappa) * P.e <= P.zA := by
    unfold zA
    have h := mul_le_mul_of_nonneg_left hu' hn0
    nlinarith
  have hprod := P.zoneA_product_lower
  have hprodScaled :
      (19047 / 10000 : Real) * (n : Real) *
          (14571 / 2500 : Real) * P.e <=
        A * P.zA := by
    have hscale0 : 0 <=
        (19047 / 10000 : Real) * (n : Real) * P.e :=
      mul_nonneg (mul_nonneg (by norm_num) hn0) P.e_pos.le
    have h1 := mul_le_mul_of_nonneg_left hprod
      hscale0
    have h2 := mul_le_mul_of_nonneg_left hz hA0
    dsimp [A] at h1 h2 ⊢
    nlinarith
  have hsecond : (3 : Real) * (39 / 5) * P.e <=
      A * ((39 / 5 : Real) * P.e) := by
    have h := mul_le_mul_of_nonneg_right hA
      (mul_nonneg (by norm_num : (0 : Real) <= 39 / 5) P.e_pos.le)
    simpa [mul_assoc] using h
  have hnR : (13 : Real) <= n := by exact_mod_cast hn13
  have hcoef : (277 / 25 : Real) * ((n : Real) + 2) <=
      (19047 / 10000 : Real) * (n : Real) * (14571 / 2500 : Real) +
        3 * (39 / 5 : Real) := by
    have hslope : 0 <=
        (19047 / 10000 : Real) * (14571 / 2500) - 277 / 25 := by
      norm_num
    have hbase : 0 <=
        (19047 / 10000 : Real) * 13 * (14571 / 2500) + 3 * (39 / 5) -
          (277 / 25) * (13 + 2) := by
      norm_num
    have hid :
        (19047 / 10000 : Real) * (n : Real) * (14571 / 2500) +
            3 * (39 / 5) - (277 / 25) * ((n : Real) + 2) =
          ((19047 / 10000 : Real) * 13 * (14571 / 2500) +
            3 * (39 / 5) - (277 / 25) * (13 + 2)) +
          ((19047 / 10000 : Real) * (14571 / 2500) - 277 / 25) *
            ((n : Real) - 13) := by
      ring
    have hnonneg : 0 <=
        ((19047 / 10000 : Real) * (n : Real) * (14571 / 2500) +
          3 * (39 / 5)) - (277 / 25) * ((n : Real) + 2) := by
      rw [hid]
      exact add_nonneg hbase (mul_nonneg hslope (sub_nonneg.mpr hnR))
    exact sub_nonneg.mp hnonneg
  have hmEq : ((n : Nat) : Real) + 2 = (P.m : Real) := by
    dsimp [n]
    exact_mod_cast (show P.m - 2 + 2 = P.m by omega)
  have hcross : (277 / 25 : Real) * (P.m : Real) * P.e <=
      A * (P.zA + (39 / 5 : Real) * P.e) := by
    have hc := mul_le_mul_of_nonneg_right hcoef P.e_pos.le
    rw [hmEq] at hc
    nlinarith [hprodScaled, hsecond]
  have hden : 0 < P.zA + (39 / 5 : Real) * P.e := by
    have hterm : 0 < (39 / 5 : Real) * P.e :=
      mul_pos (by norm_num) P.e_pos
    linarith [P.zA_pos]
  rw [div_le_div_iff₀ hden hmpos]
  dsimp [A] at hcross
  nlinarith

lemma bracket_upper_zoneA (he : P.e <= 1 / 60) :
    (((P.m - 1 : Nat) : Real) / ((P.m : Real) * P.x) -
        (1 + 1 / P.kappa) / (P.m : Real)) <=
      1 + (411 / 5000 : Real) * P.zA -
        (277 / 25 : Real) * P.e /
          (P.zA + (39 / 5 : Real) * P.e) := by
  have hm15 := P.m_ge_fifteen
  have hmpos : (0 : Real) < P.m := by exact_mod_cast (show 0 < P.m by omega)
  have hx : P.x <= 1 := P.x_lt_one.le
  have honeInv : 1 <= 1 / P.x := by
    rw [le_div_iff₀ P.x_pos]
    simpa using hx
  have hfirst :
      (((P.m - 1 : Nat) : Real) / ((P.m : Real) * P.x) -
          (1 + 1 / P.kappa) / (P.m : Real)) <=
        1 / P.x - (2 + 1 / P.kappa) / (P.m : Real) := by
    have hm1 : ((P.m - 1 : Nat) : Real) + 1 = (P.m : Real) := by
      exact_mod_cast (show P.m - 1 + 1 = P.m by omega)
    have hdiff : 0 <= (1 / P.x - 1) / (P.m : Real) :=
      div_nonneg (by linarith) hmpos.le
    calc
      ((P.m - 1 : Nat) : Real) / ((P.m : Real) * P.x) -
          (1 + 1 / P.kappa) / (P.m : Real) =
        (1 / P.x - (2 + 1 / P.kappa) / (P.m : Real)) -
          ((1 / P.x - 1) / (P.m : Real)) := by
        field_simp [hmpos.ne', P.x_pos.ne']
        nlinarith
      _ <= 1 / P.x - (2 + 1 / P.kappa) / (P.m : Real) := by
        linarith
  have hinv := P.one_div_x_upper_zoneA he
  have herr := P.reciprocal_error_le_zA he
  have hgap := P.reciprocal_gap_lower_zoneA he
  linarith

lemma sigmaA_le_tiny_e (he : P.e <= 1 / 60) :
    sigmaA P.e <= (1 / 10000000 : Real) * P.e := by
  let b := (51 / 25 : Real) * P.e
  have hb0 : 0 <= b := by
    dsimp [b]
    exact mul_nonneg (by norm_num) P.e_pos.le
  have hb : b <= 17 / 500 := by dsimp [b]; nlinarith
  have hb5 : b ^ 5 <= (17 / 500 : Real) ^ 5 :=
    pow_le_pow_left₀ hb0 hb 5
  have he0 := P.e_pos.le
  unfold sigmaA
  change b ^ 6 <= (1 / 10000000 : Real) * P.e
  rw [show b ^ 6 = b ^ 5 * ((51 / 25 : Real) * P.e) by
    dsimp [b]; ring]
  have hfactor0 : 0 <= (51 / 25 : Real) * P.e :=
    mul_nonneg (by norm_num) he0
  have hmul := mul_le_mul_of_nonneg_right hb5
    hfactor0
  calc
    b ^ 5 * ((51 / 25 : Real) * P.e) <=
        (17 / 500 : Real) ^ 5 * ((51 / 25 : Real) * P.e) := hmul
    _ <= (1 / 10000000 : Real) * P.e := by
      have hc : (17 / 500 : Real) ^ 5 * (51 / 25) <=
          1 / 10000000 := by norm_num
      have hce := mul_le_mul_of_nonneg_right hc he0
      simpa [mul_assoc] using hce

lemma sqrt_e_le_zoneA (he : P.e <= 1 / 60) :
    Real.sqrt P.e <= 1291 / 10000 := by
  apply (Real.sqrt_le_iff).2
  constructor
  · norm_num
  · nlinarith

lemma a0A_le_zoneA (he : P.e <= 1 / 60) :
    a0A P.e <= 471 / 1250 := by
  have hsqrt := P.sqrt_e_le_zoneA he
  have hsigma := P.sigmaA_le_tiny_e he
  unfold a0A
  nlinarith

end AdmissibleParams

set_option maxHeartbeats 1000000 in
/-- The exact-rational three-range check in the corrected Zone-A proof. -/
theorem zoneA_scalar_battle
    {e z gamma : Real}
    (he0 : 0 < e) (he : e <= 1 / 60) (hz : 0 < z)
    (hgamma : gamma <=
      a0A e + min (1 / 4) ((843 / 5000 : Real) * z))
    (ha0 : a0A e <= 471 / 1250)
    (hsigma : sigmaA e <= (1 / 10000000 : Real) * e) :
    1 + (411 / 5000 : Real) * z -
          (277 / 25 : Real) * e / (z + (39 / 5 : Real) * e) + sigmaA e <=
      (1 - gamma) * (1 + z + (6 / 13 : Real) * z ^ 2) := by
  let s := Real.sqrt e
  let D := 1 + z + (6 / 13 : Real) * z ^ 2
  let frac := (277 / 25 : Real) * e / (z + (39 / 5 : Real) * e)
  let F := z * ((4589 / 5000 : Real) - gamma) +
    (6 / 13 : Real) * (1 - gamma) * z ^ 2 + frac - gamma - sigmaA e
  have hs0 : 0 <= s := Real.sqrt_nonneg _
  have hspos : 0 < s := Real.sqrt_pos.2 he0
  have hsSq : s ^ 2 = e := by
    dsimp [s]
    exact Real.sq_sqrt he0.le
  have hsUpper : s <= 1291 / 10000 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · nlinarith
  have hsig0 : 0 <= sigmaA e := by unfold sigmaA; positivity
  have hsigSmall : sigmaA e < 13 / 2000 := by
    have h := hsigma.trans (mul_le_mul_of_nonneg_left he (by norm_num))
    norm_num at h ⊢
    linarith
  have hden : 0 < z + (39 / 5 : Real) * e := by
    have ht : 0 < (39 / 5 : Real) * e := mul_pos (by norm_num) he0
    linarith
  have hfrac0 : 0 <= frac := by
    dsimp [frac]
    exact div_nonneg (mul_nonneg (by norm_num) he0.le) hden.le
  have hDpos : 0 < D := by
    dsimp [D]
    have hz0 := hz.le
    have hsq0 := sq_nonneg z
    nlinarith
  have hidentity :
      (1 - gamma) * D -
          (1 + (411 / 5000 : Real) * z - frac + sigmaA e) = F := by
    dsimp [D, F]
    ring
  have hF : 0 < F := by
    by_cases hz1 : z <= 1
    · -- Range 1: 0 < z <= 1.
      have hgammaZ : gamma <= a0A e + (843 / 5000 : Real) * z :=
        hgamma.trans (add_le_add (le_refl _) (min_le_right _ _))
      let H := z * ((4589 / 5000 : Real) - gamma) +
        (6 / 13 : Real) * (1 - gamma) * z ^ 2 - gamma
      have hH : (1862 / 5000 : Real) * z - a0A e <= H := by
        let a := a0A e
        let b : Real := 843 / 5000
        let c : Real := 6 / 13
        have hza : 0 <= z * ((471 / 1250 : Real) - a) :=
          mul_nonneg hz.le (sub_nonneg.mpr ha0)
        have hcoef : 0 <= c * (1 - a) - b - b * c * z := by
          dsimp [a, b, c]
          nlinarith
        have hzcoef : 0 <= z ^ 2 * (c * (1 - a) - b - b * c * z) :=
          mul_nonneg (sq_nonneg z) hcoef
        have hupperMul : gamma * D <= (a + b * z) * D :=
          mul_le_mul_of_nonneg_right hgammaZ hDpos.le
        have hid :
            (z * (4589 / 5000 : Real) + c * z ^ 2 -
                (a + b * z) * D) - ((1862 / 5000 : Real) * z - a) =
              z * ((471 / 1250 : Real) - a) +
                z ^ 2 * (c * (1 - a) - b - b * c * z) := by
          dsimp [D, a, b, c]
          ring
        dsimp [H, D] at hupperMul ⊢
        nlinarith [hza, hzcoef, hid]
      have hFlower :
          (1862 / 5000 : Real) * z + frac - a0A e - sigmaA e <= F := by
        dsimp [F, H] at hH ⊢
        linarith
      let t := z + (39 / 5 : Real) * e
      have htpos : 0 < t := by simpa [t] using hden
      have hconst : 0 <=
          4 * (1862 / 5000 : Real) * (277 / 25) -
            (20313 / 5000 : Real) ^ 2 := by
        norm_num
      have hsqComp := sq_nonneg
        (2 * (1862 / 5000 : Real) * t - (20313 / 5000 : Real) * s)
      have hcross :
          (20313 / 5000 : Real) * s * t <=
            (1862 / 5000 : Real) * t ^ 2 + (277 / 25 : Real) * e := by
        have hid :
            4 * (1862 / 5000 : Real) *
                ((1862 / 5000 : Real) * t ^ 2 -
                  (20313 / 5000 : Real) * s * t + (277 / 25 : Real) * e) =
              (2 * (1862 / 5000 : Real) * t -
                  (20313 / 5000 : Real) * s) ^ 2 +
                (4 * (1862 / 5000 : Real) * (277 / 25) -
                  (20313 / 5000 : Real) ^ 2) * s ^ 2 := by
          nlinarith [hsSq]
        have hrhs : 0 <=
            (2 * (1862 / 5000 : Real) * t -
                (20313 / 5000 : Real) * s) ^ 2 +
              (4 * (1862 / 5000 : Real) * (277 / 25) -
                (20313 / 5000 : Real) ^ 2) * s ^ 2 :=
          add_nonneg hsqComp (mul_nonneg hconst (sq_nonneg s))
        nlinarith [hid]
      have hamgm :
          (20313 / 5000 : Real) * s <=
            (1862 / 5000 : Real) * t + (277 / 25 : Real) * e / t := by
        calc
          (20313 / 5000 : Real) * s <=
              ((1862 / 5000 : Real) * t ^ 2 + (277 / 25 : Real) * e) / t :=
            (le_div_iff₀ htpos).2 hcross
          _ = (1862 / 5000 : Real) * t + (277 / 25 : Real) * e / t := by
            field_simp [htpos.ne']
      have hpair :
          (1862 / 5000 : Real) * z + frac >=
            (20313 / 5000 : Real) * s - (3631 / 1250 : Real) * e := by
        dsimp [t, frac] at hamgm ⊢
        nlinarith
      have ha0Exact : a0A e =
          (28527 / 10000 : Real) * s + (51 / 100 : Real) * e + sigmaA e := by
        rfl
      have hmain :
          (12099 / 10000 : Real) * s -
              (8537 / 2500 : Real) * e - 2 * sigmaA e <= F := by
        rw [ha0Exact] at hFlower
        nlinarith [hpair]
      have hsigE : 2 * sigmaA e <= (1 / 5000000 : Real) * e := by
        nlinarith
      have hbracket : 0 < (12099 / 10000 : Real) -
          (17074001 / 5000000 : Real) * s := by
        nlinarith
      have hpositive : 0 <
          (12099 / 10000 : Real) * s -
            (17074001 / 5000000 : Real) * e := by
        rw [← hsSq]
        nlinarith [mul_pos hspos hbracket]
      linarith
    · have hzOne : 1 < z := lt_of_not_ge hz1
      by_cases hzTop : z <= 14827 / 10000
      · -- Range 2: 1 <= z <= 1.4827.
        have hmin : min (1 / 4) ((843 / 5000 : Real) * z) =
            (843 / 5000 : Real) * z := by
          rw [min_eq_right]
          nlinarith
        have hgammaZ : gamma <=
            (471 / 1250 : Real) + (843 / 5000 : Real) * z := by
          rw [hmin] at hgamma
          linarith
        let q := (1862 / 5000 : Real) * z + (119 / 1000 : Real) * z ^ 2 -
          (779 / 10000 : Real) * z ^ 3 - (471 / 1250 : Real) - sigmaA e
        have hqF : q <= F := by
          have hmul : gamma * D <=
              ((471 / 1250 : Real) + (843 / 5000 : Real) * z) * D :=
            mul_le_mul_of_nonneg_right hgammaZ hDpos.le
          have hrem : 0 <=
              (z * (4589 / 5000 : Real) + (6 / 13 : Real) * z ^ 2 -
                ((471 / 1250 : Real) + (843 / 5000 : Real) * z) * D) -
              ((1862 / 5000 : Real) * z + (119 / 1000 : Real) * z ^ 2 -
                (779 / 10000 : Real) * z ^ 3 - (471 / 1250 : Real)) := by
            dsimp [D]
            have hz2 := sq_nonneg z
            have hz3 : 0 <= z ^ 3 := by positivity
            nlinarith
          dsimp [q, F, D] at hmul ⊢
          nlinarith [hfrac0]
        have hzsq : z ^ 2 <= (14827 / 10000 : Real) * z := by
          nlinarith [mul_nonneg hz.le (sub_nonneg.mpr hzTop)]
        let B := (1862 / 5000 : Real) + (119 / 1000 : Real) * (z + 1) -
          (779 / 10000 : Real) * (z ^ 2 + z + 1)
        have hBpos : 0 < B := by
          dsimp [B]
          nlinarith
        have hqdiff :
            q - ((1862 / 5000 : Real) + 119 / 1000 - 779 / 10000 -
              471 / 1250 - sigmaA e) = (z - 1) * B := by
          dsimp [q, B]
          ring
        have hqpos : 0 < q := by
          have hprod := mul_pos (sub_pos.mpr hzOne) hBpos
          nlinarith
        exact hqpos.trans_le hqF
      · -- Range 3: z >= 1.4827.
        have hzBottom : 14827 / 10000 < z := lt_of_not_ge hzTop
        have hgammaConst : gamma <= 1567 / 2500 := by
          have hmin := min_le_left (1 / 4 : Real)
            ((843 / 5000 : Real) * z)
          linarith
        have hlin : (291 / 1000 : Real) * z <=
            z * ((4589 / 5000 : Real) - gamma) := by
          have hc : (291 / 1000 : Real) <= 4589 / 5000 - gamma := by
            linarith
          simpa [mul_comm] using mul_le_mul_of_nonneg_left hc hz.le
        have hquad : (861 / 5000 : Real) * z ^ 2 <=
            (6 / 13 : Real) * (1 - gamma) * z ^ 2 := by
          have hc : (861 / 5000 : Real) <=
              (6 / 13 : Real) * (1 - gamma) := by
            nlinarith
          exact mul_le_mul_of_nonneg_right hc (sq_nonneg z)
        have hbase : (183 / 1000 : Real) <
            (291 / 1000 : Real) * z + (861 / 5000 : Real) * z ^ 2 -
              1567 / 2500 := by
          have hzsq : (14827 / 10000 : Real) ^ 2 < z ^ 2 :=
            pow_lt_pow_left₀ hzBottom (by norm_num) (by norm_num)
          nlinarith
        dsimp [F]
        nlinarith
  have hnonneg : 0 <=
      (1 - gamma) * D -
        (1 + (411 / 5000 : Real) * z - frac + sigmaA e) := by
    rw [hidentity]
    exact hF.le
  exact sub_nonneg.mp hnonneg

namespace AdmissibleParams

variable (P : AdmissibleParams)

theorem zoneA_reduced_battle
    (he : P.e <= 1 / 60) (hxi : 1 <= P.xi) (hR : 0 < P.R) :
    P.reducedBracketII + P.lambdaII <= P.piII := by
  let bracket :=
    (((P.m - 1 : Nat) : Real) / ((P.m : Real) * P.x) -
      (1 + 1 / P.kappa) / (P.m : Real))
  let U := 1 + (411 / 5000 : Real) * P.zA -
    (277 / 25 : Real) * P.e /
      (P.zA + (39 / 5 : Real) * P.e)
  let D := 1 + P.zA + (6 / 13 : Real) * P.zA ^ 2
  let gamma := gammaA P.ell P.epsII P.e
  have hpi : 1 - gamma <= P.piII := by
    simpa [gamma] using P.piII_lower_gamma he hxi
  have hlambda := P.lambdaII_le_sigma_mul_xpow he hR
  have hgamma := P.gammaA_upper he hxi hR
  have ha0 := P.a0A_le_zoneA he
  have hsigma := P.sigmaA_le_tiny_e he
  have hDpos : 0 < D := by
    dsimp [D]
    have hz := P.zA_pos
    nlinarith [sq_nonneg P.zA]
  have hxpow := P.x_pow_le_zoneA_rational
  change P.x ^ (P.m - 2) * bracket + P.lambdaII <= P.piII
  by_cases hb : bracket < 0
  · have hred : P.x ^ (P.m - 2) * bracket <= 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg P.x_pos.le _) hb.le
    have hsigx : sigmaA P.e * P.x ^ (P.m - 2) <= sigmaA P.e := by
      exact mul_le_of_le_one_right P.sigmaA_nonneg
        (pow_le_one₀ P.x_pos.le P.x_lt_one.le)
    have hgammaConst : gamma <= 1567 / 2500 := by
      have hmin := min_le_left (1 / 4 : Real)
        ((843 / 5000 : Real) * P.zA)
      dsimp [gamma] at hgamma ⊢
      linarith
    have hsigSmall := P.sigmaA_lt_zoneA_margin he
    calc
      P.x ^ (P.m - 2) * bracket + P.lambdaII <=
          0 + sigmaA P.e := add_le_add hred (hlambda.trans hsigx)
      _ <= 1 - gamma := by linarith
      _ <= P.piII := hpi
  · have hb0 : 0 <= bracket := le_of_not_gt hb
    have hBU : bracket <= U := by
      dsimp [bracket, U]
      exact P.bracket_upper_zoneA he
    have hU0 : 0 <= U := hb0.trans hBU
    have hsum :
        P.x ^ (P.m - 2) * bracket + P.lambdaII <=
          P.x ^ (P.m - 2) * (U + sigmaA P.e) := by
      calc
        P.x ^ (P.m - 2) * bracket + P.lambdaII <=
            P.x ^ (P.m - 2) * bracket +
              sigmaA P.e * P.x ^ (P.m - 2) :=
          add_le_add (le_refl _) hlambda
        _ <= P.x ^ (P.m - 2) * U +
              sigmaA P.e * P.x ^ (P.m - 2) :=
          add_le_add
            (mul_le_mul_of_nonneg_left hBU (pow_nonneg P.x_pos.le _))
            (le_refl _)
        _ = P.x ^ (P.m - 2) * (U + sigmaA P.e) := by ring
    have hUS0 : 0 <= U + sigmaA P.e :=
      add_nonneg hU0 P.sigmaA_nonneg
    have hpowBound : P.x ^ (P.m - 2) * (U + sigmaA P.e) <=
        (1 / D) * (U + sigmaA P.e) :=
      mul_le_mul_of_nonneg_right (by simpa [D] using hxpow) hUS0
    have hbattle : U + sigmaA P.e <= (1 - gamma) * D := by
      dsimp [U, gamma]
      exact zoneA_scalar_battle P.e_pos he P.zA_pos hgamma ha0 hsigma
    have hdivBattle : (1 / D) * (U + sigmaA P.e) <= 1 - gamma := by
      rw [show (1 / D) * (U + sigmaA P.e) =
          (U + sigmaA P.e) / D by ring]
      exact (div_le_iff₀ hDpos).2 (by simpa [mul_comm] using hbattle)
    exact hsum.trans hpowBound |>.trans hdivBattle |>.trans hpi

theorem zoneA_bound
    (he : P.e <= 1 / 60) (hxi : 1 <= P.xi) :
    P.R <= P.C * psi P.xi P.rho := by
  by_cases hR : 0 < P.R
  · have hreduced := P.zoneA_reduced_battle he hxi hR
    exact (P.R_le_linearPaymentII_of_reduced hxi hreduced).trans
      P.linearPaymentII_le_C_psi
  · have hR0 : P.R <= 0 := le_of_not_gt hR
    have hpsi : 0 <= psi P.xi P.rho := psi_nonneg P.rho_pos.le
    exact hR0.trans (mul_nonneg P.C_pos.le hpsi)

end AdmissibleParams

end OddCycleBound.RegionII.Scalar
