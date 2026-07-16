import OddCycleBound.RegionII.Certificate.ZoneCBattleSound

/-!
# Soundness of the moderate Zone-C bottom-out leaves

The five bottom leaves meet the singular edge `kappa -> 0`.  The finite
checker replaces a battle loop there by the secant forcing
`m - 2 > C0 / kappa` and the monotonicity of `exp (-a / kappa) / kappa`.
-/

noncomputable section

namespace OddCycleBound.RegionII.Certificate

open OddCycleBound.RegionII.Scalar

def bottomG2Prime (box : RatBox) : ℚ :=
  (makeCBox box).g2Lo - (makeCBox box).g2Lo ^ 2 / 2

def bottomC0 (box : RatBox) : ℚ :=
  (makeCBox box).qLo * bottomG2Prime box / box.e2

def bottomA (box : RatBox) : ℚ :=
  (makeCBox box).uLo * bottomC0 box

structure CBottomEvidence (box : RatBox) : Prop where
  sqrtOK : (makeCBox box).sqrtOK = true
  fLo_pos : 0 < (makeCBox box).fLo
  sLo_pos : 0 < (makeCBox box).sLo
  sLo_lt_xUp : (makeCBox box).sLo < (makeCBox box).xUp
  k1_nonpos : box.k1 <= 0
  caseI : 2 * (makeCBox box).rhoLoUp * (makeCBox box).xiUp <= 1
  g2Prime_pos : 0 < bottomG2Prime box
  k2_le_halfA : box.k2 <= bottomA box / 2
  exp_check :
    (1 / (makeCBox box).aLo) * expNegUpC (bottomA box / box.k2) <=
      (makeCBox box).cI0 * box.k2 * bottomC0 box

lemma checkCBottom_evidence {box : RatBox}
    (hcheck : checkCBottom box = true) : CBottomEvidence box := by
  rw [checkCBottom] at hcheck
  split at hcheck
  · simp at hcheck
  · rename_i hshape
    dsimp only at hcheck
    split at hcheck
    · simp at hcheck
    · rename_i hgate
      split at hcheck
      · simp at hcheck
      · rename_i hk2
        have hshape' := hshape
        simp at hshape'
        have hgate' := hgate
        simp at hgate'
        have hg2' : 0 < bottomG2Prime box := by
          simpa [bottomG2Prime, sub_pos] using hgate'.2
        have hk2' : box.k2 <= bottomA box / 2 := by
          simpa [bottomA, bottomC0, bottomG2Prime] using hk2
        have hexp :
            (1 / (makeCBox box).aLo) *
                expNegUpC (bottomA box / box.k2) <=
              (makeCBox box).cI0 * box.k2 * bottomC0 box := by
          simpa only [decide_eq_true_eq, bottomA, bottomC0,
            bottomG2Prime] using hcheck
        exact
          { sqrtOK := hshape'.1.1.1.1
            fLo_pos := hshape'.1.1.1.2
            sLo_pos := hshape'.1.1.2
            sLo_lt_xUp := hshape'.1.2
            k1_nonpos := le_of_eq hshape'.2
            caseI := hgate'.1
            g2Prime_pos := hg2'
            k2_le_halfA := hk2'
            exp_check := hexp }

/-- The monotonicity used by the bottom-out checker, in exactly the direction
needed for `0 < k <= K <= a`. -/
lemma exp_neg_div_div_monotone {a k K : Real}
    (hk : 0 < k) (hkK : k <= K) (hK : 0 < K) (hKa : K <= a) :
    Real.exp (-a / k) / k <= Real.exp (-a / K) / K := by
  let z := K / k
  have hzPos : 0 < z := div_pos hK hk
  have hzOne : 1 <= z := (le_div_iff₀ hk).2 (by simpa using hkK)
  have haK : 1 <= a / K := (le_div_iff₀ hK).2 (by simpa using hKa)
  have hzSub : 0 <= z - 1 := sub_nonneg.mpr hzOne
  have hlog : Real.log z <= z - 1 :=
    Real.log_le_sub_one_of_pos hzPos
  have hscaled : z - 1 <= (a / K) * (z - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haK) hzSub]
  have hexpArg : z <= Real.exp (a / k - a / K) := by
    apply (Real.log_le_iff_le_exp hzPos).1
    calc
      Real.log z <= z - 1 := hlog
      _ <= (a / K) * (z - 1) := hscaled
      _ = a / k - a / K := by
        dsimp [z]
        field_simp [hk.ne', hK.ne']
  have hmul := mul_le_mul_of_nonneg_right hexpArg (Real.exp_pos (-a / k)).le
  have hscaledExp :
      z * Real.exp (-a / k) <= Real.exp (-a / K) := by
    calc
      z * Real.exp (-a / k) <=
          Real.exp (a / k - a / K) * Real.exp (-a / k) := hmul
      _ = Real.exp (-a / K) := by
        rw [← Real.exp_add]
        congr 1
        ring
  rw [div_le_div_iff₀ hk hK]
  calc
    Real.exp (-a / k) * K =
        (z * Real.exp (-a / k)) * k := by
      dsimp [z]
      field_simp [hk.ne']
    _ <= Real.exp (-a / K) * k :=
      mul_le_mul_of_nonneg_right hscaledExp hk.le

namespace CAnalyticBoxContext

variable {P : AdmissibleParams} {box : RatBox}
  (H : CAnalyticBoxContext P box)

include H

lemma bottomC0_div_kappa_lt
    (ht : 0 < bottomG2Prime box) (hR : 0 < P.R) :
    (bottomC0 box : Real) / P.kappa < ((P.m - 2 : Nat) : Real) := by
  let t : Real := (bottomG2Prime box : Real)
  have hprimeLog : t <= Real.log (1 + P.G2) := by
    simpa [t, bottomG2Prime] using H.g2Prime_le_log_one_add_G2
  have hgate := P.secant_gate hR
  have hprimeRatio :
      t < ((P.m - 2 : Nat) : Real) * P.d / P.q :=
    lt_of_le_of_lt hprimeLog (hgate.1.trans_le hgate.2)
  have hcross :
      t * P.q < ((P.m - 2 : Nat) : Real) * P.d :=
    (lt_div_iff₀ P.q_pos).mp
      (by simpa [div_eq_mul_inv, mul_assoc] using hprimeRatio)
  have hqLo : ((makeCBox box).qLo : Real) <= P.q :=
    H.base.makeCBox_q.1
  have htR : (0 : Real) <= (bottomG2Prime box : Real) := by
    exact_mod_cast ht.le
  have hleft : ((makeCBox box).qLo : Real) * t <= P.q * t :=
    mul_le_mul_of_nonneg_right hqLo
      (by simpa [t] using htR)
  have he2 : (0 : Real) < (box.e2 : Real) :=
    P.e_pos.trans_le H.base.e_bounds.2
  have he : P.e <= (box.e2 : Real) := H.base.e_bounds.2
  have hn : (0 : Real) <= ((P.m - 2 : Nat) : Real) := by positivity
  have hk : 0 < P.kappa := P.kappa_pos
  have hdForm : P.d = P.kappa * P.e := P.kappa_mul_e.symm
  have hright :
      ((P.m - 2 : Nat) : Real) * P.d <=
        ((P.m - 2 : Nat) : Real) * (P.kappa * (box.e2 : Real)) := by
    rw [hdForm]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left he hk.le) hn
  have hnum :
      ((makeCBox box).qLo : Real) * t <
        ((P.m - 2 : Nat) : Real) * (P.kappa * (box.e2 : Real)) := by
    have hcross' : P.q * t < ((P.m - 2 : Nat) : Real) * P.d := by
      simpa [mul_comm] using hcross
    exact lt_of_le_of_lt hleft (hcross'.trans_le hright)
  rw [show (bottomC0 box : Real) =
      ((makeCBox box).qLo : Real) * t / (box.e2 : Real) by
    simp [bottomC0, t]]
  rw [div_div]
  apply (div_lt_iff₀ (mul_pos he2 hk)).2
  simpa [mul_assoc, mul_left_comm, mul_comm] using hnum

lemma bottom_caseI_gate (E : CBottomEvidence box) (hxi : P.xi <= 1) :
    2 * P.rhoLo * P.xi <= 1 := by
  have hfLo : (0 : Real) < ((makeCBox box).fLo : Real) := by
    exact_mod_cast E.fLo_pos
  have hrho := H.rhoLo_le_rhoLoUp hfLo
  have hxiUp := (H.makeCBox_xi hxi).2
  have hmul :
      P.rhoLo * P.xi <=
        ((makeCBox box).rhoLoUp : Real) *
          ((makeCBox box).xiUp : Real) :=
    mul_le_mul hrho hxiUp P.xi_pos.le (P.rhoLo_pos.le.trans hrho)
  have hgateR :
      2 * ((makeCBox box).rhoLoUp : Real) *
          ((makeCBox box).xiUp : Real) <= 1 := by
    exact_mod_cast E.caseI
  nlinarith

lemma bottom_cI0_nonneg :
    (0 : Real) <= ((makeCBox box).cI0 : Real) := by
  have hx : 0 <= 1 - ((makeCBox box).x14Up : Real) :=
    sub_nonneg.mpr H.x14Up_le_one
  have hy : 0 <= 1 - ((makeCBox box).y14Up : Real) :=
    sub_nonneg.mpr H.y14Up_le_one
  have hdx : 0 < 1 + ((makeCBox box).xUp : Real) := by
    linarith [H.xUp_nonneg]
  have hdy : 0 < 1 + ((makeCBox box).yUp : Real) := by
    linarith [H.yUp_nonneg]
  rw [show (makeCBox box).cI0 =
    2 * (1 - (makeCBox box).x14Up) *
      (1 - (makeCBox box).y14Up) /
        ((1 + (makeCBox box).xUp) * (1 + (makeCBox box).yUp)) by rfl]
  push_cast
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx) hy)
    (mul_pos hdx hdy).le

lemma normalized_R_le_bottom_decay
    (E : CBottomEvidence box) (hR : 0 < P.R) :
    P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) <=
      (1 / ((makeCBox box).aLo : Real)) *
        Real.exp (-(bottomA box : Real) / P.kappa) := by
  let b := makeCBox box
  let n := P.m - 2
  let u : Real := (b.uLo : Real)
  let c0 : Real := (bottomC0 box : Real)
  let a : Real := (bottomA box : Real)
  have hk2 : 0 < (box.k2 : Real) :=
    P.kappa_pos.trans_le H.base.k_bounds.2
  have hhalf : (box.k2 : Real) <= a / 2 := by
    have hcast : (box.k2 : Real) <= (bottomA box : Real) / 2 := by
      exact_mod_cast E.k2_le_halfA
    simpa [a] using hcast
  have ha : 0 < a := by linarith
  have hc0 : 0 < c0 := by
    have hq := H.qLo_pos
    have ht : (0 : Real) < (bottomG2Prime box : Real) := by
      exact_mod_cast E.g2Prime_pos
    have he2 : (0 : Real) < (box.e2 : Real) :=
      P.e_pos.trans_le H.base.e_bounds.2
    rw [show c0 = ((makeCBox box).qLo : Real) *
        (bottomG2Prime box : Real) / (box.e2 : Real) by
      simp [c0, bottomC0]]
    exact div_pos (mul_pos hq ht) he2
  have haForm : a = u * c0 := by
    dsimp [a, u, c0, bottomA, b]
    push_cast
    rfl
  have hu : 0 < u := by
    rw [haForm] at ha
    exact pos_of_mul_pos_left ha hc0.le
  have hforce := H.bottomC0_div_kappa_lt E.g2Prime_pos hR
  have harg :
      -(u * ((n : Nat) : Real)) <= -a / P.kappa := by
    have hk := P.kappa_pos
    have hmul : c0 < ((n : Nat) : Real) * P.kappa := by
      exact (div_lt_iff₀ hk).mp (by simpa [n] using hforce)
    rw [haForm]
    have huscaled := mul_lt_mul_of_pos_left hmul hu
    field_simp [hk.ne'] at huscaled ⊢
    nlinarith
  have hx0 : 0 <= P.x := by
    unfold Scalar.AdmissibleParams.x
    exact div_nonneg P.alpha_nonneg P.p_pos.le
  have hxBound : P.x <= (b.xUp : Real) := by
    simpa [b] using H.base.makeCBox_x.2
  have hxPow : P.x ^ n <= (b.xUp : Real) ^ n :=
    pow_le_pow_left₀ hx0 hxBound n
  have hfrontier :
      P.x ^ n / P.alpha <=
        (1 / (b.aLo : Real)) * (b.xUp : Real) ^ n := by
    have haLo : (b.aLo : Real) <= P.alpha := by
      simpa [b] using H.base.makeCBox_alpha.1
    have hcross :
        P.x ^ n * (b.aLo : Real) <=
          (b.xUp : Real) ^ n * P.alpha :=
      mul_le_mul hxPow haLo H.aLo_pos.le
        (pow_nonneg H.xUp_nonneg n)
    rw [show (1 / (b.aLo : Real)) * (b.xUp : Real) ^ n =
      (b.xUp : Real) ^ n / (b.aLo : Real) by ring]
    exact (div_le_div_iff₀ P.alpha_pos H.aLo_pos).2
      (by simpa [mul_comm] using hcross)
  have huForm : (b.xUp : Real) = 1 - u := by
    simp [b, u, makeCBox]
  have hbaseExp : (b.xUp : Real) <= Real.exp (-u) := by
    rw [huForm]
    exact Real.one_sub_le_exp_neg u
  have hpowExp :
      (b.xUp : Real) ^ n <= Real.exp (-(u * ((n : Nat) : Real))) := by
    calc
      (b.xUp : Real) ^ n <= Real.exp (-u) ^ n :=
        pow_le_pow_left₀ H.xUp_nonneg hbaseExp n
      _ = Real.exp (((n : Nat) : Real) * (-u)) :=
        (Real.exp_nat_mul (-u) n).symm
      _ = Real.exp (-(u * ((n : Nat) : Real))) := by
        congr 1
        ring
  have hexp :
      Real.exp (-(u * ((n : Nat) : Real))) <=
        Real.exp (-a / P.kappa) := Real.exp_le_exp.mpr harg
  calc
    P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) <=
        P.x ^ (P.m - 2) / P.alpha := P.normalized_R_le_x_term
    _ <= (1 / (b.aLo : Real)) * (b.xUp : Real) ^ n := by
      simpa [n] using hfrontier
    _ <= (1 / (b.aLo : Real)) * Real.exp (-a / P.kappa) :=
      mul_le_mul_of_nonneg_left (hpowExp.trans hexp)
        (one_div_nonneg.mpr H.aLo_pos.le)
    _ = _ := by simp [b, a]

lemma bottom_decay_le_checked_coefficient (E : CBottomEvidence box) :
    (1 / ((makeCBox box).aLo : Real)) *
        Real.exp (-(bottomA box : Real) / P.kappa) <=
      ((makeCBox box).cI0 : Real) * P.kappa * (bottomC0 box : Real) := by
  let a : Real := (bottomA box : Real)
  let c0 : Real := (bottomC0 box : Real)
  let K : Real := (box.k2 : Real)
  let k : Real := P.kappa
  let pref : Real := 1 / ((makeCBox box).aLo : Real)
  have hk : 0 < k := P.kappa_pos
  have hkK : k <= K := H.base.k_bounds.2
  have hK : 0 < K := hk.trans_le hkK
  have hhalf : K <= a / 2 := by
    have hcast : (box.k2 : Real) <= (bottomA box : Real) / 2 := by
      exact_mod_cast E.k2_le_halfA
    simpa [K, a] using hcast
  have hKa : K <= a := by linarith
  have hmono : Real.exp (-a / k) / k <= Real.exp (-a / K) / K :=
    exp_neg_div_div_monotone hk hkK hK hKa
  have hexpUp : Real.exp (-a / K) <=
      (expNegUpC (bottomA box / box.k2) : Real) := by
    have hs := expNegUpC_sound
      (t := bottomA box / box.k2)
      (by
        have haR : (0 : Real) <= (bottomA box : Real) := by
          simpa [a] using hK.le.trans hKa
        have haQ : 0 <= bottomA box := by exact_mod_cast haR
        have hKR : (0 : Real) <= (box.k2 : Real) := by
          simpa [K] using hK.le
        have hKQ : 0 <= box.k2 := by exact_mod_cast hKR
        exact div_nonneg haQ hKQ)
    simpa only [a, K, Rat.cast_div, neg_div] using hs
  have hcheckR :
      (1 / ((makeCBox box).aLo : Real)) *
          (expNegUpC (bottomA box / box.k2) : Real) <=
        ((makeCBox box).cI0 : Real) * (box.k2 : Real) *
          (bottomC0 box : Real) := by
    exact_mod_cast E.exp_check
  have hpref : 0 <= pref := one_div_nonneg.mpr H.aLo_pos.le
  have hratio : 0 <= k / K := div_nonneg hk.le hK.le
  calc
    (1 / ((makeCBox box).aLo : Real)) *
        Real.exp (-(bottomA box : Real) / P.kappa) =
      (pref * k) * (Real.exp (-a / k) / k) := by
        dsimp [pref, k, a]
        field_simp [hk.ne', H.aLo_pos.ne']
        exact (div_self hk.ne').symm
    _ <= (pref * k) * (Real.exp (-a / K) / K) :=
      mul_le_mul_of_nonneg_left hmono (mul_nonneg hpref hk.le)
    _ = (k / K) * (pref * Real.exp (-a / K)) := by ring
    _ <= (k / K) *
        (pref * (expNegUpC (bottomA box / box.k2) : Real)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hexpUp hpref) hratio
    _ <= (k / K) *
        (((makeCBox box).cI0 : Real) * K * c0) := by
      apply mul_le_mul_of_nonneg_left ?_ hratio
      simpa [pref, K, c0] using hcheckR
    _ = ((makeCBox box).cI0 : Real) * P.kappa *
        (bottomC0 box : Real) := by
      have hK0 : (box.k2 : Real) ≠ 0 := by
        simpa [K] using hK.ne'
      dsimp [k, K, c0]
      field_simp [hK0]

lemma bottom_checked_coefficient_le_normalized_payment
    (E : CBottomEvidence box) (hxi : P.xi <= 1) (hR : 0 < P.R) :
    ((makeCBox box).cI0 : Real) * P.kappa * (bottomC0 box : Real) <=
      P.C * psi P.xi P.rho /
        (P.alpha ^ 3 * P.p ^ (P.m - 2)) := by
  have hforce := H.bottomC0_div_kappa_lt E.g2Prime_pos hR
  have hk := P.kappa_pos
  have hnle : (((P.m - 2 : Nat) : Nat) : Real) <= (P.m : Real) := by
    exact_mod_cast Nat.sub_le P.m 2
  have hc0le : (bottomC0 box : Real) <= (P.m : Real) * P.kappa := by
    have hc0lt : (bottomC0 box : Real) <
        (((P.m - 2 : Nat) : Nat) : Real) * P.kappa :=
      (div_lt_iff₀ hk).mp hforce
    exact hc0lt.le.trans
      (mul_le_mul_of_nonneg_right hnle hk.le)
  have hcoeff :
      ((makeCBox box).cI0 : Real) * P.kappa * (bottomC0 box : Real) <=
        (P.m : Real) *
          (((makeCBox box).cI0 : Real) * P.kappa ^ 2) := by
    have hscale : 0 <= ((makeCBox box).cI0 : Real) * P.kappa :=
      mul_nonneg H.bottom_cI0_nonneg hk.le
    calc
      ((makeCBox box).cI0 : Real) * P.kappa * (bottomC0 box : Real) <=
          (((makeCBox box).cI0 : Real) * P.kappa) *
            ((P.m : Real) * P.kappa) :=
        mul_le_mul_of_nonneg_left hc0le hscale
      _ = (P.m : Real) *
          (((makeCBox box).cI0 : Real) * P.kappa ^ 2) := by ring
  have hm0 : (0 : Real) <= (P.m : Real) := by positivity
  calc
    ((makeCBox box).cI0 : Real) * P.kappa * (bottomC0 box : Real) <=
        (P.m : Real) *
          (((makeCBox box).cI0 : Real) * P.kappa ^ 2) := hcoeff
    _ <= (P.m : Real) * P.paymentCoeffI :=
      mul_le_mul_of_nonneg_left H.cI0_mul_kappa_sq_le_paymentCoeffI hm0
    _ <= P.C * psi P.xi P.rho /
        (P.alpha ^ 3 * P.p ^ (P.m - 2)) :=
      P.paymentCoeffI_le_normalized_psi (H.bottom_caseI_gate E hxi)

end CAnalyticBoxContext

theorem checkCBottom_sound {P : AdmissibleParams} {box : RatBox}
    (H : CBoxContext P box)
    (hcheck : checkCBottom box = true)
    (hxi : P.xi <= 1) :
    P.R <= P.C * psi P.xi P.rho := by
  have hev := checkCBottom_evidence hcheck
  let HA : CAnalyticBoxContext P box :=
    { toCBoxContext := H
      sqrtOK := hev.sqrtOK }
  by_cases hR : 0 < P.R
  · have hnorm := (HA.normalized_R_le_bottom_decay hev hR).trans
      (HA.bottom_decay_le_checked_coefficient hev)
    have hpay := HA.bottom_checked_coefficient_le_normalized_payment
      hev hxi hR
    have hden : 0 < P.alpha ^ 3 * P.p ^ (P.m - 2) :=
      P.normalized_payment_pos
    exact (div_le_div_iff_of_pos_right hden).1 (hnorm.trans hpay)
  · have hRnonpos : P.R <= 0 := le_of_not_gt hR
    exact hRnonpos.trans
      (mul_nonneg P.C_pos.le (psi_nonneg P.rho_pos.le))

end OddCycleBound.RegionII.Certificate
