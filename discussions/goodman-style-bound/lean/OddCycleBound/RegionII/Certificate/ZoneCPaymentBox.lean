import OddCycleBound.RegionII.Certificate.ZoneCAnalyticBox

/-!
# Payment and secant semantics for moderate Zone-C boxes

This layer connects the remaining derived fields of `makeCBox` to the real
scalar quantities.  It is deliberately independent of the recursive battle
checker: the latter may rely only on inequalities proved here.
-/

noncomputable section

namespace OddCycleBound.RegionII.Certificate

open OddCycleBound.RegionII.Scalar

lemma xiFactor_antitone {a b : Real} (ha : 0 < a) (hab : a <= b)
    (hb : b < 1) :
    (1 - b) ^ 2 / b <= (1 - a) ^ 2 / a := by
  have hb0 : 0 < b := ha.trans_le hab
  rw [div_le_div_iff₀ hb0 ha]
  have hab0 : 0 <= b - a := sub_nonneg.mpr hab
  have hab1 : a * b < 1 := by
    have ha1 : a <= 1 := hab.trans hb.le
    exact (mul_le_of_le_one_left hb0.le ha1).trans_lt hb
  have hprod : 0 <= (b - a) * (1 - a * b) :=
    mul_nonneg hab0 (sub_nonneg.mpr hab1.le)
  nlinarith

lemma sqrtLoC_two_pos : (0 : Real) < (sqrtLoC 2 : ℚ) := by
  have hq : (0 : ℚ) < sqrtLoC 2 := by decide +kernel
  exact_mod_cast hq

lemma sqrtLoC_nonneg (x : ℚ) : (0 : Real) <= (sqrtLoC x : ℚ) := by
  have hq : (0 : ℚ) <= sqrtLoC x := by
    unfold sqrtLoC sqrtLo
    positivity
  exact_mod_cast hq

lemma paymentRatioI_mono {a b : Real} (ha : 0 <= a) (hab : a <= b) :
    (1 + 4 * a) / (1 + 2 * a) <=
      (1 + 4 * b) / (1 + 2 * b) := by
  have hda : 0 < 1 + 2 * a := by linarith
  have hdb : 0 < 1 + 2 * b := by linarith
  rw [div_le_div_iff₀ hda hdb]
  nlinarith

lemma paymentRatioII_mono {a b : Real} (ha : 0 <= a) (hab : a <= b) :
    (4 * a + 1) / (4 * a + 2) <=
      (4 * b + 1) / (4 * b + 2) := by
  have hda : 0 < 4 * a + 2 := by linarith
  have hdb : 0 < 4 * b + 2 := by linarith
  rw [div_le_div_iff₀ hda hdb]
  nlinarith

namespace CAnalyticBoxContext

variable {P : AdmissibleParams} {box : RatBox}
  (H : CAnalyticBoxContext P box)

include H

lemma aLo_pos : 0 < ((makeCBox box).aLo : Real) := by
  simp only [makeCBox]
  push_cast
  linarith [H.base.e2_lt_one]

lemma aUp_pos : 0 < ((makeCBox box).aUp : Real) :=
  P.alpha_pos.trans_le H.base.makeCBox_alpha.2

lemma pUp_pos : 0 < ((makeCBox box).pUp : Real) :=
  P.p_pos.trans_le H.base.makeCBox_p.2

lemma qLo_pos : 0 < ((makeCBox box).qLo : Real) :=
  by
    simp only [makeCBox, Rat.cast_max]
    have hmax :
        (((1 / 3 : ℚ)) : Real) <=
          max ((((1 - box.e2) / 2 - box.k2 * box.e2 : ℚ)) : Real)
            (((1 / 3 : ℚ)) : Real) :=
      le_max_right _ _
    norm_num at hmax ⊢

lemma sLo_pos : 0 < ((makeCBox box).sLo : Real) := by
  simp only [makeCBox, Rat.cast_div]
  exact div_pos H.qLo_pos H.pUp_pos

lemma sLo_le_s :
    ((makeCBox box).sLo : Real) <= P.s := by
  have hq := H.base.makeCBox_q.1
  have hp := H.base.makeCBox_p.2
  unfold AdmissibleParams.s
  have hs :
      ((makeCBox box).qLo : Real) / ((makeCBox box).pUp : Real) <=
        P.q / P.p := by
    rw [div_le_div_iff₀ H.pUp_pos P.p_pos]
    exact mul_le_mul hq hp P.p_pos.le
      P.q_nonneg
  simpa only [makeCBox, Rat.cast_div] using hs

lemma ell_sq_lower :
    ((makeCBox box).l2Lo : Real) <= P.ell ^ 2 := by
  have hnum := H.cL2Floor_le_L_sq
  have hden := H.base.makeCBox_alpha.2
  have hfloor : (0 : Real) <= cL2Floor box := by
    exact_mod_cast
      (le_max_left (0 : ℚ)
        (((1 - box.e2) / 2) * box.e1 -
          (box.k2 * box.e2) * (box.k2 * box.e2 + box.e2)))
  have hcross :
      (cL2Floor box : Real) * P.alpha ^ 2 <=
        P.L ^ 2 * ((makeCBox box).aUp : Real) ^ 2 := by
    exact mul_le_mul hnum
      (pow_le_pow_left₀ P.alpha_nonneg hden 2)
      (sq_nonneg _) (sq_nonneg P.L)
  unfold AdmissibleParams.ell
  rw [div_pow]
  have hl2 :
      ((makeCBox box).l2Lo : Real) =
        (cL2Floor box : Real) / ((makeCBox box).aUp : Real) ^ 2 := by
    simp only [makeCBox, Rat.cast_div, Rat.cast_pow]
  rw [hl2]
  rw [div_le_div_iff₀ (pow_pos H.aUp_pos 2) (pow_pos P.alpha_pos 2)]
  exact hcross

lemma ell_sq_le_raw_upper :
    P.ell ^ 2 <=
      ((cL2Ceil box / (((1 - box.e2) / 2) ^ 2) : ℚ) : Real) := by
  have hnum := H.L_sq_le_cL2Ceil
  have hden := H.base.alpha_lower
  have hceil : (0 : Real) <= cL2Ceil box :=
    (sq_nonneg P.L).trans hnum
  have hcross :
      P.L ^ 2 * ((((1 - box.e2) / 2 : ℚ) : Real) ^ 2) <=
        (cL2Ceil box : Real) * P.alpha ^ 2 := by
    exact mul_le_mul hnum
      (pow_le_pow_left₀ H.aLo_nonneg hden 2)
      (sq_nonneg _) hceil
  unfold AdmissibleParams.ell
  rw [div_pow, Rat.cast_div, Rat.cast_pow]
  rw [div_le_div_iff₀ (pow_pos P.alpha_pos 2)
    (pow_pos (by simpa only [makeCBox] using H.aLo_pos) 2)]
  simpa only [makeCBox] using hcross

lemma ell_sq_le_one : P.ell ^ 2 <= 1 := by
  unfold AdmissibleParams.ell
  rw [div_pow]
  have hsq : P.L ^ 2 <= P.alpha ^ 2 :=
    pow_le_pow_left₀ P.L_nonneg P.L_lt_alpha.le 2
  exact (div_le_one (pow_pos P.alpha_pos 2)).2 hsq

lemma makeCBox_ell_sq :
    ((makeCBox box).l2Lo : Real) <= P.ell ^ 2 ∧
      P.ell ^ 2 <= ((makeCBox box).l2Up : Real) := by
  refine ⟨H.ell_sq_lower, ?_⟩
  simp only [makeCBox, Rat.cast_min, le_min_iff]
  exact ⟨H.ell_sq_le_raw_upper, by simpa only [Rat.cast_one] using H.ell_sq_le_one⟩

lemma xiFactor_lower :
    ((((1 - box.e2) ^ 2 / box.e2 : ℚ)) : Real) <=
      (1 - P.e) ^ 2 / P.e := by
  push_cast
  exact xiFactor_antitone P.e_pos (H.base.e_bounds.2)
    H.base.e2_lt_one

lemma xiFactor_upper :
    (1 - P.e) ^ 2 / P.e <=
      ((((1 - box.e1) ^ 2 / box.e1 : ℚ)) : Real) := by
  have he1pos : (0 : Real) < box.e1 :=
    lt_of_lt_of_le (by norm_num : (0 : Real) < (1 / 60 : ℚ))
      (by exact_mod_cast (H.base.placed_rat.1))
  push_cast
  exact xiFactor_antitone he1pos H.base.e_bounds.1
    (P.e_lt_third.trans (by norm_num))

lemma xi_lower :
    ((makeCBox box).xiLo : Real) <= P.xi := by
  have hk := H.base.k_bounds.1
  have hfactor := H.xiFactor_lower
  have hfactor0 : (0 : Real) <= ((1 - box.e2) ^ 2 / box.e2 : ℚ) := by
    have he2q : (0 : ℚ) <= box.e2 := by exact_mod_cast H.e2_nonneg
    exact_mod_cast (div_nonneg (sq_nonneg (1 - box.e2)) he2q)
  have hrealFactor0 : 0 <= (1 - P.e) ^ 2 / P.e :=
    div_nonneg (sq_nonneg _) P.e_pos.le
  have hxiForm :
      P.xi = ((1 - P.e) ^ 2 / P.e) * P.kappa := by
    rw [P.xi_chart]
    field_simp [P.e_pos.ne']
  have hcast :
      ((makeCBox box).xiLo : Real) =
        (((1 - box.e2) ^ 2 / box.e2 : ℚ) : Real) * box.k1 := by
    simp only [makeCBox]
    push_cast
    ring
  rw [hcast, hxiForm]
  exact mul_le_mul hfactor hk H.base.k1_nonneg hrealFactor0

lemma xi_le_raw_upper :
    P.xi <=
      ((((1 - box.e1) ^ 2 * box.k2 / box.e1 : ℚ)) : Real) := by
  have hk := H.base.k_bounds.2
  have hfactor := H.xiFactor_upper
  have hk2 : (0 : Real) <= box.k2 := H.k2_nonneg
  have hfactor0 : 0 <= (1 - P.e) ^ 2 / P.e :=
    div_nonneg (sq_nonneg _) P.e_pos.le
  have hxiForm :
      P.xi = ((1 - P.e) ^ 2 / P.e) * P.kappa := by
    rw [P.xi_chart]
    field_simp [P.e_pos.ne']
  have hcast :
      ((((1 - box.e1) ^ 2 * box.k2 / box.e1 : ℚ)) : Real) =
        ((((1 - box.e1) ^ 2 / box.e1 : ℚ)) : Real) * box.k2 := by
    push_cast
    ring
  rw [hxiForm, hcast]
  exact mul_le_mul hfactor hk P.kappa_pos.le (hfactor0.trans hfactor)

lemma makeCBox_xi (hxi : P.xi <= 1) :
    ((makeCBox box).xiLo : Real) <= P.xi ∧
      P.xi <= ((makeCBox box).xiUp : Real) := by
  refine ⟨H.xi_lower, ?_⟩
  simp only [makeCBox, Rat.cast_min, le_min_iff]
  exact ⟨by norm_num; exact hxi, H.xi_le_raw_upper⟩

lemma sqrt_alpha_lower :
    ((sqrtLoC ((1 - box.e2) / 2) : ℚ) : Real) <= Real.sqrt P.alpha := by
  have hs := (sqrtBracketOK_sound (makeCBox_sqrt_components H.sqrtOK).2.2.1).1
  exact hs.trans (Real.sqrt_le_sqrt H.base.alpha_lower)

lemma sqrt_alpha_upper :
    Real.sqrt P.alpha <=
      ((sqrtUpC ((1 - box.e1) / 2) : ℚ) : Real) := by
  have hs := (sqrtBracketOK_sound
    (makeCBox_sqrt_components H.sqrtOK).2.2.2.1).2
  exact (Real.sqrt_le_sqrt H.base.alpha_upper).trans hs

lemma sqrt_two_lower :
    ((sqrtLoC 2 : ℚ) : Real) <= Real.sqrt 2 :=
  (sqrtBracketOK_sound
    (makeCBox_sqrt_components H.sqrtOK).2.2.2.2.1).1

lemma sqrt_two_upper :
    Real.sqrt 2 <= ((sqrtUpC 2 : ℚ) : Real) :=
  (sqrtBracketOK_sound
    (makeCBox_sqrt_components H.sqrtOK).2.2.2.2.1).2

lemma sqrt_two_alpha_lower :
    ((sqrtLoC (2 * ((1 - box.e2) / 2)) : ℚ) : Real) <=
      Real.sqrt (2 * P.alpha) := by
  have hs := (sqrtBracketOK_sound
    (makeCBox_sqrt_components H.sqrtOK).2.2.2.2.2).1
  have harg :
      (((2 * ((1 - box.e2) / 2) : ℚ)) : Real) <= 2 * P.alpha := by
    have ha := H.base.alpha_lower
    push_cast at ha
    push_cast
    linarith
  exact hs.trans (Real.sqrt_le_sqrt harg)

lemma xLo_pos : 0 < ((makeCBox box).xLo : Real) := by
  simp only [makeCBox, cast_chartXQ]
  unfold chartXR
  exact div_pos (sub_pos.mpr H.base.e2_lt_one)
    (chartXR_den_pos H.e2_nonneg H.k2_nonneg)

lemma xUp_nonneg : 0 <= ((makeCBox box).xUp : Real) :=
  (div_nonneg P.alpha_nonneg P.p_pos.le).trans H.base.makeCBox_x.2

lemma x14Lo_le :
    ((makeCBox box).x14Lo : Real) <= P.x ^ 14 := by
  have hxLoQ : (0 : ℚ) <= (makeCBox box).xLo := by
    exact_mod_cast H.xLo_pos.le
  have hr0Q := roundDown_nonneg hxLoQ (by norm_num : 0 < 10 ^ 6)
  have hrleQ := roundDown_le (makeCBox box).xLo
    (by norm_num : 0 < 10 ^ 6)
  have hr0 : (0 : Real) <= roundDown (makeCBox box).xLo (10 ^ 6) := by
    exact_mod_cast hr0Q
  have hrle :
      ((roundDown (makeCBox box).xLo (10 ^ 6) : ℚ) : Real) <= P.x := by
    have hcast :
        ((roundDown (makeCBox box).xLo (10 ^ 6) : ℚ) : Real) <=
          ((makeCBox box).xLo : Real) := by
      exact_mod_cast hrleQ
    exact hcast.trans H.base.makeCBox_x.1
  have hp := pow_le_pow_left₀ hr0 hrle 14
  simpa only [makeCBox, Rat.cast_pow] using hp

lemma x14_le_x14Up :
    P.x ^ 14 <= ((makeCBox box).x14Up : Real) := by
  have hxUpQ : (0 : ℚ) <= (makeCBox box).xUp := by
    exact_mod_cast H.xUp_nonneg
  have hrQ := le_roundUp (makeCBox box).xUp
    (by norm_num : 0 < 10 ^ 6)
  have hr :
      P.x <= ((roundUp (makeCBox box).xUp (10 ^ 6) : ℚ) : Real) :=
    H.base.makeCBox_x.2.trans (by exact_mod_cast hrQ)
  have hx0 : 0 <= P.x := div_nonneg P.alpha_nonneg P.p_pos.le
  have hpRound := pow_le_pow_left₀ hx0 hr 14
  have hpOne : P.x ^ 14 <= 1 :=
    (pow_le_one₀ hx0 P.x_lt_one.le)
  simp only [makeCBox, Rat.cast_min, le_min_iff, Rat.cast_pow]
  exact ⟨by simpa only [Rat.cast_one] using hpOne, hpRound⟩

lemma x14Up_le_one :
    ((makeCBox box).x14Up : Real) <= 1 := by
  simp only [makeCBox, Rat.cast_min]
  simpa only [Rat.cast_one] using
    (min_le_left (1 : Real)
      ((((roundUp (chartXQ box.e1 box.k1) (10 ^ 6)) ^ 14 : ℚ)) : Real))

lemma y_pow_le_y14Up :
    P.y ^ (P.m - 1) <= ((makeCBox box).y14Up : Real) := by
  have hyUp0 : 0 <= ((makeCBox box).yUp : Real) :=
    P.y_nonneg.trans H.y_le_yUp
  have hyUpQ : (0 : ℚ) <= (makeCBox box).yUp := by
    exact_mod_cast hyUp0
  have hrQ := le_roundUp (makeCBox box).yUp
    (by norm_num : 0 < 10 ^ 6)
  have hr :
      P.y <= ((roundUp (makeCBox box).yUp (10 ^ 6) : ℚ) : Real) :=
    H.y_le_yUp.trans (by exact_mod_cast hrQ)
  have hm14 : 14 <= P.m - 1 := by
    have hm := P.m_ge_fifteen
    omega
  have hy1 : P.y <= 1 := H.y_le_half.trans (by norm_num)
  have hdrop : P.y ^ (P.m - 1) <= P.y ^ 14 :=
    pow_le_pow_of_le_one P.y_nonneg hy1 hm14
  have hpRound : P.y ^ 14 <=
      ((roundUp (makeCBox box).yUp (10 ^ 6) : ℚ) : Real) ^ 14 :=
    pow_le_pow_left₀ P.y_nonneg hr 14
  have hpOne : P.y ^ (P.m - 1) <= 1 :=
    pow_le_one₀ P.y_nonneg hy1
  simp only [makeCBox, Rat.cast_min, le_min_iff, Rat.cast_pow]
  exact ⟨by simpa only [Rat.cast_one] using hpOne, hdrop.trans hpRound⟩

lemma y14Up_le_one :
    ((makeCBox box).y14Up : Real) <= 1 := by
  have hq : (makeCBox box).y14Up <= (1 : ℚ) := by
    rw [show (makeCBox box).y14Up =
      min 1 (roundUp (makeCBox box).yUp (10 ^ 6) ^ 14) by rfl]
    exact min_le_left _ _
  exact_mod_cast hq

lemma xiLo_nonneg :
    (0 : Real) <= ((makeCBox box).xiLo : Real) := by
  have he2 : (0 : Real) < box.e2 := P.e_pos.trans_le H.base.e_bounds.2
  have he2q : (0 : ℚ) < box.e2 := by exact_mod_cast he2
  have hk1q : (0 : ℚ) <= box.k1 := by exact_mod_cast H.base.k1_nonneg
  have hq :
      (0 : ℚ) <= (1 - box.e2) ^ 2 * box.k1 / box.e2 :=
    div_nonneg (mul_nonneg (sq_nonneg _) hk1q) he2q.le
  simpa only [makeCBox] using
    (show (0 : Real) <=
      ((((1 - box.e2) ^ 2 * box.k1 / box.e2 : ℚ)) : Real) by
        exact_mod_cast hq)

lemma y_div_s_le_ysUp :
    P.y / P.s <=
      (cYSUp box : Real) := by
  have hyUp0 : 0 <= ((makeCBox box).yUp : Real) :=
    P.y_nonneg.trans H.y_le_yUp
  have hsLoQ : (0 : ℚ) < (makeCBox box).sLo := by
    exact_mod_cast H.sLo_pos
  have hratio :
      P.y / P.s <=
        ((makeCBox box).yUp : Real) / ((makeCBox box).sLo : Real) := by
    rw [div_le_div_iff₀ P.s_pos H.sLo_pos]
    exact mul_le_mul H.y_le_yUp H.sLo_le_s H.sLo_pos.le
      (P.y_nonneg.trans H.y_le_yUp)
  have hratioQ :
      (0 : ℚ) <= (makeCBox box).yUp / (makeCBox box).sLo := by
    have hyUpQ : (0 : ℚ) <= (makeCBox box).yUp := by exact_mod_cast hyUp0
    exact div_nonneg hyUpQ hsLoQ.le
  have hroundQ := le_roundUp
    ((makeCBox box).yUp / (makeCBox box).sLo)
    (by norm_num : 0 < 10 ^ 6)
  have hYS :
      cYSUp box =
        min (roundUp ((makeCBox box).yUp / (makeCBox box).sLo) (10 ^ 6)) 1 := by
    rfl
  rw [hYS, Rat.cast_min, le_min_iff]
  refine ⟨?_, by norm_num; exact P.y_div_s_lt_one.le⟩
  calc
    P.y / P.s <=
        ((makeCBox box).yUp : Real) / ((makeCBox box).sLo : Real) := hratio
    _ = (((makeCBox box).yUp / (makeCBox box).sLo : ℚ) : Real) := by
      rw [Rat.cast_div]
    _ <= ((roundUp ((makeCBox box).yUp / (makeCBox box).sLo)
        (10 ^ 6) : ℚ) : Real) := by exact_mod_cast hroundQ

lemma l2Lo_nonneg :
    (0 : Real) <= ((makeCBox box).l2Lo : Real) := by
  simp only [makeCBox, Rat.cast_div]
  exact div_nonneg
    (by
      exact_mod_cast
        (le_max_left (0 : ℚ)
          (((1 - box.e2) / 2) * box.e1 -
            (box.k2 * box.e2) * (box.k2 * box.e2 + box.e2))))
    (by positivity)

lemma g2Lo_nonneg :
    (0 : Real) <= ((makeCBox box).g2Lo : Real) := by
  have hys0 : (0 : Real) <= cYSUp box :=
    P.y_div_s_nonneg.trans H.y_div_s_le_ysUp
  have hys1 : (cYSUp box : Real) <= 1 := by
    unfold cYSUp
    rw [Rat.cast_min]
    simpa only [Rat.cast_one] using
      (min_le_right
        (((roundUp (cYUp box / cSLo box)
          (10 ^ 6) : ℚ)) : Real) (1 : Real))
  have hfactor : (0 : Real) <= 1 - (cYSUp box : Real) ^ 13 :=
    sub_nonneg.mpr (pow_le_one₀ hys0 hys1)
  rw [show (makeCBox box).g2Lo =
      (makeCBox box).l2Lo * (1 - cYSUp box ^ 13) by rfl]
  push_cast
  exact mul_nonneg H.l2Lo_nonneg hfactor

lemma g2Lo_le_G2 :
    ((makeCBox box).g2Lo : Real) <= P.G2 := by
  have hys := H.y_div_s_le_ysUp
  have hys0 : (0 : Real) <= cYSUp box := P.y_div_s_nonneg.trans hys
  have hys1 : (cYSUp box : Real) <= 1 := by
    unfold cYSUp
    rw [Rat.cast_min]
    simpa only [Rat.cast_one] using
      (min_le_right
        (((roundUp (cYUp box / cSLo box)
          (10 ^ 6) : ℚ)) : Real) (1 : Real))
  have hpow :
      (P.y / P.s) ^ 13 <= (cYSUp box : Real) ^ 13 :=
    pow_le_pow_left₀ P.y_div_s_nonneg hys 13
  have hfactor :
      1 - (cYSUp box : Real) ^ 13 <= 1 - (P.y / P.s) ^ 13 :=
    sub_le_sub_left hpow 1
  have hfactor0 : 0 <= 1 - (cYSUp box : Real) ^ 13 :=
    sub_nonneg.mpr (pow_le_one₀ hys0 hys1)
  unfold AdmissibleParams.G2
  have hmul := mul_le_mul H.makeCBox_ell_sq.1 hfactor
    hfactor0 (sq_nonneg P.ell)
  rw [show (makeCBox box).g2Lo =
      (makeCBox box).l2Lo * (1 - cYSUp box ^ 13) by rfl]
  push_cast
  exact hmul

lemma rhoLo_le_rhoLoUp
    (hfLo : (0 : Real) < (makeCBox box).fLo) :
    P.rhoLo <= ((makeCBox box).rhoLoUp : Real) := by
  let n : Real := (1 - P.x ^ 14) * Real.sqrt P.alpha
  let nUp : Real :=
    (1 - ((makeCBox box).x14Lo : Real)) *
      ((sqrtUpC (makeCBox box).aUp : ℚ) : Real)
  let den : Real :=
    2 * Real.sqrt 2 * P.f * (1 + P.x)
  let denLo : Real :=
    2 * ((sqrtLoC 2 : ℚ) : Real) * ((makeCBox box).fLo : Real) *
      (1 + ((makeCBox box).xLo : Real))
  have hx14lt : P.x ^ 14 < 1 :=
    pow_lt_one₀ (div_nonneg P.alpha_nonneg P.p_pos.le)
      P.x_lt_one (by norm_num)
  have hxsub : 0 <= 1 - P.x ^ 14 := sub_nonneg.mpr hx14lt.le
  have hxsubUp : 0 <= 1 - ((makeCBox box).x14Lo : Real) :=
    sub_nonneg.mpr (H.x14Lo_le.trans hx14lt.le)
  have hn : n <= nUp := by
    dsimp [n, nUp]
    exact mul_le_mul (sub_le_sub_left H.x14Lo_le 1)
      H.sqrt_alpha_upper (Real.sqrt_nonneg _) hxsubUp
  have hnUp0 : 0 <= nUp := by
    dsimp [nUp]
    exact mul_nonneg hxsubUp
      ((Real.sqrt_nonneg _).trans H.sqrt_alpha_upper)
  have hdenLoPos : 0 < denLo := by
    dsimp [denLo]
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) sqrtLoC_two_pos) hfLo)
      (by linarith [H.xLo_pos])
  have hdenPos : 0 < den := by
    dsimp [den]
    have hx0 : 0 <= P.x := div_nonneg P.alpha_nonneg P.p_pos.le
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num)))
        P.f_pos)
      (by linarith)
  have hden : denLo <= den := by
    dsimp [denLo, den]
    have h1 :
        2 * ((sqrtLoC 2 : ℚ) : Real) <= 2 * Real.sqrt 2 :=
      mul_le_mul_of_nonneg_left H.sqrt_two_lower (by norm_num)
    have h2 :
        2 * ((sqrtLoC 2 : ℚ) : Real) * ((makeCBox box).fLo : Real) <=
          2 * Real.sqrt 2 * P.f :=
      mul_le_mul h1 H.fLo_le_f hfLo.le
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    have hxadd :
        1 + ((makeCBox box).xLo : Real) <= 1 + P.x := by
      linarith [H.base.makeCBox_x.1]
    exact mul_le_mul h2 hxadd (by linarith [H.xLo_pos])
      (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num)))
        P.f_pos).le
  unfold Scalar.AdmissibleParams.rhoLo
  change n / den <= ((makeCBox box).rhoLoUp : Real)
  have hform :
      ((makeCBox box).rhoLoUp : Real) = nUp / denLo := by
    rw [show (makeCBox box).rhoLoUp =
      (1 - (makeCBox box).x14Lo) * sqrtUpC (makeCBox box).aUp /
        (2 * sqrtLoC 2 * (makeCBox box).fLo *
          (1 + (makeCBox box).xLo)) by rfl]
    push_cast
    rfl
  rw [hform, div_le_div_iff₀ hdenPos hdenLoPos]
  exact mul_le_mul hn hden hdenLoPos.le hnUp0

lemma rhoLoLo_le_rhoLo
    (hfLo : (0 : Real) < (makeCBox box).fLo) :
    ((makeCBox box).rhoLoLo : Real) <= P.rhoLo := by
  let nLo : Real :=
    (1 - ((makeCBox box).x14Up : Real)) *
      ((sqrtLoC (makeCBox box).aLo : ℚ) : Real)
  let n : Real := (1 - P.x ^ 14) * Real.sqrt P.alpha
  let denUp : Real :=
    2 * ((sqrtUpC 2 : ℚ) : Real) * ((makeCBox box).fUp : Real) *
      (1 + ((makeCBox box).xUp : Real))
  let den : Real :=
    2 * Real.sqrt 2 * P.f * (1 + P.x)
  have hx14UpOne :
      ((makeCBox box).x14Up : Real) <= 1 := by
    simp only [makeCBox, Rat.cast_min]
    simpa only [Rat.cast_one] using
      (min_le_left (1 : Real)
        ((((roundUp (chartXQ box.e1 box.k1) (10 ^ 6)) ^ 14 : ℚ)) : Real))
  have hxsubLo : 0 <= 1 - ((makeCBox box).x14Up : Real) :=
    sub_nonneg.mpr hx14UpOne
  have hsqrtLo0 :
      0 <= ((sqrtLoC (makeCBox box).aLo : ℚ) : Real) := by
    have hc := (makeCBox_sqrt_components H.sqrtOK).2.2.1
    have hq : (0 : ℚ) <= sqrtLoC ((1 - box.e2) / 2) := by
      have hall : (0 : ℚ) <= sqrtLoC ((1 - box.e2) / 2) ∧
          sqrtLoC ((1 - box.e2) / 2) * sqrtLoC ((1 - box.e2) / 2) <=
            (1 - box.e2) / 2 ∧
          (1 - box.e2) / 2 <=
            sqrtUpC ((1 - box.e2) / 2) * sqrtUpC ((1 - box.e2) / 2) ∧
          0 <= sqrtUpC ((1 - box.e2) / 2) := by
        simpa [sqrtBracketOK] using hc
      exact hall.1
    simpa only [makeCBox] using (show (0 : Real) <=
      ((sqrtLoC ((1 - box.e2) / 2) : ℚ) : Real) by exact_mod_cast hq)
  have hn : nLo <= n := by
    dsimp [nLo, n]
    have hxsub : 0 <= 1 - P.x ^ 14 :=
      sub_nonneg.mpr (pow_le_one₀
        (div_nonneg P.alpha_nonneg P.p_pos.le) P.x_lt_one.le)
    exact mul_le_mul (sub_le_sub_left H.x14_le_x14Up 1)
      H.sqrt_alpha_lower hsqrtLo0 hxsub
  have hn0 : 0 <= n := by
    dsimp [n]
    exact mul_nonneg
      (sub_nonneg.mpr (pow_le_one₀
        (div_nonneg P.alpha_nonneg P.p_pos.le) P.x_lt_one.le))
      (Real.sqrt_nonneg _)
  have hdenPos : 0 < den := by
    dsimp [den]
    have hx0 : 0 <= P.x := div_nonneg P.alpha_nonneg P.p_pos.le
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num)))
        P.f_pos)
      (by linarith)
  have hdenUpPos : 0 < denUp := by
    dsimp [denUp]
    have hfUp : 0 < ((makeCBox box).fUp : Real) :=
      P.f_pos.trans_le H.f_le_fUp
    have hsqrtUp : 0 < ((sqrtUpC 2 : ℚ) : Real) :=
      (Real.sqrt_pos.2 (by norm_num)).trans_le H.sqrt_two_upper
    have hxUp0 := H.xUp_nonneg
    exact mul_pos (mul_pos (mul_pos (by norm_num) hsqrtUp) hfUp)
      (by linarith)
  have hden : den <= denUp := by
    dsimp [den, denUp]
    have h1 :
        2 * Real.sqrt 2 <= 2 * ((sqrtUpC 2 : ℚ) : Real) :=
      mul_le_mul_of_nonneg_left H.sqrt_two_upper (by norm_num)
    have h2 :
        2 * Real.sqrt 2 * P.f <=
          2 * ((sqrtUpC 2 : ℚ) : Real) * ((makeCBox box).fUp : Real) :=
      mul_le_mul h1 H.f_le_fUp P.f_pos.le
        (mul_nonneg (by norm_num)
          ((Real.sqrt_nonneg _).trans H.sqrt_two_upper))
    have hxadd :
        1 + P.x <= 1 + ((makeCBox box).xUp : Real) := by
      linarith [H.base.makeCBox_x.2]
    exact mul_le_mul h2 hxadd
      (by
        have hx0 : 0 <= P.x := div_nonneg P.alpha_nonneg P.p_pos.le
        linarith)
      (mul_pos
        (mul_pos (by norm_num)
          ((Real.sqrt_pos.2 (by norm_num)).trans_le H.sqrt_two_upper))
        (P.f_pos.trans_le H.f_le_fUp)).le
  unfold Scalar.AdmissibleParams.rhoLo
  change ((makeCBox box).rhoLoLo : Real) <= n / den
  have hform :
      ((makeCBox box).rhoLoLo : Real) = nLo / denUp := by
    rw [show (makeCBox box).rhoLoLo =
      (1 - (makeCBox box).x14Up) * sqrtLoC (makeCBox box).aLo /
        (2 * sqrtUpC 2 * (makeCBox box).fUp *
          (1 + (makeCBox box).xUp)) by rfl]
    push_cast
    rfl
  rw [hform, div_le_div_iff₀ hdenUpPos hdenPos]
  exact mul_le_mul hn hden hdenPos.le hn0

lemma cI_le_paymentCoeffI :
    ((makeCBox box).cI : Real) <= P.paymentCoeffI := by
  let baseLo : Real :=
    2 * (1 - ((makeCBox box).x14Up : Real)) *
      (1 - ((makeCBox box).y14Up : Real)) *
      ((box.k1 : Real) ^ 2)
  let base : Real :=
    2 * (1 - P.x ^ 14) * (1 - P.y ^ (P.m - 1)) * P.kappa ^ 2
  let denUp : Real :=
    (1 + ((makeCBox box).xUp : Real)) *
      (1 + ((makeCBox box).yUp : Real))
  let den : Real := (1 + P.x) * (1 + P.y)
  let rLo : Real :=
    (1 + 4 * ((makeCBox box).xiLo : Real)) /
      (1 + 2 * ((makeCBox box).xiLo : Real))
  let r : Real := (1 + 4 * P.xi) / (1 + 2 * P.xi)
  have hxLo0 : 0 <= 1 - ((makeCBox box).x14Up : Real) :=
    sub_nonneg.mpr H.x14Up_le_one
  have hyLo0 : 0 <= 1 - ((makeCBox box).y14Up : Real) :=
    sub_nonneg.mpr H.y14Up_le_one
  have hx0 : 0 <= 1 - P.x ^ 14 :=
    sub_nonneg.mpr (pow_le_one₀
      (div_nonneg P.alpha_nonneg P.p_pos.le) P.x_lt_one.le)
  have hy0 : 0 <= 1 - P.y ^ (P.m - 1) :=
    P.one_sub_y_pow_pos.le
  have hx :
      1 - ((makeCBox box).x14Up : Real) <= 1 - P.x ^ 14 :=
    sub_le_sub_left H.x14_le_x14Up 1
  have hy :
      1 - ((makeCBox box).y14Up : Real) <=
        1 - P.y ^ (P.m - 1) :=
    sub_le_sub_left H.y_pow_le_y14Up 1
  have hkSq :
      (box.k1 : Real) ^ 2 <= P.kappa ^ 2 :=
    pow_le_pow_left₀ H.base.k1_nonneg H.base.k_bounds.1 2
  have hbase : baseLo <= base := by
    dsimp [baseLo, base]
    have h1 :
        2 * (1 - ((makeCBox box).x14Up : Real)) <=
          2 * (1 - P.x ^ 14) :=
      mul_le_mul_of_nonneg_left hx (by norm_num)
    have h2 :
        2 * (1 - ((makeCBox box).x14Up : Real)) *
            (1 - ((makeCBox box).y14Up : Real)) <=
          2 * (1 - P.x ^ 14) * (1 - P.y ^ (P.m - 1)) :=
      mul_le_mul h1 hy hyLo0 (mul_nonneg (by norm_num) hx0)
    exact mul_le_mul h2 hkSq (sq_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num) hx0) hy0)
  have hbase0 : 0 <= base := by
    dsimp [base]
    positivity
  have hyUp0 : 0 <= ((makeCBox box).yUp : Real) :=
    P.y_nonneg.trans H.y_le_yUp
  have hden : den <= denUp := by
    dsimp [den, denUp]
    have hxadd :
        1 + P.x <= 1 + ((makeCBox box).xUp : Real) := by
      linarith [H.base.makeCBox_x.2]
    have hyadd :
        1 + P.y <= 1 + ((makeCBox box).yUp : Real) := by
      linarith [H.y_le_yUp]
    exact mul_le_mul hxadd hyadd (by linarith [P.y_nonneg])
      (by linarith [H.xUp_nonneg])
  have hdenPos : 0 < den := by
    dsimp [den]
    have hx0' : 0 <= P.x := div_nonneg P.alpha_nonneg P.p_pos.le
    exact mul_pos (by linarith) (by linarith [P.y_nonneg])
  have hdenUpPos : 0 < denUp := by
    dsimp [denUp]
    exact mul_pos (by linarith [H.xUp_nonneg]) (by linarith [hyUp0])
  have hfrac : baseLo / denUp <= base / den := by
    rw [div_le_div_iff₀ hdenUpPos hdenPos]
    exact mul_le_mul hbase hden hdenPos.le hbase0
  have hr : rLo <= r := by
    dsimp [rLo, r]
    exact paymentRatioI_mono H.xiLo_nonneg H.xi_lower
  have hrLo0 : 0 <= rLo := by
    dsimp [rLo]
    exact div_nonneg (by linarith [H.xiLo_nonneg])
      (by linarith [H.xiLo_nonneg])
  have hfracActual0 : 0 <= base / den :=
    div_nonneg hbase0 hdenPos.le
  have hmain : (baseLo / denUp) * rLo <= (base / den) * r :=
    mul_le_mul hfrac hr hrLo0 hfracActual0
  have hcForm :
      ((makeCBox box).cI : Real) = (baseLo / denUp) * rLo := by
    rw [show (makeCBox box).cI =
      2 * (1 - (makeCBox box).x14Up) *
          (1 - (makeCBox box).y14Up) * box.k1 ^ 2 *
          (1 + 4 * (makeCBox box).xiLo) /
        ((1 + (makeCBox box).xUp) * (1 + (makeCBox box).yUp) *
          (1 + 2 * (makeCBox box).xiLo)) by rfl]
    push_cast
    dsimp [baseLo, denUp, rLo]
    field_simp [hdenUpPos.ne']
  have hpForm :
      P.paymentCoeffI = (base / den) * r := by
    unfold Scalar.AdmissibleParams.paymentCoeffI
    dsimp [base, den, r]
    field_simp [hdenPos.ne']
  rw [hcForm, hpForm]
  exact hmain

lemma cI0_mul_kappa_sq_le_paymentCoeffI :
    ((makeCBox box).cI0 : Real) * P.kappa ^ 2 <= P.paymentCoeffI := by
  let baseLo : Real :=
    2 * (1 - ((makeCBox box).x14Up : Real)) *
      (1 - ((makeCBox box).y14Up : Real)) * P.kappa ^ 2
  let base : Real :=
    2 * (1 - P.x ^ 14) * (1 - P.y ^ (P.m - 1)) * P.kappa ^ 2
  let denUp : Real :=
    (1 + ((makeCBox box).xUp : Real)) *
      (1 + ((makeCBox box).yUp : Real))
  let den : Real := (1 + P.x) * (1 + P.y)
  let r : Real := (1 + 4 * P.xi) / (1 + 2 * P.xi)
  have hxLo0 : 0 <= 1 - ((makeCBox box).x14Up : Real) :=
    sub_nonneg.mpr H.x14Up_le_one
  have hyLo0 : 0 <= 1 - ((makeCBox box).y14Up : Real) :=
    sub_nonneg.mpr H.y14Up_le_one
  have hx0 : 0 <= 1 - P.x ^ 14 :=
    sub_nonneg.mpr (pow_le_one₀
      (div_nonneg P.alpha_nonneg P.p_pos.le) P.x_lt_one.le)
  have hy0 : 0 <= 1 - P.y ^ (P.m - 1) := P.one_sub_y_pow_pos.le
  have hx : 1 - ((makeCBox box).x14Up : Real) <= 1 - P.x ^ 14 :=
    sub_le_sub_left H.x14_le_x14Up 1
  have hy : 1 - ((makeCBox box).y14Up : Real) <=
      1 - P.y ^ (P.m - 1) :=
    sub_le_sub_left H.y_pow_le_y14Up 1
  have hbase : baseLo <= base := by
    dsimp [baseLo, base]
    have h1 :
        2 * (1 - ((makeCBox box).x14Up : Real)) <=
          2 * (1 - P.x ^ 14) :=
      mul_le_mul_of_nonneg_left hx (by norm_num)
    have h2 :
        2 * (1 - ((makeCBox box).x14Up : Real)) *
            (1 - ((makeCBox box).y14Up : Real)) <=
          2 * (1 - P.x ^ 14) * (1 - P.y ^ (P.m - 1)) :=
      mul_le_mul h1 hy hyLo0 (mul_nonneg (by norm_num) hx0)
    exact mul_le_mul_of_nonneg_right h2 (sq_nonneg P.kappa)
  have hbase0 : 0 <= base := by
    dsimp [base]
    positivity
  have hyUp0 : 0 <= ((makeCBox box).yUp : Real) :=
    P.y_nonneg.trans H.y_le_yUp
  have hden : den <= denUp := by
    dsimp [den, denUp]
    exact mul_le_mul
      (by linarith [H.base.makeCBox_x.2])
      (by linarith [H.y_le_yUp])
      (by linarith [P.y_nonneg])
      (by linarith [H.xUp_nonneg])
  have hdenPos : 0 < den := by
    dsimp [den]
    have hxP : 0 <= P.x := by
      unfold Scalar.AdmissibleParams.x
      exact div_nonneg P.alpha_nonneg P.p_pos.le
    exact mul_pos
      (by linarith [hxP])
      (by linarith [P.y_nonneg])
  have hdenUpPos : 0 < denUp := by
    dsimp [denUp]
    exact mul_pos (by linarith [H.xUp_nonneg]) (by linarith [hyUp0])
  have hfrac : baseLo / denUp <= base / den := by
    rw [div_le_div_iff₀ hdenUpPos hdenPos]
    exact mul_le_mul hbase hden hdenPos.le hbase0
  have hr : 1 <= r := by
    dsimp [r]
    rw [le_div_iff₀ (by linarith [P.xi_pos] : 0 < 1 + 2 * P.xi)]
    linarith [P.xi_pos]
  have hfrac0 : 0 <= base / den := div_nonneg hbase0 hdenPos.le
  have hmain : baseLo / denUp <= (base / den) * r :=
    hfrac.trans (by simpa using mul_le_mul_of_nonneg_left hr hfrac0)
  have hcForm :
      ((makeCBox box).cI0 : Real) * P.kappa ^ 2 = baseLo / denUp := by
    rw [show (makeCBox box).cI0 =
      2 * (1 - (makeCBox box).x14Up) *
          (1 - (makeCBox box).y14Up) /
        ((1 + (makeCBox box).xUp) * (1 + (makeCBox box).yUp)) by rfl]
    push_cast
    dsimp [baseLo, denUp]
    field_simp [hdenUpPos.ne']
  have hpForm : P.paymentCoeffI = (base / den) * r := by
    unfold Scalar.AdmissibleParams.paymentCoeffI
    dsimp [base, den, r]
    field_simp [hdenPos.ne']
  rw [hcForm, hpForm]
  exact hmain

lemma cII_le_paymentCoeffII
    (hfLo : (0 : Real) < (makeCBox box).fLo) :
    ((makeCBox box).cII : Real) <= P.paymentCoeffII := by
  let baseLo : Real :=
    ((sqrtLoC (2 * (makeCBox box).aLo : ℚ) : ℚ) : Real) *
      (1 - ((makeCBox box).y14Up : Real)) *
      ((makeCBox box).fLo : Real) * ((makeCBox box).dLo : Real)
  let base : Real :=
    Real.sqrt (2 * P.alpha) * (1 - P.y ^ (P.m - 1)) * P.f * P.d
  let denUp : Real :=
    ((makeCBox box).aUp : Real) ^ 3 *
      (1 + ((makeCBox box).yUp : Real))
  let den : Real := P.alpha ^ 3 * (1 + P.y)
  let rLo : Real :=
    (4 * ((makeCBox box).xiLo : Real) + 1) /
      (4 * ((makeCBox box).xiLo : Real) + 2)
  let r : Real := (4 * P.xi + 1) / (4 * P.xi + 2)
  have hsqrt0 :
      0 <= ((sqrtLoC (2 * (makeCBox box).aLo : ℚ) : ℚ) : Real) :=
    sqrtLoC_nonneg _
  have hyLo0 : 0 <= 1 - ((makeCBox box).y14Up : Real) :=
    sub_nonneg.mpr H.y14Up_le_one
  have hdLo0 : 0 <= ((makeCBox box).dLo : Real) := by
    simp only [makeCBox]
    push_cast
    exact mul_nonneg H.base.k1_nonneg
      (by
        have he1 : (0 : Real) < box.e1 :=
          lt_of_lt_of_le (by norm_num : (0 : Real) < (1 / 60 : ℚ))
            (by exact_mod_cast H.base.placed_rat.1)
        exact he1.le)
  have hy0 : 0 <= 1 - P.y ^ (P.m - 1) := P.one_sub_y_pow_pos.le
  have hy :
      1 - ((makeCBox box).y14Up : Real) <=
        1 - P.y ^ (P.m - 1) :=
    sub_le_sub_left H.y_pow_le_y14Up 1
  have hbase : baseLo <= base := by
    dsimp [baseLo, base]
    have h1 :
        ((sqrtLoC (2 * (makeCBox box).aLo : ℚ) : ℚ) : Real) *
            (1 - ((makeCBox box).y14Up : Real)) <=
          Real.sqrt (2 * P.alpha) * (1 - P.y ^ (P.m - 1)) :=
      mul_le_mul H.sqrt_two_alpha_lower hy hyLo0
        (Real.sqrt_nonneg _)
    have h2 :
        ((sqrtLoC (2 * (makeCBox box).aLo : ℚ) : ℚ) : Real) *
              (1 - ((makeCBox box).y14Up : Real)) *
              ((makeCBox box).fLo : Real) <=
          Real.sqrt (2 * P.alpha) * (1 - P.y ^ (P.m - 1)) * P.f :=
      mul_le_mul h1 H.fLo_le_f hfLo.le
        (mul_nonneg (Real.sqrt_nonneg _) hy0)
    exact mul_le_mul h2 H.base.makeCBox_d.1 hdLo0
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hy0) P.f_pos.le)
  have hbase0 : 0 <= base := by
    dsimp [base]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hy0) P.f_pos.le)
      P.d_pos.le
  have hyUp0 : 0 <= ((makeCBox box).yUp : Real) :=
    P.y_nonneg.trans H.y_le_yUp
  have hden : den <= denUp := by
    dsimp [den, denUp]
    have haPow :
        P.alpha ^ 3 <= ((makeCBox box).aUp : Real) ^ 3 :=
      pow_le_pow_left₀ P.alpha_nonneg H.base.makeCBox_alpha.2 3
    have hyadd :
        1 + P.y <= 1 + ((makeCBox box).yUp : Real) := by
      linarith [H.y_le_yUp]
    exact mul_le_mul haPow hyadd (by linarith [P.y_nonneg])
      (pow_nonneg (P.alpha_nonneg.trans H.base.makeCBox_alpha.2) 3)
  have hdenPos : 0 < den := by
    dsimp [den]
    exact mul_pos (pow_pos P.alpha_pos 3) (by linarith [P.y_nonneg])
  have hdenUpPos : 0 < denUp := by
    dsimp [denUp]
    exact mul_pos (pow_pos H.aUp_pos 3) (by linarith [hyUp0])
  have hfrac : baseLo / denUp <= base / den := by
    rw [div_le_div_iff₀ hdenUpPos hdenPos]
    exact mul_le_mul hbase hden hdenPos.le hbase0
  have hr : rLo <= r := by
    dsimp [rLo, r]
    exact paymentRatioII_mono H.xiLo_nonneg H.xi_lower
  have hrLo0 : 0 <= rLo := by
    dsimp [rLo]
    exact div_nonneg (by linarith [H.xiLo_nonneg])
      (by linarith [H.xiLo_nonneg])
  have hfracActual0 : 0 <= base / den :=
    div_nonneg hbase0 hdenPos.le
  have hmain : (baseLo / denUp) * rLo <= (base / den) * r :=
    mul_le_mul hfrac hr hrLo0 hfracActual0
  have hcForm :
      ((makeCBox box).cII : Real) = (baseLo / denUp) * rLo := by
    rw [show (makeCBox box).cII =
      sqrtLoC (2 * (makeCBox box).aLo) *
          (1 - (makeCBox box).y14Up) * (makeCBox box).fLo *
          (makeCBox box).dLo * (4 * (makeCBox box).xiLo + 1) /
        ((makeCBox box).aUp ^ 3 * (1 + (makeCBox box).yUp) *
          (4 * (makeCBox box).xiLo + 2)) by rfl]
    push_cast
    dsimp [baseLo, denUp, rLo]
    field_simp [hdenUpPos.ne']
  have hpForm :
      P.paymentCoeffII = (base / den) * r := by
    unfold Scalar.AdmissibleParams.paymentCoeffII
    dsimp [base, den, r]
    field_simp [hdenPos.ne']
  rw [hcForm, hpForm]
  exact hmain

lemma cLo_le_applicablePayment
    (hxi : P.xi <= 1)
    (hfLo : (0 : Real) < (makeCBox box).fLo) :
    ((makeCBox box).cLo : Real) <=
      if 2 * P.rhoLo * P.xi <= 1 then
        P.paymentCoeffI
      else
        P.paymentCoeffII := by
  have hxiBounds := H.makeCBox_xi hxi
  have hrhoLo := H.rhoLoLo_le_rhoLo hfLo
  have hrhoUp := H.rhoLo_le_rhoLoUp hfLo
  have hprodLo :
      2 * ((makeCBox box).rhoLoLo : Real) *
          ((makeCBox box).xiLo : Real) <=
        2 * P.rhoLo * P.xi := by
    have hmul :
        ((makeCBox box).rhoLoLo : Real) *
            ((makeCBox box).xiLo : Real) <=
          P.rhoLo * P.xi :=
      mul_le_mul hrhoLo H.xi_lower H.xiLo_nonneg P.rhoLo_pos.le
    nlinarith
  have hprodUp :
      2 * P.rhoLo * P.xi <=
        2 * ((makeCBox box).rhoLoUp : Real) *
          ((makeCBox box).xiUp : Real) := by
    have hmul :
        P.rhoLo * P.xi <=
          ((makeCBox box).rhoLoUp : Real) *
            ((makeCBox box).xiUp : Real) :=
      mul_le_mul hrhoUp hxiBounds.2 P.xi_pos.le
        (P.rhoLo_pos.le.trans hrhoUp)
    nlinarith
  by_cases hgate : 2 * P.rhoLo * P.xi <= 1
  · rw [if_pos hgate]
    have hcQ : (makeCBox box).cLo <= (makeCBox box).cI := by
      unfold CBoxData.cLo
      split_ifs with hUp hLo
      · exact le_rfl
      · exfalso
        have hLoR :
            1 < 2 * ((makeCBox box).rhoLoLo : Real) *
              ((makeCBox box).xiLo : Real) := by
          exact_mod_cast hLo
        linarith
      · exact min_le_left _ _
    have hc : ((makeCBox box).cLo : Real) <=
        ((makeCBox box).cI : Real) := by exact_mod_cast hcQ
    exact hc.trans H.cI_le_paymentCoeffI
  · rw [if_neg hgate]
    have hgate' : 1 < 2 * P.rhoLo * P.xi := lt_of_not_ge hgate
    have hcQ : (makeCBox box).cLo <= (makeCBox box).cII := by
      unfold CBoxData.cLo
      split_ifs with hUp hLo
      · exfalso
        have hUpR :
            2 * ((makeCBox box).rhoLoUp : Real) *
                ((makeCBox box).xiUp : Real) <= 1 := by
          exact_mod_cast hUp
        linarith
      · exact le_rfl
      · exact min_le_right _ _
    have hc : ((makeCBox box).cLo : Real) <=
        ((makeCBox box).cII : Real) := by exact_mod_cast hcQ
    exact hc.trans (H.cII_le_paymentCoeffII hfLo)

lemma cLo_le_normalized_payment
    (hxi : P.xi <= 1)
    (hfLo : (0 : Real) < (makeCBox box).fLo) :
    (P.m : Real) * ((makeCBox box).cLo : Real) <=
      P.C * psi P.xi P.rho /
        (P.alpha ^ 3 * P.p ^ (P.m - 2)) := by
  have hc := H.cLo_le_applicablePayment hxi hfLo
  by_cases hgate : 2 * P.rhoLo * P.xi <= 1
  · rw [if_pos hgate] at hc
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans
      (P.paymentCoeffI_le_normalized_psi hgate)
  · rw [if_neg hgate] at hc
    have hgate' : 1 < 2 * P.rhoLo * P.xi := lt_of_not_ge hgate
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans
      (P.paymentCoeffII_le_normalized_psi hgate')

end CAnalyticBoxContext

end OddCycleBound.RegionII.Certificate
