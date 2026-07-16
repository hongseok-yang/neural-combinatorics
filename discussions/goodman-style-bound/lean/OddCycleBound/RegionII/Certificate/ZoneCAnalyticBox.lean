import OddCycleBound.RegionII.Certificate.ZoneCBox
import OddCycleBound.RegionII.Certificate.Soundness

/-!
# Square-root semantics for moderate Zone-C boxes

The executable checker brackets several square roots with exact integers.
Here those boolean brackets are connected to the real quantities `L` and `f`
of an admissible parameter point.
-/

noncomputable section

namespace OddCycleBound.RegionII.Certificate

open OddCycleBound.RegionII.Scalar

lemma makeCBox_sqrt_components {box : RatBox}
    (h : (makeCBox box).sqrtOK = true) :
    sqrtBracketOK (cL2Floor box) (cLLo box) (sqrtUpC (cL2Floor box)) = true ∧
    sqrtBracketOK (cL2Ceil box) (sqrtLoC (cL2Ceil box)) (cLRawUp box) = true ∧
    sqrtBracketOK ((1 - box.e2) / 2) (sqrtLoC ((1 - box.e2) / 2))
      (sqrtUpC ((1 - box.e2) / 2)) = true ∧
    sqrtBracketOK ((1 - box.e1) / 2) (sqrtLoC ((1 - box.e1) / 2))
      (sqrtUpC ((1 - box.e1) / 2)) = true ∧
    sqrtBracketOK 2 (sqrtLoC 2) (sqrtUpC 2) = true ∧
    sqrtBracketOK (2 * ((1 - box.e2) / 2))
      (sqrtLoC (2 * ((1 - box.e2) / 2)))
      (sqrtUpC (2 * ((1 - box.e2) / 2))) = true := by
  simp only [makeCBox, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  exact ⟨h1, h2, h3, h4, h5, h6⟩

structure CAnalyticBoxContext (P : AdmissibleParams) (box : RatBox)
    extends CBoxContext P box : Prop where
  sqrtOK : (makeCBox box).sqrtOK = true

namespace CAnalyticBoxContext

variable {P : AdmissibleParams} {box : RatBox}
  (H : CAnalyticBoxContext P box)

include H

lemma base : CBoxContext P box := H.toCBoxContext

lemma e2_nonneg : (0 : Real) <= box.e2 :=
  ((H.base.e1_nonneg.trans H.base.e_bounds.1).trans H.base.e_bounds.2)

lemma k2_nonneg : (0 : Real) <= box.k2 :=
  ((H.base.k1_nonneg.trans H.base.k_bounds.1).trans H.base.k_bounds.2)

lemma aLo_nonneg : (0 : Real) <= ((1 - box.e2) / 2 : ℚ) := by
  push_cast
  linarith [H.base.e2_lt_one]

lemma dUp_nonneg : (0 : Real) <= (box.k2 * box.e2 : ℚ) := by
  push_cast
  exact mul_nonneg H.k2_nonneg H.e2_nonneg

lemma cL2Floor_le_L_sq :
    (cL2Floor box : Real) <= P.L ^ 2 := by
  have ha := H.base.alpha_lower
  have hd := H.base.d_upper
  have he1 := H.base.e_bounds.1
  have he2 := H.base.e_bounds.2
  push_cast at ha hd he1 he2
  have hAlphaProd :
      (((1 - box.e2) / 2 : ℚ) : Real) * box.e1 <= P.alpha * P.e := by
    push_cast
    exact mul_le_mul ha he1 H.base.e1_nonneg P.alpha_nonneg
  have hsum :
      P.d + P.e <= ((box.k2 * box.e2 + box.e2 : ℚ) : Real) := by
    push_cast
    linarith
  have hDProd :
      P.d * (P.d + P.e) <=
        ((box.k2 * box.e2 : ℚ) : Real) *
          ((box.k2 * box.e2 + box.e2 : ℚ) : Real) := by
    push_cast
    push_cast at hsum
    exact mul_le_mul hd hsum (add_nonneg P.d_pos.le P.e_pos.le)
      (mul_nonneg H.k2_nonneg H.e2_nonneg)
  rw [P.L_sq_chart]
  unfold cL2Floor
  rw [Rat.cast_max, max_le_iff]
  constructor
  · norm_num
    have hs := sq_nonneg P.L
    rw [P.L_sq_chart] at hs
    linarith
  · push_cast
    push_cast at hAlphaProd hDProd
    linarith

lemma L_sq_le_cL2Ceil :
    P.L ^ 2 <= (cL2Ceil box : Real) := by
  have ha := H.base.alpha_upper
  have he := H.base.e_bounds.2
  have hq := H.base.q_upper
  push_cast at ha he hq
  have hAlphaProd :
      P.alpha * P.e <=
        (((1 - box.e1) / 2 : ℚ) : Real) * box.e2 := by
    push_cast
    exact mul_le_mul ha he P.e_pos.le (P.alpha_nonneg.trans ha)
  have hFirst :
    P.L ^ 2 <= (((1 - box.e1) / 2 : ℚ) : Real) * box.e2 := by
    rw [P.L_sq_chart]
    have hdterm : 0 <= P.d * (P.d + P.e) :=
      mul_nonneg P.d_pos.le (add_nonneg P.d_pos.le P.e_pos.le)
    push_cast
    push_cast at hAlphaProd
    linarith
  have hqUp0 :
      0 <= ((((1 - box.e1) / 2) - box.k1 * box.e1 : ℚ) : Real) := by
    push_cast
    exact P.q_nonneg.trans hq
  have hLq :
      P.L <= ((((1 - box.e1) / 2) - box.k1 * box.e1 : ℚ) : Real) := by
    push_cast
    exact P.L_lt_q.le.trans hq
  have hSecond :
      P.L ^ 2 <=
        ((((1 - box.e1) / 2) - box.k1 * box.e1 : ℚ) : Real) ^ 2 :=
    pow_le_pow_left₀ P.L_nonneg hLq 2
  unfold cL2Ceil
  rw [Rat.cast_min, le_min_iff]
  exact ⟨by simpa using hFirst, by simpa using hSecond⟩

lemma cLLo_le_L :
    (cLLo box : Real) <= P.L := by
  have hcomp := (makeCBox_sqrt_components H.sqrtOK).1
  have hsqrt := (sqrtBracketOK_sound hcomp).1
  calc
    (cLLo box : Real) <= Real.sqrt (cL2Floor box) := hsqrt
    _ <= Real.sqrt (P.L ^ 2) :=
      Real.sqrt_le_sqrt H.cL2Floor_le_L_sq
    _ = P.L := Real.sqrt_sq P.L_nonneg

lemma L_le_cLRawUp :
    P.L <= (cLRawUp box : Real) := by
  have hcomp := (makeCBox_sqrt_components H.sqrtOK).2.1
  have hsqrt := (sqrtBracketOK_sound hcomp).2
  calc
    P.L = Real.sqrt (P.L ^ 2) := (Real.sqrt_sq P.L_nonneg).symm
    _ <= Real.sqrt (cL2Ceil box) :=
      Real.sqrt_le_sqrt H.L_sq_le_cL2Ceil
    _ <= (cLRawUp box : Real) := hsqrt

lemma L_le_cLUp :
    P.L <= (cLUp box : Real) := by
  unfold cLUp
  rw [Rat.cast_min, le_min_iff]
  exact ⟨H.L_le_cLRawUp, P.L_lt_q.le.trans H.base.q_upper⟩

lemma fLo_le_f :
    ((makeCBox box).fLo : Real) <= P.f := by
  have hFirst :
      ((((1 - box.e2) / 2) - cLUp box : ℚ) : Real) <= P.f := by
    unfold AdmissibleParams.f
    push_cast
    have ha := H.base.alpha_lower
    have hL := H.L_le_cLUp
    push_cast at ha hL
    linarith
  have hSecond :
      ((box.k1 * box.e1 + (1 - 3 * box.e2) / 6 : ℚ) : Real) <= P.f := by
    have hd := H.base.d_lower
    have ha := H.base.alpha_lower
    have hgap := P.f_ge_d_add_delta
    push_cast at hd ha hgap ⊢
    linarith
  change
    ((max ((((1 - box.e2) / 2) - cLUp box : ℚ))
      (box.k1 * box.e1 + (1 - 3 * box.e2) / 6) : ℚ) : Real) <= P.f
  rw [Rat.cast_max, max_le_iff]
  exact ⟨hFirst, hSecond⟩

lemma f_le_fUp :
    P.f <= ((makeCBox box).fUp : Real) := by
  change P.f <= ((((1 - box.e1) / 2) - cLLo box : ℚ) : Real)
  unfold AdmissibleParams.f
  push_cast
  have ha := H.base.alpha_upper
  have hL := H.cLLo_le_L
  push_cast at ha hL
  linarith

lemma makeCBox_f :
    ((makeCBox box).fLo : Real) <= P.f ∧
      P.f <= ((makeCBox box).fUp : Real) :=
  ⟨H.fLo_le_f, H.f_le_fUp⟩

lemma two_mul_L_le_p : 2 * P.L <= P.p := by
  have hqSq : P.q ^ 2 <= P.alpha ^ 2 :=
    pow_le_pow_left₀ P.q_nonneg P.alpha_gt_q.le 2
  have hpq : P.p = 1 - P.q := rfl
  have hsquare : (2 * P.L) ^ 2 <= P.p ^ 2 := by
    have hLsq := P.L_sq
    rw [hpq] at hLsq ⊢
    nlinarith [hLsq, hqSq, sq_nonneg (1 - 3 * P.q)]
  exact (sq_le_sq₀ (mul_nonneg (by norm_num) P.L_nonneg) P.p_pos.le).mp hsquare

lemma y_le_half : P.y <= 1 / 2 := by
  unfold AdmissibleParams.y
  exact (div_le_iff₀ P.p_pos).2 (by linarith [H.two_mul_L_le_p])

lemma pLo_pos : 0 < ((makeCBox box).pLo : Real) := by
  simp only [makeCBox]
  push_cast
  have hkprod : (0 : Real) <= box.k1 * box.e1 :=
    mul_nonneg H.base.k1_nonneg H.base.e1_nonneg
  nlinarith [H.base.e1_nonneg]

lemma y_le_lUp_div_pLo :
    P.y <= (cLUp box : Real) / ((makeCBox box).pLo : Real) := by
  have hpLo := H.base.makeCBox_p.1
  unfold AdmissibleParams.y
  rw [div_le_div_iff₀ P.p_pos H.pLo_pos]
  exact mul_le_mul H.L_le_cLUp hpLo H.pLo_pos.le
    (P.L_nonneg.trans H.L_le_cLUp)

lemma s_le_sUp :
    P.s <= ((makeCBox box).sUp : Real) := by
  have hq := H.base.makeCBox_q.2
  have hp := H.base.makeCBox_p.1
  unfold AdmissibleParams.s
  have hs :
      P.q / P.p <=
        ((makeCBox box).qUp : Real) / ((makeCBox box).pLo : Real) := by
    rw [div_le_div_iff₀ P.p_pos H.pLo_pos]
    exact mul_le_mul hq hp H.pLo_pos.le (P.q_nonneg.trans hq)
  simpa only [makeCBox, Rat.cast_div] using hs

lemma y_le_yUp :
    P.y <= ((makeCBox box).yUp : Real) := by
  have hys : P.y <= ((makeCBox box).sUp : Real) :=
    P.y_lt_s.le.trans H.s_le_sUp
  change P.y <=
    ((min (min (cLUp box / (makeCBox box).pLo) (1 / 2))
      (makeCBox box).sUp : ℚ) : Real)
  rw [Rat.cast_min, le_min_iff, Rat.cast_min, le_min_iff]
  have hyL : P.y <= ((cLUp box / (makeCBox box).pLo : ℚ) : Real) := by
    rw [Rat.cast_div]
    exact H.y_le_lUp_div_pLo
  exact ⟨⟨hyL, by norm_num; exact H.y_le_half⟩, hys⟩

end CAnalyticBoxContext

end OddCycleBound.RegionII.Certificate
