import OddCycleBound.RegionII.Certificate.ChartIntervals

/-!
# Real semantics of a moderate Zone-C box

This file begins the trusted bridge from the rational data constructed by
`makeCBox` to an admissible real scalar point.  It contains only endpoint
geometry and chart algebra; square-root and battle-loop semantics are layered
on top in later files.
-/

noncomputable section

namespace OddCycleBound.RegionII.Certificate

open OddCycleBound.RegionII.Scalar

structure CBoxContext (P : AdmissibleParams) (box : RatBox) : Prop where
  point : box.Contains P.e P.kappa
  placed : wellPlacedC box = true

namespace CBoxContext

variable {P : AdmissibleParams} {box : RatBox} (H : CBoxContext P box)

include H

lemma placed_rat :
    zoneCRoot.e1 <= box.e1 ∧ box.e1 <= box.e2 ∧ box.e2 <= zoneCRoot.e2 ∧
      zoneCRoot.k1 <= box.k1 ∧ box.k1 <= box.k2 ∧ box.k2 <= zoneCRoot.k2 := by
  simpa [wellPlacedC] using H.placed

lemma e1_nonneg : (0 : Real) <= box.e1 := by
  have h := (placed_rat H).1
  norm_num [zoneCRoot] at h ⊢
  linarith

lemma e2_lt_one : (box.e2 : Real) < 1 := by
  have h := (placed_rat H).2.2.1
  have hR : (box.e2 : Real) <= ((997 / 3000 : ℚ) : Real) := by
    norm_num [zoneCRoot] at h
    exact_mod_cast h
  norm_num at hR ⊢
  linarith

lemma k1_nonneg : (0 : Real) <= box.k1 := by
  have h := (placed_rat H).2.2.2.1
  norm_num [zoneCRoot] at h ⊢
  exact_mod_cast h

lemma e_bounds :
    (box.e1 : Real) <= P.e ∧ P.e <= (box.e2 : Real) :=
  ⟨H.point.1, H.point.2.1⟩

lemma k_bounds :
    (box.k1 : Real) <= P.kappa ∧ P.kappa <= (box.k2 : Real) :=
  H.point.2.2

lemma alpha_lower :
    (((1 - box.e2) / 2 : ℚ) : Real) <= P.alpha := by
  rw [P.alpha_eq_chart]
  unfold chartAlpha
  push_cast
  linarith [(e_bounds H).2]

lemma alpha_upper :
    P.alpha <= (((1 - box.e1) / 2 : ℚ) : Real) := by
  rw [P.alpha_eq_chart]
  unfold chartAlpha
  push_cast
  linarith [(e_bounds H).1]

lemma d_lower :
    ((box.k1 * box.e1 : ℚ) : Real) <= P.d := by
  rw [← P.kappa_mul_e]
  push_cast
  calc
    (box.k1 : Real) * box.e1 <= P.kappa * box.e1 :=
      mul_le_mul_of_nonneg_right (k_bounds H).1 (e1_nonneg H)
    _ <= P.kappa * P.e :=
      mul_le_mul_of_nonneg_left (e_bounds H).1 P.kappa_pos.le

lemma d_upper :
    P.d <= ((box.k2 * box.e2 : ℚ) : Real) := by
  rw [← P.kappa_mul_e]
  push_cast
  have hk2 : (0 : Real) <= box.k2 :=
    ((k1_nonneg H).trans (k_bounds H).1).trans (k_bounds H).2
  calc
    P.kappa * P.e <= (box.k2 : Real) * P.e :=
      mul_le_mul_of_nonneg_right (k_bounds H).2 P.e_pos.le
    _ <= (box.k2 : Real) * box.e2 :=
      mul_le_mul_of_nonneg_left (e_bounds H).2 hk2

lemma x_lower :
    (chartXQ box.e2 box.k2 : Real) <= P.x := by
  rw [P.x_eq_chartXR, cast_chartXQ]
  exact chartXR_antitone P.e_pos.le (e_bounds H).2 (e2_lt_one H)
    P.kappa_pos.le (k_bounds H).2

lemma x_upper :
    P.x <= (chartXQ box.e1 box.k1 : Real) := by
  rw [P.x_eq_chartXR, cast_chartXQ]
  exact chartXR_antitone (e1_nonneg H) (e_bounds H).1
    (P.e_lt_third.trans (by norm_num))
    (k1_nonneg H) (k_bounds H).1

lemma q_lower :
    ((max (((1 - box.e2) / 2) - box.k2 * box.e2) (1 / 3) : ℚ) : Real)
      <= P.q := by
  rw [Rat.cast_max]
  rw [max_le_iff]
  constructor
  · push_cast
    have hd := d_upper H
    have ha := alpha_lower H
    unfold AdmissibleParams.d at hd
    push_cast at hd ha
    linarith
  · norm_num
    exact P.q_gt_third.le

lemma q_upper :
    P.q <= ((((1 - box.e1) / 2) - box.k1 * box.e1 : ℚ) : Real) := by
  push_cast
  have hd := d_lower H
  have ha := alpha_upper H
  unfold AdmissibleParams.d at hd
  push_cast at hd ha
  linarith

lemma p_lower :
    ((1 - (((1 - box.e1) / 2) - box.k1 * box.e1) : ℚ) : Real) <= P.p := by
  rw [P.p_eq_one_sub_q]
  push_cast
  have hq := q_upper H
  push_cast at hq
  linarith

lemma p_upper :
    P.p <=
      ((1 - max (((1 - box.e2) / 2) - box.k2 * box.e2) (1 / 3) : ℚ) : Real) := by
  rw [P.p_eq_one_sub_q]
  push_cast
  have hq := q_lower H
  rw [Rat.cast_max] at hq
  push_cast at hq
  linarith

lemma makeCBox_alpha :
    ((makeCBox box).aLo : Real) <= P.alpha ∧
      P.alpha <= ((makeCBox box).aUp : Real) := by
  simpa [makeCBox] using And.intro (alpha_lower H) (alpha_upper H)

lemma makeCBox_d :
    ((makeCBox box).dLo : Real) <= P.d ∧
      P.d <= ((makeCBox box).dUp : Real) := by
  simpa [makeCBox] using And.intro (d_lower H) (d_upper H)

lemma makeCBox_q :
    ((makeCBox box).qLo : Real) <= P.q ∧
      P.q <= ((makeCBox box).qUp : Real) := by
  simpa [makeCBox] using And.intro (q_lower H) (q_upper H)

lemma makeCBox_p :
    ((makeCBox box).pLo : Real) <= P.p ∧
      P.p <= ((makeCBox box).pUp : Real) := by
  simpa [makeCBox] using And.intro (p_lower H) (p_upper H)

lemma makeCBox_x :
    ((makeCBox box).xLo : Real) <= P.x ∧
      P.x <= ((makeCBox box).xUp : Real) := by
  simpa [makeCBox] using And.intro (x_lower H) (x_upper H)

end CBoxContext

end OddCycleBound.RegionII.Certificate
