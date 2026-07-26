import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# A local Gibbs inequality

This is the only relative-entropy fact needed by the graphon-direct
junction-tree argument.  It is proved pointwise from `log u ≤ u - 1`.
-/

open MeasureTheory

namespace PureChordal

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

lemma integral_mul_log_div_nonpos
    {f g : X → ℝ}
    (hf_int : Integrable f ν)
    (hg_int : Integrable g ν)
    (hf_pos : ∀ᵐ x ∂ν, 0 < f x)
    (hg_pos : ∀ᵐ x ∂ν, 0 < g x)
    (hf_one : ∫ x, f x ∂ν = 1)
    (hg_one : ∫ x, g x ∂ν = 1)
    (hlog_int : Integrable (fun x ↦ f x * Real.log (g x / f x)) ν) :
    ∫ x, f x * Real.log (g x / f x) ∂ν ≤ 0 := by
  have hpoint :
      ∀ᵐ x ∂ν, f x * Real.log (g x / f x) ≤ g x - f x := by
    filter_upwards [hf_pos, hg_pos] with x hfx hgx
    calc
      f x * Real.log (g x / f x)
          ≤ f x * (g x / f x - 1) :=
        mul_le_mul_of_nonneg_left
          (Real.log_le_sub_one_of_pos (div_pos hgx hfx)) hfx.le
      _ = g x - f x := by
        rw [mul_sub, mul_one, mul_div_cancel₀ (g x) hfx.ne']
  have hle :
      (∫ x, f x * Real.log (g x / f x) ∂ν) ≤ ∫ x, g x - f x ∂ν :=
    integral_mono_ae hlog_int (hg_int.sub hf_int) hpoint
  rw [integral_sub hg_int hf_int, hg_one, hf_one, sub_self] at hle
  exact hle

/-- A bounded measurable logarithmic integrand is automatically integrable on
a finite measure space, which is the form used for uniformly positive graphon
densities. -/
lemma integral_mul_log_div_nonpos_of_bound
    [IsFiniteMeasure ν]
    {f g : X → ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_int : Integrable f ν) (hg_int : Integrable g ν)
    (hf_pos : ∀ᵐ x ∂ν, 0 < f x)
    (hg_pos : ∀ᵐ x ∂ν, 0 < g x)
    (hf_one : ∫ x, f x ∂ν = 1)
    (hg_one : ∫ x, g x ∂ν = 1)
    (C : ℝ)
    (hbound : ∀ x, ‖f x * Real.log (g x / f x)‖ ≤ C) :
    ∫ x, f x * Real.log (g x / f x) ∂ν ≤ 0 := by
  have hlog_meas :
      Measurable (fun x => f x * Real.log (g x / f x)) :=
    hf_meas.mul ((hg_meas.div hf_meas).log)
  have hlog_int :
      Integrable (fun x => f x * Real.log (g x / f x)) ν := by
    exact (integrable_const C).mono'
      hlog_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  exact integral_mul_log_div_nonpos hf_int hg_int
    hf_pos hg_pos hf_one hg_one hlog_int

/-- Gibbs with explicit common positive lower and finite upper bounds. -/
lemma integral_mul_log_div_nonpos_of_two_sided_bounds
    [IsFiniteMeasure ν]
    {f g : X → ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_int : Integrable f ν) (hg_int : Integrable g ν)
    (hf_one : ∫ x, f x ∂ν = 1)
    (hg_one : ∫ x, g x ∂ν = 1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hf_lower : ∀ x, a ≤ f x) (hg_lower : ∀ x, a ≤ g x)
    (hf_upper : ∀ x, f x ≤ b) (hg_upper : ∀ x, g x ≤ b) :
    ∫ x, f x * Real.log (g x / f x) ∂ν ≤ 0 := by
  let C := max |Real.log (a / b)| |Real.log (b / a)|
  have hbound :
      ∀ x, ‖f x * Real.log (g x / f x)‖ ≤ b * C := by
    intro x
    have hfx : 0 < f x := ha.trans_le (hf_lower x)
    have hgx : 0 < g x := ha.trans_le (hg_lower x)
    have hl : a / b ≤ g x / f x := by
      apply (div_le_div_iff₀ hb hfx).2
      exact mul_le_mul (hg_lower x) (hf_upper x)
        hfx.le hgx.le
    have hu : g x / f x ≤ b / a := by
      apply (div_le_div_iff₀ hfx ha).2
      exact mul_le_mul (hg_upper x) (hf_lower x)
        ha.le hb.le
    have hlogl :
        Real.log (a / b) ≤ Real.log (g x / f x) :=
      Real.log_le_log (div_pos ha hb) hl
    have hlogu :
        Real.log (g x / f x) ≤ Real.log (b / a) :=
      Real.log_le_log (div_pos hgx hfx) hu
    have habs :
        |Real.log (g x / f x)| ≤ C := by
      rw [abs_le]
      constructor
      · calc
          -C ≤ -|Real.log (a / b)| :=
            neg_le_neg (le_max_left _ _)
          _ ≤ Real.log (a / b) := neg_abs_le _
          _ ≤ Real.log (g x / f x) := hlogl
      · calc
          Real.log (g x / f x) ≤ Real.log (b / a) := hlogu
          _ ≤ |Real.log (b / a)| := le_abs_self _
          _ ≤ C := le_max_right _ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hfx]
    exact mul_le_mul (hf_upper x) habs (abs_nonneg _) hb.le
  apply integral_mul_log_div_nonpos_of_bound
    hf_meas hg_meas hf_int hg_int
  · exact Filter.Eventually.of_forall fun x =>
      ha.trans_le (hf_lower x)
  · exact Filter.Eventually.of_forall fun x =>
      ha.trans_le (hg_lower x)
  · exact hf_one
  · exact hg_one
  · exact hbound

lemma integral_mul_log_div_nonpos_of_exists_bounds
    [IsFiniteMeasure ν]
    {f g : X → ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_int : Integrable f ν) (hg_int : Integrable g ν)
    (hf_one : ∫ x, f x ∂ν = 1)
    (hg_one : ∫ x, g x ∂ν = 1)
    (hf_lower : ∃ a > 0, ∀ x, a ≤ f x)
    (hg_lower : ∃ a > 0, ∀ x, a ≤ g x)
    (hf_upper : ∃ b > 0, ∀ x, f x ≤ b)
    (hg_upper : ∃ b > 0, ∀ x, g x ≤ b) :
    ∫ x, f x * Real.log (g x / f x) ∂ν ≤ 0 := by
  rcases hf_lower with ⟨af, haf, hflo⟩
  rcases hg_lower with ⟨ag, hag, hglo⟩
  rcases hf_upper with ⟨bf, hbf, hfhi⟩
  rcases hg_upper with ⟨bg, hbg, hghi⟩
  apply integral_mul_log_div_nonpos_of_two_sided_bounds
    hf_meas hg_meas hf_int hg_int hf_one hg_one
    (lt_min haf hag) (lt_max_of_lt_left hbf)
  · exact fun x => (min_le_left af ag).trans (hflo x)
  · exact fun x => (min_le_right af ag).trans (hglo x)
  · exact fun x => (hfhi x).trans (le_max_left bf bg)
  · exact fun x => (hghi x).trans (le_max_right bf bg)

lemma integrable_mul_log_div_of_two_sided_bounds
    [IsFiniteMeasure ν]
    {f g : X → ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hf_lower : ∀ x, a ≤ f x) (hg_lower : ∀ x, a ≤ g x)
    (hf_upper : ∀ x, f x ≤ b) (hg_upper : ∀ x, g x ≤ b) :
    Integrable (fun x => f x * Real.log (g x / f x)) ν := by
  let C := max |Real.log (a / b)| |Real.log (b / a)|
  have hbound :
      ∀ x, ‖f x * Real.log (g x / f x)‖ ≤ b * C := by
    intro x
    have hfx : 0 < f x := ha.trans_le (hf_lower x)
    have hgx : 0 < g x := ha.trans_le (hg_lower x)
    have hl : a / b ≤ g x / f x := by
      apply (div_le_div_iff₀ hb hfx).2
      exact mul_le_mul (hg_lower x) (hf_upper x)
        hfx.le hgx.le
    have hu : g x / f x ≤ b / a := by
      apply (div_le_div_iff₀ hfx ha).2
      exact mul_le_mul (hg_upper x) (hf_lower x)
        ha.le hb.le
    have hlogl :
        Real.log (a / b) ≤ Real.log (g x / f x) :=
      Real.log_le_log (div_pos ha hb) hl
    have hlogu :
        Real.log (g x / f x) ≤ Real.log (b / a) :=
      Real.log_le_log (div_pos hgx hfx) hu
    have habs :
        |Real.log (g x / f x)| ≤ C := by
      rw [abs_le]
      constructor
      · calc
          -C ≤ -|Real.log (a / b)| :=
            neg_le_neg (le_max_left _ _)
          _ ≤ Real.log (a / b) := neg_abs_le _
          _ ≤ Real.log (g x / f x) := hlogl
      · calc
          Real.log (g x / f x) ≤ Real.log (b / a) := hlogu
          _ ≤ |Real.log (b / a)| := le_abs_self _
          _ ≤ C := le_max_right _ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hfx]
    exact mul_le_mul (hf_upper x) habs (abs_nonneg _) hb.le
  exact (integrable_const (b * C)).mono'
    (hf_meas.mul ((hg_meas.div hf_meas).log)).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

lemma integrable_mul_log_div_of_exists_bounds
    [IsFiniteMeasure ν]
    {f g : X → ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_lower : ∃ a > 0, ∀ x, a ≤ f x)
    (hg_lower : ∃ a > 0, ∀ x, a ≤ g x)
    (hf_upper : ∃ b > 0, ∀ x, f x ≤ b)
    (hg_upper : ∃ b > 0, ∀ x, g x ≤ b) :
    Integrable (fun x => f x * Real.log (g x / f x)) ν := by
  rcases hf_lower with ⟨af, haf, hflo⟩
  rcases hg_lower with ⟨ag, hag, hglo⟩
  rcases hf_upper with ⟨bf, hbf, hfhi⟩
  rcases hg_upper with ⟨bg, hbg, hghi⟩
  apply integrable_mul_log_div_of_two_sided_bounds
    hf_meas hg_meas (lt_min haf hag) (lt_max_of_lt_left hbf)
  · exact fun x => (min_le_left af ag).trans (hflo x)
  · exact fun x => (min_le_right af ag).trans (hglo x)
  · exact fun x => (hfhi x).trans (le_max_left bf bg)
  · exact fun x => (hghi x).trans (le_max_right bf bg)

end PureChordal
