import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# A local Gibbs inequality

This is the only relative-entropy fact needed by the graphon-direct
junction-tree argument.  It is proved pointwise from `log u ≤ u - 1`.

The public entry points are `integral_mul_log_div_nonpos` (the bare inequality,
assuming integrability of the logarithmic integrand) and the
`*_of_exists_bounds` forms, which package the uniformly-positive-density case
used by the entropy-gluing argument.
-/

open MeasureTheory

namespace PureChordal

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- Gibbs' inequality in the form `∫ f · log (g / f) ≤ 0` for positive densities
of equal total mass, given integrability of the logarithmic integrand.  This is
the mathematical core; everything else supplies its hypotheses. -/
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

/-- The pointwise bound underlying integrability and nonpositivity for
uniformly two-sided-bounded densities: if `a ≤ u, v ≤ b` with `0 < a`, then
`‖u · log (v / u)‖ ≤ b · max |log (a/b)| |log (b/a)|`. -/
private lemma norm_mul_log_div_le
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {u v : ℝ} (hu_lower : a ≤ u) (hu_upper : u ≤ b)
    (hv_lower : a ≤ v) (hv_upper : v ≤ b) :
    ‖u * Real.log (v / u)‖ ≤ b * max |Real.log (a / b)| |Real.log (b / a)| := by
  set C := max |Real.log (a / b)| |Real.log (b / a)| with hC
  have hu : 0 < u := ha.trans_le hu_lower
  have hv : 0 < v := ha.trans_le hv_lower
  have hl : a / b ≤ v / u := by
    apply (div_le_div_iff₀ hb hu).2
    exact mul_le_mul hv_lower hu_upper hu.le hv.le
  have hupper : v / u ≤ b / a := by
    apply (div_le_div_iff₀ hu ha).2
    exact mul_le_mul hv_upper hu_lower ha.le hb.le
  have hlogl : Real.log (a / b) ≤ Real.log (v / u) :=
    Real.log_le_log (div_pos ha hb) hl
  have hlogu : Real.log (v / u) ≤ Real.log (b / a) :=
    Real.log_le_log (div_pos hv hu) hupper
  have habs : |Real.log (v / u)| ≤ C := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · calc
        -C ≤ -|Real.log (a / b)| := neg_le_neg (le_max_left _ _)
        _ ≤ Real.log (a / b) := neg_abs_le _
        _ ≤ Real.log (v / u) := hlogl
    · calc
        Real.log (v / u) ≤ Real.log (b / a) := hlogu
        _ ≤ |Real.log (b / a)| := le_abs_self _
        _ ≤ C := le_max_right _ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hu]
  exact mul_le_mul hu_upper habs (abs_nonneg _) hb.le

/-- The logarithmic integrand is integrable on a finite measure space once the
densities have common positive lower and finite upper bounds. -/
lemma integrable_mul_log_div_of_two_sided_bounds
    [IsFiniteMeasure ν]
    {f g : X → ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hf_lower : ∀ x, a ≤ f x) (hg_lower : ∀ x, a ≤ g x)
    (hf_upper : ∀ x, f x ≤ b) (hg_upper : ∀ x, g x ≤ b) :
    Integrable (fun x => f x * Real.log (g x / f x)) ν :=
  (integrable_const (b * max |Real.log (a / b)| |Real.log (b / a)|)).mono'
    (hf_meas.mul ((hg_meas.div hf_meas).log)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x =>
      norm_mul_log_div_le ha hb (hf_lower x) (hf_upper x) (hg_lower x) (hg_upper x))

/-- Gibbs with explicit common positive lower and finite upper bounds;
integrability of the logarithmic integrand is automatic. -/
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
    ∫ x, f x * Real.log (g x / f x) ∂ν ≤ 0 :=
  integral_mul_log_div_nonpos hf_int hg_int
    (Filter.Eventually.of_forall fun x => ha.trans_le (hf_lower x))
    (Filter.Eventually.of_forall fun x => ha.trans_le (hg_lower x))
    hf_one hg_one
    (integrable_mul_log_div_of_two_sided_bounds hf_meas hg_meas ha hb
      hf_lower hg_lower hf_upper hg_upper)

/-- Gibbs nonpositivity from existence of common positive lower and finite upper
bounds; this is the form the entropy-gluing argument applies. -/
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

/-- Integrability of the logarithmic integrand from existence of common positive
lower and finite upper bounds. -/
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
