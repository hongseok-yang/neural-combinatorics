import Taeyoung.Methods.PureChordal.Gibbs
import Taeyoung.Methods.OddWalk.Basic

/-!
# Gibbs' inequality in free-energy form

`Methods/PureChordal/Gibbs.lean` proves `∫ f log(g/f) ≤ 0` for two probability
densities.  The entropy argument of `notes/blekherman_raymond.tex` §2 uses it in
the equivalent *free-energy* form

```
∫ u · log (h / u)  ≤  log ∫ h ,
```

valid for a probability density `u` and any positive `h`: normalise `h` by its
own integral and the two statements differ by `log ∫ h · ∫ u = log ∫ h`.

This is the form that makes the chain induction of `OddWalk/Chain.lean`
possible without ever constructing a measure on `Ω⁶`.  The right-hand side is a
*partition function*, and the induction peels one edge of the walk at a time,
each step being one application of this lemma on `Ω` and one Fubini on `Ω²`.
-/

namespace Taeyoung.Methods.OddWalk

open MeasureTheory
open Taeyoung.Methods.PureChordal

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]

/-- A measurable function with a positive lower bound and a finite upper bound is
integrable on a probability space, and its integral lies between the bounds. -/
lemma integrable_of_bounds {h : X → ℝ} (hmeas : Measurable h)
    {b : ℝ} (hhi : ∀ x, h x ≤ b) {a : ℝ} (hlo : ∀ x, a ≤ h x) :
    Integrable h ν := by
  refine (integrable_const (μ := ν) (max |a| |b|)).mono' hmeas.aestronglyMeasurable
    (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · exact le_trans (neg_le_neg (le_max_left |a| |b|)) (le_trans (neg_abs_le a) (hlo x))
  · exact le_trans (hhi x) (le_trans (le_abs_self b) (le_max_right |a| |b|))

lemma le_integral_of_le {h : X → ℝ} (hint : Integrable h ν) {a : ℝ}
    (hlo : ∀ x, a ≤ h x) : a ≤ ∫ x, h x ∂ν := by
  calc a = ∫ _x : X, a ∂ν := by simp
    _ ≤ ∫ x, h x ∂ν := integral_mono (integrable_const _) hint hlo

/-- **Gibbs, free-energy form.**  For a probability density `u` and a positive
`h`, both bounded away from `0` and `∞`,

```
∫ u · log (h / u)  ≤  log ∫ h .
```
-/
theorem integral_mul_log_div_le_log_integral
    {u h : X → ℝ}
    (hu_meas : Measurable u) (hh_meas : Measurable h)
    (hu_one : ∫ x, u x ∂ν = 1)
    (hu_lo : ∃ a > 0, ∀ x, a ≤ u x) (hu_hi : ∃ b > 0, ∀ x, u x ≤ b)
    (hh_lo : ∃ a > 0, ∀ x, a ≤ h x) (hh_hi : ∃ b > 0, ∀ x, h x ≤ b) :
    ∫ x, u x * Real.log (h x / u x) ∂ν ≤ Real.log (∫ x, h x ∂ν) := by
  obtain ⟨au, hau, hulo⟩ := hu_lo
  obtain ⟨bu, hbu, huhi⟩ := hu_hi
  obtain ⟨ah, hah, hhlo⟩ := hh_lo
  obtain ⟨bh, hbh, hhhi⟩ := hh_hi
  have hu_int : Integrable u ν := integrable_of_bounds hu_meas huhi hulo
  have hh_int : Integrable h ν := integrable_of_bounds hh_meas hhhi hhlo
  set Z : ℝ := ∫ x, h x ∂ν with hZdef
  have hZ : 0 < Z := lt_of_lt_of_le hah (le_integral_of_le hh_int hhlo)
  -- the normalised density
  set g : X → ℝ := fun x ↦ h x / Z with hgdef
  have hg_meas : Measurable g := hh_meas.div_const Z
  have hg_one : ∫ x, g x ∂ν = 1 := by
    rw [hgdef]
    simp only []
    rw [integral_div, ← hZdef]
    field_simp
  have hg_int : Integrable g ν := hh_int.div_const Z
  have hg_lo : ∃ a > 0, ∀ x, a ≤ g x :=
    ⟨ah / Z, by positivity, fun x ↦ by
      show ah / Z ≤ h x / Z
      gcongr
      exact hhlo x⟩
  have hg_hi : ∃ b > 0, ∀ x, g x ≤ b :=
    ⟨bh / Z, by positivity, fun x ↦ by
      show h x / Z ≤ bh / Z
      gcongr
      exact hhhi x⟩
  have key := integral_mul_log_div_nonpos_of_exists_bounds
    hu_meas hg_meas hu_int hg_int hu_one hg_one
    ⟨au, hau, hulo⟩ hg_lo ⟨bu, hbu, huhi⟩ hg_hi
  -- rewrite the integrand
  have hpt : ∀ x, u x * Real.log (g x / u x)
      = u x * Real.log (h x / u x) - u x * Real.log Z := by
    intro x
    have hux : 0 < u x := lt_of_lt_of_le hau (hulo x)
    have hhx : 0 < h x := lt_of_lt_of_le hah (hhlo x)
    have hrw : g x / u x = (h x / u x) / Z := by
      rw [hgdef]; field_simp
    rw [hrw, Real.log_div (by positivity) (ne_of_gt hZ)]
    ring
  have hint1 : Integrable (fun x ↦ u x * Real.log (g x / u x)) ν :=
    integrable_mul_log_div_of_exists_bounds hu_meas hg_meas
      ⟨au, hau, hulo⟩ hg_lo ⟨bu, hbu, huhi⟩ hg_hi
  have hint2 : Integrable (fun x ↦ u x * Real.log Z) ν := hu_int.mul_const _
  have hint3 : Integrable (fun x ↦ u x * Real.log (h x / u x)) ν := by
    have : (fun x ↦ u x * Real.log (h x / u x))
        = fun x ↦ u x * Real.log (g x / u x) + u x * Real.log Z := by
      funext x; rw [hpt x]; ring
    rw [this]
    exact hint1.add hint2
  have hsplit : ∫ x, u x * Real.log (g x / u x) ∂ν
      = (∫ x, u x * Real.log (h x / u x) ∂ν) - Real.log Z := by
    calc ∫ x, u x * Real.log (g x / u x) ∂ν
        = ∫ x, (u x * Real.log (h x / u x) - u x * Real.log Z) ∂ν :=
          integral_congr_ae (ae_of_all _ hpt)
      _ = (∫ x, u x * Real.log (h x / u x) ∂ν)
            - ∫ x, u x * Real.log Z ∂ν := integral_sub hint3 hint2
      _ = (∫ x, u x * Real.log (h x / u x) ∂ν) - Real.log Z := by
          rw [integral_mul_const, hu_one, one_mul]
  linarith [hsplit ▸ key]

end Taeyoung.Methods.OddWalk
