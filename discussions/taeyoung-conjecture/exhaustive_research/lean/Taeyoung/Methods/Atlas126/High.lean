import Taeyoung.Methods.Atlas126.Coefficients
import Taeyoung.Methods.Atlas126.Rows

/-!
# Atlas 126: high-density assembly

The large scalar certificate proves a pointwise supporting plane.  This file
supplies every other obligation needed to integrate the high-density plane:
coefficient signs, endpoint gaps, and the zero triangle multiplier.
-/

open MeasureTheory

namespace Taeyoung.Methods.Atlas126

open Taeyoung Taeyoung.Methods

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma target_eq_target126 (p : ℝ) : target p = target126 p := rfl

/-- On `2/3 ≤ p`, proving the high scalar plane is the only remaining input to
the graphon inequality. -/
theorem graph126_bound_high_of_plane (W : Graphon Ω μ)
    (hp : (2 : ℝ) / 3 ≤ cliqueDensity 2 W)
    (hplane : ScalarPlane (cliqueDensity 2 W)
      (target (cliqueDensity 2 W))
      (betaHigh (cliqueDensity 2 W))
      (gammaHigh (cliqueDensity 2 W)) 0 0) :
    target (cliqueDensity 2 W) ≤ homDensity graph126 W := by
  let p := cliqueDensity 2 W
  have hp' : (2 : ℝ) / 3 ≤ p := hp
  have hgap0 := gapZeroHigh_nonneg hp'
  have hgap1 := gapOneHigh_nonneg hp'
  refine graph126_bound W (C := target p) (beta := betaHigh p)
    (gamma := gammaHigh p) (lam := 0) (g := 0) ?_ ?_ ?_ ?_ ?_
  · norm_num
  · exact cliqueDensity_nonneg 3 W
  · simp only [zero_mul, add_zero]
    simp only [gapZeroHigh] at hgap0
    linarith
  · simp only [zero_mul, sub_zero, add_zero]
    simp only [gapOneHigh] at hgap1
    linarith
  · exact hplane

/-- The same reduction in the catalogue target's spelling. -/
theorem target126_bound_high_of_plane (W : Graphon Ω μ)
    (hp : (2 : ℝ) / 3 ≤ cliqueDensity 2 W)
    (hplane : ScalarPlane (cliqueDensity 2 W)
      (target126 (cliqueDensity 2 W))
      (betaHigh (cliqueDensity 2 W))
      (gammaHigh (cliqueDensity 2 W)) 0 0) :
    target126 (cliqueDensity 2 W) ≤ homDensity graph126 W := by
  rw [← target_eq_target126] at hplane ⊢
  exact graph126_bound_high_of_plane W hp hplane

end Taeyoung.Methods.Atlas126
