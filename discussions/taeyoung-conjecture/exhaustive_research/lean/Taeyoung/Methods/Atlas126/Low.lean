import Taeyoung.Methods.Atlas126.Signs
import Taeyoung.Methods.Atlas126.Rows

/-!
# Atlas 126: low-density assembly

This file connects the three polynomial low-density planes to Fisher's sharp
triangle profile and to the already-formalized graphon integration.  The only
remaining assumptions are the scalar-plane certificates themselves. The
quadratic junction plane replaces plane C on `15/16 ≤ x ≤ 1`.
-/

open MeasureTheory

namespace Taeyoung.Methods.Atlas126

open Taeyoung Taeyoung.Methods Taeyoung.Methods.TriangleDensity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- All non-pointwise obligations for certificate A. -/
theorem graph126_bound_A_of_plane (W : Graphon Ω μ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ (5 : ℝ) / 8)
    (hp : cliqueDensity 2 W = lowDensity x)
    (hg : lowTriangle x ≤ cliqueDensity 3 W)
    (hplane : ScalarPlane (lowDensity x) (target (lowDensity x))
      (betaA x) (gammaA x) (lambdaA x) (lowTriangle x)) :
    target (lowDensity x) ≤ homDensity graph126 W := by
  have hgap0 := gapZeroA_nonneg hx0 hx1
  have hgap1 := gapOneA_nonneg hx0 hx1
  refine graph126_bound W (C := target (lowDensity x)) (beta := betaA x)
    (gamma := gammaA x) (lam := lambdaA x) (g := lowTriangle x)
    (lambdaA_nonneg hx0) hg ?_ ?_ ?_
  · rw [hp]
    simp only [gapZeroA] at hgap0
    linarith
  · rw [hp]
    simp only [gapOneA] at hgap1
    linarith
  · simpa only [hp] using hplane

/-- All non-pointwise obligations for certificate C. -/
theorem graph126_bound_C_of_plane (W : Graphon Ω μ) {x : ℝ}
    (hx0 : (5 : ℝ) / 8 ≤ x) (hx1 : x ≤ 1)
    (hp : cliqueDensity 2 W = lowDensity x)
    (hg : lowTriangle x ≤ cliqueDensity 3 W)
    (hplane : ScalarPlane (lowDensity x) (target (lowDensity x))
      (betaC x) (gammaC x) (lambdaC x) (lowTriangle x)) :
    target (lowDensity x) ≤ homDensity graph126 W := by
  have hgap0 := gapZeroC_nonneg hx0 hx1
  have hgap1 := gapOneC_nonneg hx0 hx1
  refine graph126_bound W (C := target (lowDensity x)) (beta := betaC x)
    (gamma := gammaC x) (lam := lambdaC x) (g := lowTriangle x)
    (lambdaC_nonneg hx0 hx1) hg ?_ ?_ ?_
  · rw [hp]
    simp only [gapZeroC] at hgap0
    linarith
  · rw [hp]
    simp only [gapOneC] at hgap1
    linarith
  · simpa only [hp] using hplane

/-- The corrected quadratic junction has the same integration interface. -/
theorem graph126_bound_J_of_plane (W : Graphon Ω μ) {x : ℝ}
    (hx0 : (15 : ℝ) / 16 ≤ x) (hx1 : x ≤ 1)
    (hp : cliqueDensity 2 W = lowDensity x)
    (hg : lowTriangle x ≤ cliqueDensity 3 W)
    (hplane : ScalarPlane (lowDensity x) (target (lowDensity x))
      (betaJ x) (gammaJ x) (lambdaJ x) (lowTriangle x)) :
    target (lowDensity x) ≤ homDensity graph126 W := by
  have hgap0 := gapZeroJ_nonneg hx0 hx1
  have hgap1 := gapOneJ_nonneg hx0 hx1
  refine graph126_bound W (C := target (lowDensity x)) (beta := betaJ x)
    (gamma := gammaJ x) (lam := lambdaJ x) (g := lowTriangle x)
    lambdaJ_nonneg hg ?_ ?_ ?_
  · rw [hp]
    simp only [gapZeroJ] at hgap0
    linarith
  · rw [hp]
    simp only [gapOneJ] at hgap1
    linarith
  · simpa only [hp] using hplane

/-- Once the three scalar certificate families are supplied, Fisher's parameter
chooses the correct one and proves the whole interval `[1/2,2/3]`. -/
theorem graph126_bound_low_of_planes (W : Graphon Ω μ)
    (hp0 : (1 : ℝ) / 2 ≤ cliqueDensity 2 W)
    (hp1 : cliqueDensity 2 W ≤ (2 : ℝ) / 3)
    (hplaneA : ∀ {x : ℝ}, 0 ≤ x → x ≤ (5 : ℝ) / 8 →
      ScalarPlane (lowDensity x) (target (lowDensity x))
        (betaA x) (gammaA x) (lambdaA x) (lowTriangle x))
    (hplaneC : ∀ {x : ℝ}, (5 : ℝ) / 8 ≤ x → x ≤ (15 : ℝ) / 16 →
      ScalarPlane (lowDensity x) (target (lowDensity x))
        (betaC x) (gammaC x) (lambdaC x) (lowTriangle x))
    (hplaneJ : ∀ {x : ℝ}, (15 : ℝ) / 16 ≤ x → x ≤ 1 →
      ScalarPlane (lowDensity x) (target (lowDensity x))
        (betaJ x) (gammaJ x) (lambdaJ x) (lowTriangle x)) :
    target (cliqueDensity 2 W) ≤ homDensity graph126 W := by
  by_cases heq : cliqueDensity 2 W = (1 : ℝ) / 2
  · rw [heq]
    norm_num [target]
    exact homDensity_nonneg graph126 W
  · have hpStrict : (1 : ℝ) / 2 < cliqueDensity 2 W :=
      lt_of_le_of_ne hp0 (Ne.symm heq)
    let x : ℝ := 3 * fisherParam (cliqueDensity 2 W)
    have hy := fisherParam_mem hp0
    have hx0 : 0 ≤ x := by
      simp only [x]
      linarith [hy.1]
    have hx1 : x ≤ 1 := by
      simp only [x]
      linarith [hy.2]
    have hpEq : cliqueDensity 2 W = lowDensity x := by
      symm
      calc
        lowDensity x = (1 + 2 * fisherParam (cliqueDensity 2 W) -
            3 * fisherParam (cliqueDensity 2 W) ^ 2) / 2 := by
          simpa only [x] using lowDensity_fisher (fisherParam (cliqueDensity 2 W))
        _ = cliqueDensity 2 W := fisherParam_quadratic hp1
    have hg : lowTriangle x ≤ cliqueDensity 3 W := by
      calc
        lowTriangle x = fisherProfile (cliqueDensity 2 W) := by
          rw [show x = 3 * fisherParam (cliqueDensity 2 W) from rfl,
            lowTriangle_fisher]
          rfl
        _ ≤ cliqueDensity 3 W := fisher_triangle_bound W hpStrict hp1
    rcases le_total x ((5 : ℝ) / 8) with hxA | hxC
    · rw [hpEq]
      exact graph126_bound_A_of_plane W hx0 hxA hpEq hg (hplaneA hx0 hxA)
    · rw [hpEq]
      rcases le_total x ((15 : ℝ) / 16) with hxC1 | hxJ
      · exact graph126_bound_C_of_plane W hxC hx1 hpEq hg (hplaneC hxC hxC1)
      · exact graph126_bound_J_of_plane W hxJ hx1 hpEq hg (hplaneJ hxJ hx1)

end Taeyoung.Methods.Atlas126
