import Taeyoung.Methods.Atlas148.LowEdge
import Taeyoung.Methods.Atlas148.Linear
import Taeyoung.Methods.PagePawBranch.Core

/-!
# Atlas 148: the leaf symmetrization

The note's paw estimate starts by averaging the three ways of putting the paw
leaf on a triangle vertex and applying arithmetic--geometric mean:

```
G ≥ ∫∫∫ W(x,y)W(x,z)W(y,z)·(d(x)d(y)d(z))^{1/3}.
```

Here the triangle integrand really is symmetric, so the averaging is genuine —
unlike the page-orbit step of `notes/triangle_book_page_paw_branch.tex`, which
turned out to be vacuous.

No permutation of a triple integral is needed, though.  Integrating the third
vertex first turns each of the three weights into a page operator,

```
∫ W(x,z)W(y,z)·d(z)^s dμ(z) = H_s(x,y),
```

so the arithmetic--geometric mean becomes the *pointwise* estimate

```
d(x)^{1/3}d(y)^{1/3}·H_{1/3}(x,y) ≤ (d(x)+d(y))/3·H₀(x,y) + H₁(x,y)/3,
```

and what remains is one `integral_mono` over the spine pair.  The three terms
on the right are all `G`: the first two by `Linear.pawG_eq_fst`, and the third
because `∫∫W·H₁` and `G` both collapse to `∫d·τ`, by `integral_edge_pageOp`
and `integral_edge_degree_pageOp` respectively.
-/

open MeasureTheory

namespace Taeyoung.Methods.Atlas148

open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.PureChordal
  Taeyoung.Methods.PagePawBranch

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `∫∫ W(x,y)·d(x)^{1/3}d(y)^{1/3}·H_{1/3}(x,y)`: the geometric-mean weighted
triangle density, with the third vertex already integrated. -/
noncomputable def triGeo (W : Graphon Ω μ) : ℝ :=
  ∫ q, W q.1 q.2 * (degree W q.1 ^ ((1:ℝ)/3) * degree W q.2 ^ ((1:ℝ)/3) *
    pageOp W ((1:ℝ)/3) q.1 q.2) ∂(μ.prod μ)

/-! ### The pointwise arithmetic--geometric mean -/

/-- Three-term AM--GM, applied inside the page integral. -/
theorem geo_page_le (W : Graphon Ω μ) (x y : Ω) :
    degree W x ^ ((1:ℝ)/3) * degree W y ^ ((1:ℝ)/3) * pageOp W ((1:ℝ)/3) x y
      ≤ (degree W x + degree W y) / 3 * pageOp W 0 x y + pageOp W 1 x y / 3 := by
  have hthird : (0:ℝ) ≤ 1/3 := by norm_num
  have hi13 := integrable_pageOp_integrand W hthird x y
  have hi0 := integrable_pageOp_integrand W (le_refl (0:ℝ)) x y
  have hi1 := integrable_pageOp_integrand W zero_le_one x y
  -- the left side, as one integral in `z`
  have hL : degree W x ^ ((1:ℝ)/3) * degree W y ^ ((1:ℝ)/3) *
      pageOp W ((1:ℝ)/3) x y
      = ∫ z, (degree W x ^ ((1:ℝ)/3) * degree W y ^ ((1:ℝ)/3)) *
          (W x z * W y z * degree W z ^ ((1:ℝ)/3)) ∂μ := by
    rw [pageOp, ← integral_const_mul]
  -- the right side, as one integral in `z`
  have hR : (degree W x + degree W y) / 3 * pageOp W 0 x y + pageOp W 1 x y / 3
      = ∫ z, (W x z * W y z) * ((degree W x + degree W y + degree W z) / 3) ∂μ := by
    have he : ∀ z, (W x z * W y z) * ((degree W x + degree W y + degree W z) / 3)
        = ((degree W x + degree W y) / 3) * (W x z * W y z * degree W z ^ (0:ℝ))
          + (1/3) * (W x z * W y z * degree W z ^ (1:ℝ)) := by
      intro z
      rw [Real.rpow_zero, Real.rpow_one]
      ring
    rw [integral_congr_ae (ae_of_all _ he),
      integral_add (hi0.const_mul _) (hi1.const_mul _),
      integral_const_mul, integral_const_mul, ← pageOp, ← pageOp]
    ring
  rw [hL, hR]
  refine integral_mono ((hi13.const_mul _).congr (ae_of_all _ fun z ↦ rfl))
    (by
      refine (((hi0.const_mul ((degree W x + degree W y) / 3)).add
        (hi1.const_mul (1/3))).congr (ae_of_all _ fun z ↦ ?_))
      show ((degree W x + degree W y) / 3) * (W x z * W y z * degree W z ^ (0:ℝ))
          + (1/3) * (W x z * W y z * degree W z ^ (1:ℝ))
          = W x z * W y z * ((degree W x + degree W y + degree W z) / 3)
      rw [Real.rpow_zero, Real.rpow_one]
      ring) fun z ↦ ?_
  have hw : 0 ≤ W x z * W y z := mul_nonneg (W.nonneg _ _) (W.nonneg _ _)
  have hamgm : degree W x ^ ((1:ℝ)/3) * degree W y ^ ((1:ℝ)/3) *
      degree W z ^ ((1:ℝ)/3)
      ≤ (degree W x + degree W y + degree W z) / 3 := by
    have h := Real.geom_mean_le_arith_mean3_weighted
      (by norm_num : (0:ℝ) ≤ 1/3) (by norm_num : (0:ℝ) ≤ 1/3)
      (by norm_num : (0:ℝ) ≤ 1/3) (degree_nonneg W x) (degree_nonneg W y)
      (degree_nonneg W z) (by norm_num)
    linarith [h]
  calc (degree W x ^ ((1:ℝ)/3) * degree W y ^ ((1:ℝ)/3)) *
        (W x z * W y z * degree W z ^ ((1:ℝ)/3))
      = (W x z * W y z) * (degree W x ^ ((1:ℝ)/3) * degree W y ^ ((1:ℝ)/3) *
          degree W z ^ ((1:ℝ)/3)) := by ring
    _ ≤ (W x z * W y z) * ((degree W x + degree W y + degree W z) / 3) :=
        mul_le_mul_of_nonneg_left hamgm hw

/-! ### The three copies of `G` -/

/-- `G = ∫ d·τ`. -/
theorem pawG_eq_integral_deg_rootedTriangle (W : Graphon Ω μ) :
    pawG W = ∫ z, degree W z * rootedTriangle W z ∂μ := by
  have h := integral_edge_degree_pageOp W (s := (1:ℝ)) zero_le_one
  rw [pawG]
  have he : ∀ q : Ω × Ω, W q.1 q.2 * pageOp W 0 q.1 q.2 * degree W q.2
      = W q.1 q.2 * (degree W q.2 ^ (1:ℝ) * pageOp W 0 q.1 q.2) := by
    intro q; rw [Real.rpow_one]; ring
  rw [integral_congr_ae (ae_of_all _ he), h]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  show degree W z ^ (1:ℝ) * rootedTriangle W z = degree W z * rootedTriangle W z
  rw [Real.rpow_one]

/-- `∫∫ W·H₁ = ∫ d·τ`, hence also `G`. -/
theorem integral_edge_pageOp_one (W : Graphon Ω μ) :
    (∫ q, W q.1 q.2 * pageOp W 1 q.1 q.2 ∂(μ.prod μ)) = pawG W := by
  rw [pawG_eq_integral_deg_rootedTriangle, integral_edge_pageOp W zero_le_one]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  show degree W z ^ (1:ℝ) * rootedTriangle W z = degree W z * rootedTriangle W z
  rw [Real.rpow_one]

/-! ### The symmetrization -/

set_option maxHeartbeats 800000 in
/-- **The leaf symmetrization.**  `∫∫∫ W³·(d d d)^{1/3} ≤ G`. -/
theorem triGeo_le_pawG (W : Graphon Ω μ) : triGeo W ≤ pawG W := by
  have hthird : (0:ℝ) ≤ 1/3 := by norm_num
  -- the two integrands
  have hiL : Integrable (fun q : Ω × Ω ↦ W q.1 q.2 *
      (degree W q.1 ^ ((1:ℝ)/3) * degree W q.2 ^ ((1:ℝ)/3) *
        pageOp W ((1:ℝ)/3) q.1 q.2)) (μ.prod μ) := by
    refine integrable_prod_of_bdd (W.measurable.mul
      ((((measurable_degree_rpow W hthird).comp measurable_fst).mul
        ((measurable_degree_rpow W hthird).comp measurable_snd)).mul
        (measurable_pageOp W hthird))) (C := 1) fun q ↦ ?_
    have h1 : 0 ≤ degree W q.1 ^ ((1:ℝ)/3) * degree W q.2 ^ ((1:ℝ)/3) *
        pageOp W ((1:ℝ)/3) q.1 q.2 :=
      mul_nonneg (mul_nonneg (degree_rpow_nonneg W _ _) (degree_rpow_nonneg W _ _))
        (pageOp_nonneg W hthird _ _)
    rw [abs_of_nonneg (mul_nonneg (W.nonneg _ _) h1)]
    exact mul_le_one₀ (W.le_one _ _) h1
      (mul_le_one₀ (mul_le_one₀ (degree_rpow_le_one W hthird _)
        (degree_rpow_nonneg W _ _) (degree_rpow_le_one W hthird _))
        (pageOp_nonneg W hthird _ _) (pageOp_le_one W hthird _ _))
  have hiA : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * pageOp W 0 q.1 q.2 * degree W q.1) (μ.prod μ) :=
    integrable_edge_page_deg_fst W
  have hiB : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * pageOp W 0 q.1 q.2 * degree W q.2) (μ.prod μ) :=
    integrable_edge_page_deg_snd W
  have hiC : Integrable (fun q : Ω × Ω ↦ W q.1 q.2 * pageOp W 1 q.1 q.2)
      (μ.prod μ) := by
    refine integrable_prod_of_bdd (W.measurable.mul (measurable_pageOp W zero_le_one))
      (C := 1) fun q ↦ ?_
    rw [abs_of_nonneg (mul_nonneg (W.nonneg _ _) (pageOp_nonneg W zero_le_one _ _))]
    exact mul_le_one₀ (W.le_one _ _) (pageOp_nonneg W zero_le_one _ _)
      (pageOp_le_one W zero_le_one _ _)
  have hiA3 : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * pageOp W 0 q.1 q.2 * degree W q.1 / 3) (μ.prod μ) := hiA.div_const 3
  have hiB3 : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * pageOp W 0 q.1 q.2 * degree W q.2 / 3) (μ.prod μ) := hiB.div_const 3
  have hiC3 : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * pageOp W 1 q.1 q.2 / 3) (μ.prod μ) := hiC.div_const 3
  have hiBC : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * pageOp W 0 q.1 q.2 * degree W q.2 / 3 +
        W q.1 q.2 * pageOp W 1 q.1 q.2 / 3) (μ.prod μ) :=
    (hiB3.add hiC3).congr (ae_of_all _ fun q ↦ rfl)
  have hiR : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * pageOp W 0 q.1 q.2 * degree W q.1 / 3 +
      (W q.1 q.2 * pageOp W 0 q.1 q.2 * degree W q.2 / 3 +
        W q.1 q.2 * pageOp W 1 q.1 q.2 / 3)) (μ.prod μ) :=
    (hiA3.add hiBC).congr (ae_of_all _ fun q ↦ rfl)
  -- the pointwise comparison
  have hmono : triGeo W ≤ ∫ q, (W q.1 q.2 * pageOp W 0 q.1 q.2 * degree W q.1 / 3 +
      (W q.1 q.2 * pageOp W 0 q.1 q.2 * degree W q.2 / 3 +
        W q.1 q.2 * pageOp W 1 q.1 q.2 / 3)) ∂(μ.prod μ) := by
    rw [triGeo]
    refine integral_mono hiL hiR fun q ↦ ?_
    have h := mul_le_mul_of_nonneg_left (geo_page_le W q.1 q.2) (W.nonneg q.1 q.2)
    calc W q.1 q.2 * (degree W q.1 ^ ((1:ℝ)/3) * degree W q.2 ^ ((1:ℝ)/3) *
          pageOp W ((1:ℝ)/3) q.1 q.2)
        ≤ W q.1 q.2 * ((degree W q.1 + degree W q.2) / 3 * pageOp W 0 q.1 q.2 +
            pageOp W 1 q.1 q.2 / 3) := h
      _ = _ := by ring
  -- the right-hand integral is `G`
  rw [integral_add hiA3 hiBC, integral_add hiB3 hiC3,
    integral_div, integral_div, integral_div, pawG_eq_fst, integral_edge_pageOp_one,
    ← pawG] at hmono
  linarith

end Taeyoung.Methods.Atlas148
