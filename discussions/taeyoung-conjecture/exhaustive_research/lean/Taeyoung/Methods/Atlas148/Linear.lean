import Taeyoung.Methods.Atlas148.GeoMean
import Taeyoung.Methods.Atlas148.Scalar

/-!
# Atlas 148: the high-density linear estimate

The two-dimensional projection of
`notes/atlas148_paw_bias_hilbert_projection.tex` produces three edge integrals,

```
G = ∫∫ W·S·d(y),      D = ∫∫ W·S²,      L = ∫∫ W·S·d(x)d(y),
```

and `Δ = D - L`.  This file proves the note's linear estimate

```
p²G - qΔ ≥ p·c·f          (p ∈ [3/5, 1]),
```

which is what the final Cauchy--Schwarz in the two-dimensional space consumes.

The proof is the note's, in three moves.  `L` is *exactly* `∫∫ W·S·Z²`, because
`Z² = d(x)d(y)`.  `G` dominates `∫∫ W·S·Z`, because `W·S` is symmetric, so `G`
equals `∫∫ W·S·(d(x)+d(y))/2`, and `2Z ≤ d(x)+d(y)`.  Hence the whole left side
dominates `∫∫ W·F_p(Z,S)`, and `Scalar.line_le_edgeFn` replaces the integrand
by the supporting line `ℓ_p(Z)`.  Integrating a line is linear: what is left is
`p·cf + m_p(∫∫W·Z - p²)`, and both `m_p ≥ 0` and `∫∫W·Z ≥ p²` are already
proved.

The pointwise hypotheses of `Scalar.line_le_edgeFn` are exactly the three
bounds of `GeoMean`: `S ≤ Z` is Cauchy--Schwarz, `2Z - 1 ≤ S` combines the
codegree Goodman bound `d(x)+d(y)-1 ≤ S` with `2Z ≤ d(x)+d(y)`, and `S ≥ 0`.
-/

open MeasureTheory

namespace Taeyoung.Methods.Atlas148

open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The three edge integrals -/

/-- `G = ∫∫ W·S·d(y)`: the paw density, in the form the projection produces. -/
noncomputable def pawG (W : Graphon Ω μ) : ℝ :=
  ∫ q, W q.1 q.2 * pageOp W 0 q.1 q.2 * degree W q.2 ∂(μ.prod μ)

/-- `D = ∫∫ W·S²`. -/
noncomputable def bigD (W : Graphon Ω μ) : ℝ :=
  ∫ q, W q.1 q.2 * pageOp W 0 q.1 q.2 ^ 2 ∂(μ.prod μ)

/-- `L = ∫∫ W·S·d(x)d(y)`. -/
noncomputable def bigL (W : Graphon Ω μ) : ℝ :=
  ∫ q, W q.1 q.2 * pageOp W 0 q.1 q.2 * (degree W q.1 * degree W q.2) ∂(μ.prod μ)

/-- `Δ = D - L`. -/
noncomputable def bigDelta (W : Graphon Ω μ) : ℝ := bigD W - bigL W

/-! ### Symmetry of the codegree kernel -/

lemma pageOp_symm (W : Graphon Ω μ) (s : ℝ) (x y : Ω) :
    pageOp W s x y = pageOp W s y x := by
  simp only [pageOp]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  show W x z * W y z * degree W z ^ s = W y z * W x z * degree W z ^ s
  ring

/-! ### Bounded integrands -/

section Bounds

variable (W : Graphon Ω μ)

private lemma edgePage_nonneg (q : Ω × Ω) : 0 ≤ W q.1 q.2 * pageOp W 0 q.1 q.2 :=
  mul_nonneg (W.nonneg _ _) (pageOp_nonneg W le_rfl _ _)

private lemma edgePage_le_one (q : Ω × Ω) : W q.1 q.2 * pageOp W 0 q.1 q.2 ≤ 1 :=
  mul_le_one₀ (W.le_one _ _) (pageOp_nonneg W le_rfl _ _) (pageOp_le_one W le_rfl _ _)

/-- `W·S·h` is integrable for any measurable `h` with values in `[0,1]`. -/
lemma integrable_edgePage_mul {h : Ω × Ω → ℝ} (hm : Measurable h)
    (h0 : ∀ q, 0 ≤ h q) (h1 : ∀ q, h q ≤ 1) :
    Integrable (fun q : Ω × Ω ↦ W q.1 q.2 * pageOp W 0 q.1 q.2 * h q) (μ.prod μ) := by
  refine integrable_prod_of_bdd ((W.measurable.mul (measurable_pageOp W le_rfl)).mul hm)
    (C := 1) fun q ↦ ?_
  rw [abs_of_nonneg (mul_nonneg (edgePage_nonneg W q) (h0 q))]
  exact mul_le_one₀ (edgePage_le_one W q) (h0 q) (h1 q)

lemma integrable_edge_page_deg_fst :
    Integrable (Function.uncurry fun x y ↦
      W x y * pageOp W 0 x y * degree W x) (μ.prod μ) :=
  integrable_edgePage_mul W ((measurable_degree W).comp measurable_fst)
    (fun q ↦ degree_nonneg W _) fun q ↦ degree_le_one W _

lemma integrable_edge_page_deg_snd :
    Integrable (Function.uncurry fun x y ↦
      W x y * pageOp W 0 x y * degree W y) (μ.prod μ) :=
  integrable_edgePage_mul W ((measurable_degree W).comp measurable_snd)
    (fun q ↦ degree_nonneg W _) fun q ↦ degree_le_one W _

lemma integrable_edge_page_geo :
    Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * pageOp W 0 q.1 q.2 * geoDeg W q.1 q.2) (μ.prod μ) :=
  integrable_edgePage_mul W (measurable_geoDeg W)
    (fun q ↦ geoDeg_nonneg W _ _) fun q ↦ geoDeg_le_one W _ _

lemma integrable_edge_page_geo_sq :
    Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * pageOp W 0 q.1 q.2 * geoDeg W q.1 q.2 ^ 2) (μ.prod μ) :=
  integrable_edgePage_mul W ((measurable_geoDeg W).pow_const 2)
    (fun q ↦ sq_nonneg _)
    fun q ↦ pow_le_one₀ (geoDeg_nonneg W _ _) (geoDeg_le_one W _ _)

lemma integrable_bigD :
    Integrable (fun q : Ω × Ω ↦ W q.1 q.2 * pageOp W 0 q.1 q.2 ^ 2) (μ.prod μ) := by
  refine ((integrable_edgePage_mul W (measurable_pageOp W le_rfl)
    (fun q ↦ pageOp_nonneg W le_rfl _ _)
    fun q ↦ pageOp_le_one W le_rfl _ _)).congr (ae_of_all _ fun q ↦ ?_)
  show W q.1 q.2 * pageOp W 0 q.1 q.2 * pageOp W 0 q.1 q.2
      = W q.1 q.2 * pageOp W 0 q.1 q.2 ^ 2
  ring

lemma integrable_edge_geo :
    Integrable (fun q : Ω × Ω ↦ W q.1 q.2 * geoDeg W q.1 q.2) (μ.prod μ) := by
  refine integrable_prod_of_bdd (W.measurable.mul (measurable_geoDeg W))
    (C := 1) fun q ↦ ?_
  rw [abs_of_nonneg (mul_nonneg (W.nonneg _ _) (geoDeg_nonneg W _ _))]
  exact mul_le_one₀ (W.le_one _ _) (geoDeg_nonneg W _ _) (geoDeg_le_one W _ _)

lemma integrable_edge :
    Integrable (fun q : Ω × Ω ↦ W q.1 q.2) (μ.prod μ) :=
  integrable_prod_of_bdd W.measurable (C := 1) fun q ↦ by
    show |W q.1 q.2| ≤ 1
    rw [abs_of_nonneg (W.nonneg q.1 q.2)]; exact W.le_one q.1 q.2

end Bounds

/-! ### `G` is symmetric, and dominates the geometric-mean form -/

/-- Putting the leaf degree on either spine endpoint gives the same integral. -/
theorem pawG_eq_fst (W : Graphon Ω μ) :
    (∫ q, W q.1 q.2 * pageOp W 0 q.1 q.2 * degree W q.1 ∂(μ.prod μ)) = pawG W := by
  rw [pawG, ← integral_integral (integrable_edge_page_deg_fst W),
    ← integral_integral (integrable_edge_page_deg_snd W),
    integral_integral_swap (integrable_edge_page_deg_snd W)]
  refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
  refine integral_congr_ae (ae_of_all _ fun b ↦ ?_)
  show W a b * pageOp W 0 a b * degree W a = W b a * pageOp W 0 b a * degree W a
  rw [W.symm a b, pageOp_symm W 0 a b]

/-- **The arithmetic--geometric mean step.**  `∫∫ W·S·Z ≤ G`. -/
theorem integral_edge_page_geo_le (W : Graphon Ω μ) :
    (∫ q, W q.1 q.2 * pageOp W 0 q.1 q.2 * geoDeg W q.1 q.2 ∂(μ.prod μ)) ≤ pawG W := by
  have hi1 : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * pageOp W 0 q.1 q.2 * degree W q.1) (μ.prod μ) :=
    integrable_edge_page_deg_fst W
  have hi2 : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * pageOp W 0 q.1 q.2 * degree W q.2) (μ.prod μ) :=
    integrable_edge_page_deg_snd W
  have hisum : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * pageOp W 0 q.1 q.2 * degree W q.1 +
      W q.1 q.2 * pageOp W 0 q.1 q.2 * degree W q.2) (μ.prod μ) :=
    (hi1.add hi2).congr (ae_of_all _ fun q ↦ rfl)
  have htwo : (∫ q, W q.1 q.2 * pageOp W 0 q.1 q.2 * geoDeg W q.1 q.2 ∂(μ.prod μ)) * 2
      ≤ ∫ q, (W q.1 q.2 * pageOp W 0 q.1 q.2 * degree W q.1 +
          W q.1 q.2 * pageOp W 0 q.1 q.2 * degree W q.2) ∂(μ.prod μ) := by
    rw [← integral_mul_const]
    refine integral_mono ((integrable_edge_page_geo W).mul_const 2) hisum fun q ↦ ?_
    nlinarith [two_geoDeg_le W q.1 q.2, edgePage_nonneg W q]
  rw [integral_add hi1 hi2, pawG_eq_fst W, ← pawG] at htwo
  linarith

/-! ### The linear estimate -/

set_option maxHeartbeats 1000000 in
/-- **The high-density linear estimate.**  `p²G - qΔ ≥ pcf` for `p ∈ [3/5,1]`. -/
theorem linear_estimate (W : Graphon Ω μ) (hp0 : 3 / 5 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W * ((2 * cliqueDensity 2 W - 1) *
        (3 * cliqueDensity 2 W ^ 2 - 3 * cliqueDensity 2 W + 1))
      ≤ cliqueDensity 2 W ^ 2 * pawG W - (1 - cliqueDensity 2 W) * bigDelta W := by
  set p := cliqueDensity 2 W with hpdef
  have hp1 : p ≤ 1 := cliqueDensity_le_one 2 W
  have hp0' : (0:ℝ) < p := by linarith
  set Ig := ∫ q, W q.1 q.2 * pageOp W 0 q.1 q.2 * geoDeg W q.1 q.2 ∂(μ.prod μ) with hIg
  set Iz := ∫ q, W q.1 q.2 * geoDeg W q.1 q.2 ∂(μ.prod μ) with hIz
  -- `L` is exactly the `Z²` integral
  have hLZ : bigL W = ∫ q, W q.1 q.2 * pageOp W 0 q.1 q.2 * geoDeg W q.1 q.2 ^ 2
      ∂(μ.prod μ) := by
    rw [bigL]
    refine integral_congr_ae (ae_of_all _ fun q ↦ ?_)
    show W q.1 q.2 * pageOp W 0 q.1 q.2 * (degree W q.1 * degree W q.2)
        = W q.1 q.2 * pageOp W 0 q.1 q.2 * geoDeg W q.1 q.2 ^ 2
    rw [geoDeg, Real.sq_sqrt (mul_nonneg (degree_nonneg W _) (degree_nonneg W _))]
  -- measurability of the two comparison integrands
  have hmZ := measurable_geoDeg W
  have hmS := measurable_pageOp W (le_refl (0:ℝ))
  have hcline : Continuous fun z : ℝ ↦ line p z := by unfold line slope; fun_prop
  have hcedge : Continuous fun r : ℝ × ℝ ↦ edgeFn p r.1 r.2 := by unfold edgeFn; fun_prop
  have hiLine : Integrable (fun q : Ω × Ω ↦ W q.1 q.2 * line p (geoDeg W q.1 q.2))
      (μ.prod μ) := by
    refine integrable_prod_of_bdd (W.measurable.mul (hcline.measurable.comp hmZ))
      (C := 40) fun q ↦ ?_
    have hz0 := geoDeg_nonneg W q.1 q.2
    have hz1 := geoDeg_le_one W q.1 q.2
    have hm0 := slope_nonneg hp0 hp1
    have hm3 := slope_le_three hp0 hp1
    obtain ⟨hcf0, hcf1⟩ := cf_bounds hp0 hp1
    have hb : |line p (geoDeg W q.1 q.2)| ≤ 40 := by
      rw [line, abs_le]
      constructor <;>
        nlinarith [mul_le_mul_of_nonneg_left
            (by linarith : geoDeg W q.1 q.2 - p ≤ 1) hm0,
          mul_le_mul_of_nonneg_left
            (by linarith : (-1:ℝ) ≤ geoDeg W q.1 q.2 - p) hm0]
    calc |W q.1 q.2 * line p (geoDeg W q.1 q.2)|
        = W q.1 q.2 * |line p (geoDeg W q.1 q.2)| := by
          rw [abs_mul, abs_of_nonneg (W.nonneg _ _)]
      _ ≤ 1 * 40 := mul_le_mul (W.le_one _ _) hb (abs_nonneg _) zero_le_one
      _ = 40 := one_mul _
  have hiEdge : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * edgeFn p (geoDeg W q.1 q.2) (pageOp W 0 q.1 q.2)) (μ.prod μ) := by
    refine integrable_prod_of_bdd
      (W.measurable.mul (hcedge.measurable.comp (hmZ.prodMk hmS))) (C := 40) fun q ↦ ?_
    have hz0 := geoDeg_nonneg W q.1 q.2
    have hz1 := geoDeg_le_one W q.1 q.2
    have hs0 := pageOp_nonneg W (le_refl (0:ℝ)) q.1 q.2
    have hs1 := pageOp_le_one W (le_refl (0:ℝ)) q.1 q.2
    have hinner : p ^ 2 * geoDeg W q.1 q.2 + (1 - p) * geoDeg W q.1 q.2 ^ 2
        - (1 - p) * pageOp W 0 q.1 q.2 ≤ 2 := by nlinarith
    have hinner' : (-2 : ℝ) ≤ p ^ 2 * geoDeg W q.1 q.2 + (1 - p) * geoDeg W q.1 q.2 ^ 2
        - (1 - p) * pageOp W 0 q.1 q.2 := by nlinarith
    have hb : |edgeFn p (geoDeg W q.1 q.2) (pageOp W 0 q.1 q.2)| ≤ 40 := by
      rw [edgeFn, abs_le]
      constructor <;>
        nlinarith [mul_le_mul_of_nonneg_left hinner hs0,
          mul_le_mul_of_nonneg_left hinner' hs0, hs0, hs1]
    calc |W q.1 q.2 * edgeFn p (geoDeg W q.1 q.2) (pageOp W 0 q.1 q.2)|
        = W q.1 q.2 * |edgeFn p (geoDeg W q.1 q.2) (pageOp W 0 q.1 q.2)| := by
          rw [abs_mul, abs_of_nonneg (W.nonneg _ _)]
      _ ≤ 1 * 40 := mul_le_mul (W.le_one _ _) hb (abs_nonneg _) zero_le_one
      _ = 40 := one_mul _
  -- the pointwise scalar inequality, integrated
  have hpoint : (∫ q, W q.1 q.2 * line p (geoDeg W q.1 q.2) ∂(μ.prod μ))
      ≤ ∫ q, W q.1 q.2 * edgeFn p (geoDeg W q.1 q.2) (pageOp W 0 q.1 q.2)
          ∂(μ.prod μ) := by
    refine integral_mono hiLine hiEdge fun q ↦ ?_
    refine mul_le_mul_of_nonneg_left ?_ (W.nonneg _ _)
    refine line_le_edgeFn hp0 hp1 (geoDeg_nonneg W _ _) (geoDeg_le_one W _ _)
      (pageOp_nonneg W le_rfl _ _) ?_ (pageOp_zero_le_geoDeg W _ _)
    have hgood := le_pageOp_zero W q.1 q.2
    have hamgm := two_geoDeg_le W q.1 q.2
    linarith
  -- evaluate the two integrals
  have hedgeval : (∫ q, W q.1 q.2 * edgeFn p (geoDeg W q.1 q.2) (pageOp W 0 q.1 q.2)
        ∂(μ.prod μ)) = p ^ 2 * Ig + (1 - p) * bigL W - (1 - p) * bigD W := by
    have hpt : ∀ q : Ω × Ω,
        W q.1 q.2 * edgeFn p (geoDeg W q.1 q.2) (pageOp W 0 q.1 q.2)
          = p ^ 2 * (W q.1 q.2 * pageOp W 0 q.1 q.2 * geoDeg W q.1 q.2)
            + ((1 - p) * (W q.1 q.2 * pageOp W 0 q.1 q.2 * geoDeg W q.1 q.2 ^ 2)
              - (1 - p) * (W q.1 q.2 * pageOp W 0 q.1 q.2 ^ 2)) := by
      intro q; rw [edgeFn]; ring
    have hA : Integrable (fun q : Ω × Ω ↦
        p ^ 2 * (W q.1 q.2 * pageOp W 0 q.1 q.2 * geoDeg W q.1 q.2)) (μ.prod μ) :=
      (integrable_edge_page_geo W).const_mul _
    have hB : Integrable (fun q : Ω × Ω ↦
        (1 - p) * (W q.1 q.2 * pageOp W 0 q.1 q.2 * geoDeg W q.1 q.2 ^ 2)) (μ.prod μ) :=
      (integrable_edge_page_geo_sq W).const_mul _
    have hC : Integrable (fun q : Ω × Ω ↦
        (1 - p) * (W q.1 q.2 * pageOp W 0 q.1 q.2 ^ 2)) (μ.prod μ) :=
      (integrable_bigD W).const_mul _
    have hBC : Integrable (fun q : Ω × Ω ↦
        (1 - p) * (W q.1 q.2 * pageOp W 0 q.1 q.2 * geoDeg W q.1 q.2 ^ 2)
          - (1 - p) * (W q.1 q.2 * pageOp W 0 q.1 q.2 ^ 2)) (μ.prod μ) :=
      (hB.sub hC).congr (ae_of_all _ fun q ↦ rfl)
    rw [integral_congr_ae (ae_of_all _ hpt), integral_add hA hBC,
      integral_sub hB hC, integral_const_mul, integral_const_mul, integral_const_mul,
      hLZ, bigD, hIg]
    ring
  have hlineval : (∫ q, W q.1 q.2 * line p (geoDeg W q.1 q.2) ∂(μ.prod μ))
      = ((2 * p - 1) * (3 * p ^ 2 - 3 * p + 1) - slope p * p) * p + slope p * Iz := by
    have hpt : ∀ q : Ω × Ω, W q.1 q.2 * line p (geoDeg W q.1 q.2)
        = ((2 * p - 1) * (3 * p ^ 2 - 3 * p + 1) - slope p * p) * W q.1 q.2
          + slope p * (W q.1 q.2 * geoDeg W q.1 q.2) := by
      intro q; rw [line]; ring
    have hA : Integrable (fun q : Ω × Ω ↦
        ((2 * p - 1) * (3 * p ^ 2 - 3 * p + 1) - slope p * p) * W q.1 q.2) (μ.prod μ) :=
      (integrable_edge W).const_mul _
    have hB : Integrable (fun q : Ω × Ω ↦
        slope p * (W q.1 q.2 * geoDeg W q.1 q.2)) (μ.prod μ) :=
      (integrable_edge_geo W).const_mul _
    rw [integral_congr_ae (ae_of_all _ hpt), integral_add hA hB,
      integral_const_mul, integral_const_mul, integral_prod_edge, hIz]
  -- assemble
  have hGZ := integral_edge_page_geo_le W
  have hzz : p ^ 2 ≤ Iz := sq_le_integral_edge_geoDeg W
  have hm : 0 ≤ slope p := slope_nonneg hp0 hp1
  rw [hedgeval, hlineval] at hpoint
  have hstep : ((2 * p - 1) * (3 * p ^ 2 - 3 * p + 1) - slope p * p) * p + slope p * Iz
      ≥ p * ((2 * p - 1) * (3 * p ^ 2 - 3 * p + 1)) := by
    nlinarith [mul_le_mul_of_nonneg_left hzz hm]
  have hfin : p ^ 2 * Ig + (1 - p) * bigL W - (1 - p) * bigD W
      ≤ p ^ 2 * pawG W - (1 - p) * bigDelta W := by
    have : p ^ 2 * Ig ≤ p ^ 2 * pawG W :=
      mul_le_mul_of_nonneg_left hGZ (by positivity)
    rw [bigDelta]
    linarith
  linarith

end Taeyoung.Methods.Atlas148
