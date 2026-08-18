import Taeyoung.Methods.Atlas148.LowSymm
import Taeyoung.Methods.Atlas148.LowScalar
import Taeyoung.Methods.Atlas148.Density

/-!
# Atlas 148: the low-density interval

On `[1/2, 3/5]` the note bounds the density below by the square of the paw
density and the paw density below by `p·g(p)`, the sharp value.  This file
assembles that.

The paw estimate runs on the tilted probability measure

```
ν = d^{1/3}·μ / M,          M = ∫ d^{1/3},
```

under which the edge and triangle densities of the same kernel are

```
s = t(K₂,W;ν) = N/M²,       t(K₃,W;ν) = ∫∫∫W³(d d d)^{1/3} / M³,
```

with `N` the fractionally weighted edge of `LowEdge.lean`.  Writing `z = M³`,
the two inputs `LowScalar.paw_scalar_*` need are `z ≤ p` and `p⁵ ≤ z²s³`, and
the second is *identically* `p⁵ ≤ N³` because the `M`'s cancel — so both come
straight from `LowEdge.lean`.

The triangle density under `ν` is bounded below by Fisher's sharp profile when
`s ≤ 2/3` and by Goodman `s(2s-1)` when `s ≥ 2/3`; the two agree at `2/3`, so
no case is lost.  `LowSymm.triGeo_le_pawG` then carries `z·t(K₃,W;ν)` back to
`G`, and `LowScalar.low_comparison` converts `G ≥ p·g(p)` into the target.
-/

open MeasureTheory

namespace Taeyoung.Methods.Atlas148

open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.PureChordal
  Taeyoung.Methods.TriangleDensity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### `p ≤ M` -/

lemma degree_le_rpow_third (W : Graphon Ω μ) (x : Ω) :
    degree W x ≤ degree W x ^ ((1:ℝ)/3) := by
  rcases eq_or_lt_of_le (degree_nonneg W x) with h | h
  · rw [← h, Real.zero_rpow (by norm_num)]
  · calc degree W x = degree W x ^ (1:ℝ) := (Real.rpow_one _).symm
      _ ≤ degree W x ^ ((1:ℝ)/3) :=
        Real.rpow_le_rpow_of_exponent_ge h (degree_le_one W x) (by norm_num)

theorem le_cubeMoment (W : Graphon Ω μ) : cliqueDensity 2 W ≤ cubeMoment W := by
  rw [← integral_degree W, cubeMoment, momentR]
  exact integral_mono (integrable_degree W) (integrable_degree_rpow W (by norm_num))
    fun x ↦ degree_le_rpow_third W x

/-! ### The tilted measure -/

/-- The tilt density `d^{1/3}/M`. -/
noncomputable def tiltDens (W : Graphon Ω μ) (x : Ω) : ℝ :=
  degree W x ^ ((1:ℝ)/3) / cubeMoment W

lemma tiltDens_nonneg (W : Graphon Ω μ) (x : Ω) : 0 ≤ tiltDens W x :=
  div_nonneg (degree_rpow_nonneg W _ x) (cubeMoment_nonneg W)

lemma measurable_tiltDens (W : Graphon Ω μ) : Measurable (tiltDens W) :=
  (measurable_degree_rpow W (by norm_num)).div_const _

lemma integrable_tiltDens (W : Graphon Ω μ) : Integrable (tiltDens W) μ :=
  (integrable_degree_rpow W (by norm_num)).div_const _

lemma integral_tiltDens (W : Graphon Ω μ) (hM : 0 < cubeMoment W) :
    (∫ x, tiltDens W x ∂μ) = 1 := by
  simp only [tiltDens]
  rw [integral_div]
  exact div_self (ne_of_gt hM)

/-- `ν = d^{1/3}·μ/M`. -/
noncomputable def tiltMeasure (W : Graphon Ω μ) : Measure Ω :=
  μ.withDensity fun x ↦ ENNReal.ofReal (tiltDens W x)

lemma tiltMeasure_univ (W : Graphon Ω μ) (hM : 0 < cubeMoment W) :
    tiltMeasure W Set.univ = 1 := by
  rw [tiltMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_tiltDens W)
      (ae_of_all _ (tiltDens_nonneg W)), integral_tiltDens W hM]
  simp

lemma isProbabilityMeasure_tiltMeasure (W : Graphon Ω μ) (hM : 0 < cubeMoment W) :
    IsProbabilityMeasure (tiltMeasure W) :=
  ⟨tiltMeasure_univ W hM⟩

/-- Integration against the tilt. -/
theorem integral_tiltMeasure (W : Graphon Ω μ) (g : Ω → ℝ) :
    (∫ x, g x ∂(tiltMeasure W)) = ∫ x, tiltDens W x * g x ∂μ := by
  rw [tiltMeasure,
    integral_withDensity_eq_integral_toReal_smul
      ((measurable_tiltDens W).ennreal_ofReal)
      (ae_of_all _ fun x ↦ ENNReal.ofReal_lt_top) g]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  show (ENNReal.ofReal (tiltDens W x)).toReal • g x = tiltDens W x * g x
  rw [smul_eq_mul, ENNReal.toReal_ofReal (tiltDens_nonneg W x)]

/-- The same kernel, viewed as a graphon on the tilted space. -/
noncomputable def tiltGraphon (W : Graphon Ω μ) : Graphon Ω (tiltMeasure W) where
  toFun := W.toFun
  measurable := W.measurable
  nonneg := W.nonneg
  le_one := W.le_one
  symm := W.symm

/-! ### The two tilted densities, in `μ`-terms -/

/-- `t(K₂,W;ν) = N/M²`. -/
theorem tilt_edge_eq (W : Graphon Ω μ) :
    (∫ x, ∫ y, W x y ∂(tiltMeasure W) ∂(tiltMeasure W))
      = fracEdge W / cubeMoment W ^ 2 := by
  rw [integral_tiltMeasure]
  have hinner : ∀ x : Ω, tiltDens W x * (∫ y, W x y ∂(tiltMeasure W))
      = ∫ y, W x y * (degree W x ^ ((1:ℝ)/3) * degree W y ^ ((1:ℝ)/3))
          / cubeMoment W ^ 2 ∂μ := by
    intro x
    rw [integral_tiltMeasure, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    show tiltDens W x * (tiltDens W y * W x y)
        = W x y * (degree W x ^ ((1:ℝ)/3) * degree W y ^ ((1:ℝ)/3))
            / cubeMoment W ^ 2
    simp only [tiltDens]
    ring
  rw [integral_congr_ae (ae_of_all _ hinner)]
  have hstep : ∀ x : Ω, (∫ y, W x y *
      (degree W x ^ ((1:ℝ)/3) * degree W y ^ ((1:ℝ)/3)) / cubeMoment W ^ 2 ∂μ)
      = (∫ y, W x y * (degree W x ^ ((1:ℝ)/3) * degree W y ^ ((1:ℝ)/3)) ∂μ)
          / cubeMoment W ^ 2 := fun x ↦ integral_div _ _
  rw [integral_congr_ae (ae_of_all _ hstep), integral_div, fracEdge,
    integral_integral (integrable_fracEdge W)]

/-- `t(K₃,W;ν) = ∫∫∫W³(d d d)^{1/3} / M³`. -/
theorem tilt_triangle_eq (W : Graphon Ω μ) :
    (∫ a0, ∫ a1, ∫ a2, W a0 a1 * W a0 a2 * W a1 a2
        ∂(tiltMeasure W) ∂(tiltMeasure W) ∂(tiltMeasure W))
      = triGeo W / cubeMoment W ^ 3 := by
  have hthird : (0:ℝ) ≤ 1/3 := by norm_num
  -- the innermost integral
  have h2 : ∀ a0 a1 : Ω, (∫ a2, W a0 a1 * W a0 a2 * W a1 a2 ∂(tiltMeasure W))
      = W a0 a1 * pageOp W ((1:ℝ)/3) a0 a1 / cubeMoment W := by
    intro a0 a1
    rw [integral_tiltMeasure, pageOp, ← integral_const_mul, ← integral_div]
    refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
    show tiltDens W a2 * (W a0 a1 * W a0 a2 * W a1 a2)
        = W a0 a1 * (W a0 a2 * W a1 a2 * degree W a2 ^ ((1:ℝ)/3)) / cubeMoment W
    simp only [tiltDens]
    ring
  -- the middle integral
  have h1 : ∀ a0 : Ω, (∫ a1, ∫ a2, W a0 a1 * W a0 a2 * W a1 a2
        ∂(tiltMeasure W) ∂(tiltMeasure W))
      = (∫ a1, W a0 a1 * (degree W a1 ^ ((1:ℝ)/3) * pageOp W ((1:ℝ)/3) a0 a1) ∂μ)
          / cubeMoment W ^ 2 := by
    intro a0
    rw [integral_congr_ae (ae_of_all _ (h2 a0)), integral_tiltMeasure,
      ← integral_div]
    refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
    show tiltDens W a1 * (W a0 a1 * pageOp W ((1:ℝ)/3) a0 a1 / cubeMoment W)
        = W a0 a1 * (degree W a1 ^ ((1:ℝ)/3) * pageOp W ((1:ℝ)/3) a0 a1)
            / cubeMoment W ^ 2
    simp only [tiltDens]
    ring
  rw [integral_congr_ae (ae_of_all _ h1), integral_tiltMeasure]
  -- the outer integral
  have h0 : ∀ a0 : Ω, tiltDens W a0 *
      ((∫ a1, W a0 a1 * (degree W a1 ^ ((1:ℝ)/3) * pageOp W ((1:ℝ)/3) a0 a1) ∂μ)
        / cubeMoment W ^ 2)
      = (∫ a1, W a0 a1 * (degree W a0 ^ ((1:ℝ)/3) * degree W a1 ^ ((1:ℝ)/3) *
          pageOp W ((1:ℝ)/3) a0 a1) ∂μ) / cubeMoment W ^ 3 := by
    intro a0
    rw [← integral_div, ← integral_div, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
    show tiltDens W a0 * (W a0 a1 *
        (degree W a1 ^ ((1:ℝ)/3) * pageOp W ((1:ℝ)/3) a0 a1) / cubeMoment W ^ 2)
        = W a0 a1 * (degree W a0 ^ ((1:ℝ)/3) * degree W a1 ^ ((1:ℝ)/3) *
            pageOp W ((1:ℝ)/3) a0 a1) / cubeMoment W ^ 3
    simp only [tiltDens]
    ring
  rw [integral_congr_ae (ae_of_all _ h0)]
  have hi : Integrable (fun q : Ω × Ω ↦ W q.1 q.2 *
      (degree W q.1 ^ ((1:ℝ)/3) * degree W q.2 ^ ((1:ℝ)/3) *
        pageOp W ((1:ℝ)/3) q.1 q.2)) (μ.prod μ) := by
    refine integrable_prod_of_bdd (W.measurable.mul
      ((((measurable_degree_rpow W hthird).comp measurable_fst).mul
        ((measurable_degree_rpow W hthird).comp measurable_snd)).mul
        (measurable_pageOp W hthird))) (C := 1) fun q ↦ ?_
    have h1' : 0 ≤ degree W q.1 ^ ((1:ℝ)/3) * degree W q.2 ^ ((1:ℝ)/3) *
        pageOp W ((1:ℝ)/3) q.1 q.2 :=
      mul_nonneg (mul_nonneg (degree_rpow_nonneg W _ _) (degree_rpow_nonneg W _ _))
        (pageOp_nonneg W hthird _ _)
    rw [abs_of_nonneg (mul_nonneg (W.nonneg _ _) h1')]
    exact mul_le_one₀ (W.le_one _ _) h1'
      (mul_le_one₀ (mul_le_one₀ (degree_rpow_le_one W hthird _)
        (degree_rpow_nonneg W _ _) (degree_rpow_le_one W hthird _))
        (pageOp_nonneg W hthird _ _) (pageOp_le_one W hthird _ _))
  rw [integral_div, triGeo, integral_integral hi]

/-! ### The projection at `λ = 0` -/

/-- `G² ≤ T`, the projection with the multiplier switched off. -/
theorem sq_pawG_le_bigT (W : Graphon Ω μ) : pawG W ^ 2 ≤ bigT W := by
  have hfib : ∀ x : Ω, gFib W x ^ 2 ≤ fibNormSq W x := fun x ↦ by
    have h := fibOp_sq_lower W x 0
    rw [fibNormSq]
    linarith [h]
  have hmono : (∫ x, gFib W x ^ 2 ∂μ) ≤ bigT W :=
    integral_mono (integrable_gFib_sq W) (integrable_fibNormSq W) hfib
  have hjen : pawG W ^ 2 ≤ ∫ x, gFib W x ^ 2 ∂μ := by
    rw [← integral_gFib W]
    exact sq_integral_le (gFib W) (integrable_gFib W) (integrable_gFib_sq W)
  linarith

/-! ### The paw estimate, and the low interval -/

lemma bigT_nonneg (W : Graphon Ω μ) : 0 ≤ bigT W :=
  integral_nonneg fun x ↦ fibNormSq_nonneg W x

set_option maxHeartbeats 1000000 in
/-- **The sharp paw bound.**  `G ≥ p·g(p)` for `1/2 < p ≤ 3/5`. -/
theorem pawG_ge (W : Graphon Ω μ) (hlo : 1 / 2 < cliqueDensity 2 W)
    (hhi : cliqueDensity 2 W ≤ 3 / 5) :
    paramEdge (fisherParam (cliqueDensity 2 W)) *
      paramProfile (fisherParam (cliqueDensity 2 W)) ≤ pawG W := by
  have hp0 : (0:ℝ) < cliqueDensity 2 W := by linarith
  have hM : 0 < cubeMoment W := lt_of_lt_of_le hp0 (le_cubeMoment W)
  haveI := isProbabilityMeasure_tiltMeasure W hM
  obtain ⟨hy0, hy3⟩ := fisherParam_mem (p := cliqueDensity 2 W) (by linarith)
  have hpy : paramEdge (fisherParam (cliqueDensity 2 W)) = cliqueDensity 2 W :=
    paramEdge_fisherParam (by linarith)
  have hy8 : fisherParam (cliqueDensity 2 W) ≤ 1 / 8 :=
    param_le_eighth hy0 hy3 (by rw [hpy]; linarith)
  -- the tilted edge and triangle densities
  have hsval : cliqueDensity 2 (tiltGraphon W) = fracEdge W / cubeMoment W ^ 2 := by
    rw [← integral_degree (tiltGraphon W)]
    exact tilt_edge_eq W
  have hTval : cliqueDensity 3 (tiltGraphon W) = triGeo W / cubeMoment W ^ 3 := by
    rw [cliqueDensity_three_eq (tiltGraphon W)]
    exact tilt_triangle_eq W
  have hM3 : (0:ℝ) < cubeMoment W ^ 3 := by positivity
  have hzT : cubeMoment W ^ 3 * cliqueDensity 3 (tiltGraphon W) = triGeo W := by
    rw [hTval]
    field_simp
  -- the two hypotheses of the scalar lemmas
  have hz0 : (0:ℝ) ≤ cubeMoment W ^ 3 := by positivity
  have hzpC : cubeMoment W ^ 3 ≤ cliqueDensity 2 W := cube_cubeMoment_le W
  have hkeyC : cliqueDensity 2 W ^ 5
      ≤ (cubeMoment W ^ 3) ^ 2 * cliqueDensity 2 (tiltGraphon W) ^ 3 := by
    rw [hsval]
    have hne : cubeMoment W ≠ 0 := ne_of_gt hM
    calc cliqueDensity 2 W ^ 5 ≤ fracEdge W ^ 3 := pow_five_le_fracEdge_cube W
      _ = (cubeMoment W ^ 3) ^ 2 * (fracEdge W / cubeMoment W ^ 2) ^ 3 := by
          field_simp
  have hzp : cubeMoment W ^ 3 ≤ paramEdge (fisherParam (cliqueDensity 2 W)) := by
    rw [hpy]; exact hzpC
  have hkey : paramEdge (fisherParam (cliqueDensity 2 W)) ^ 5
      ≤ (cubeMoment W ^ 3) ^ 2 * cliqueDensity 2 (tiltGraphon W) ^ 3 := by
    rw [hpy]; exact hkeyC
  -- Fisher below `2/3`, Goodman above it
  have hmain : paramEdge (fisherParam (cliqueDensity 2 W)) *
      paramProfile (fisherParam (cliqueDensity 2 W))
      ≤ cubeMoment W ^ 3 * cliqueDensity 3 (tiltGraphon W) := by
    rcases le_or_gt (cliqueDensity 2 (tiltGraphon W)) (2 / 3) with hcase | hcase
    · -- `p ≤ s`, so Fisher applies
      have hs0 : 0 ≤ cliqueDensity 2 (tiltGraphon W) :=
        cliqueDensity_nonneg 2 (tiltGraphon W)
      have hz2 : (cubeMoment W ^ 3) ^ 2 ≤ cliqueDensity 2 W ^ 2 := by
        nlinarith [hz0, hzpC]
      have hstep : cliqueDensity 2 W ^ 2 * cliqueDensity 2 W ^ 3
          ≤ cliqueDensity 2 W ^ 2 * cliqueDensity 2 (tiltGraphon W) ^ 3 := by
        calc cliqueDensity 2 W ^ 2 * cliqueDensity 2 W ^ 3
            = cliqueDensity 2 W ^ 5 := by ring
          _ ≤ (cubeMoment W ^ 3) ^ 2 * cliqueDensity 2 (tiltGraphon W) ^ 3 := hkeyC
          _ ≤ cliqueDensity 2 W ^ 2 * cliqueDensity 2 (tiltGraphon W) ^ 3 :=
              mul_le_mul_of_nonneg_right hz2 (pow_nonneg hs0 3)
      have hcube : cliqueDensity 2 W ^ 3 ≤ cliqueDensity 2 (tiltGraphon W) ^ 3 :=
        le_of_mul_le_mul_left hstep (pow_pos hp0 2)
      have hps : cliqueDensity 2 W ≤ cliqueDensity 2 (tiltGraphon W) :=
        le_of_pow_le_pow_left₀ (n := 3) three_ne_zero hs0 hcube
      have hslo : 1 / 2 < cliqueDensity 2 (tiltGraphon W) := by linarith
      obtain ⟨h20, h23⟩ := fisherParam_mem
        (p := cliqueDensity 2 (tiltGraphon W)) (by linarith)
      have hpy2 : paramEdge (fisherParam (cliqueDensity 2 (tiltGraphon W)))
          = cliqueDensity 2 (tiltGraphon W) := paramEdge_fisherParam hcase
      have hfish := fisher_triangle_bound (tiltGraphon W) hslo hcase
      rw [fisherProfile_eq] at hfish
      refine paw_scalar_fisher hy0 hy8 h20 h23 hz0 hzp ?_ hfish
      rw [hpy2]
      exact hkey
    · have hs1 : cliqueDensity 2 (tiltGraphon W) ≤ 1 :=
        cliqueDensity_le_one 2 (tiltGraphon W)
      have hgood := goodman_triangle_bound (tiltGraphon W) (by linarith)
      exact paw_scalar_goodman hy0 hy8 hcase.le hs1 hz0 hkey hgood
  rw [hzT] at hmain
  exact le_trans hmain (triGeo_le_pawG W)

set_option maxHeartbeats 1000000 in
/-- **The low-density interval.**  `t ≥ p(2p-1)²(3p²-3p+1)` for `1/2 ≤ p ≤ 3/5`. -/
theorem homDensity_graph148_low (W : Graphon Ω μ) (hlo : 1 / 2 ≤ cliqueDensity 2 W)
    (hhi : cliqueDensity 2 W ≤ 3 / 5) :
    cliqueDensity 2 W * (2 * cliqueDensity 2 W - 1) ^ 2 *
        (3 * cliqueDensity 2 W ^ 2 - 3 * cliqueDensity 2 W + 1)
      ≤ homDensity graph148 W := by
  rw [homDensity_graph148_eq_bigT]
  rcases eq_or_lt_of_le hlo with hhalf | hgt
  · have : (2 * cliqueDensity 2 W - 1) = 0 := by rw [← hhalf]; ring
    rw [this]
    simpa using bigT_nonneg W
  · have hG := pawG_ge W hgt hhi
    obtain ⟨hy0, hy3⟩ := fisherParam_mem (p := cliqueDensity 2 W) (by linarith)
    have hpy : paramEdge (fisherParam (cliqueDensity 2 W)) = cliqueDensity 2 W :=
      paramEdge_fisherParam (by linarith)
    have hy8 : fisherParam (cliqueDensity 2 W) ≤ 1 / 8 :=
      param_le_eighth hy0 hy3 (by rw [hpy]; linarith)
    have hcmp := low_comparison hy0 hy8
    rw [hpy] at hcmp hG
    have hg0 : 0 ≤ paramProfile (fisherParam (cliqueDensity 2 W)) :=
      paramProfile_nonneg hy0
    have hsq := sq_pawG_le_bigT W
    have hpg : 0 ≤ cliqueDensity 2 W * paramProfile (fisherParam (cliqueDensity 2 W)) :=
      mul_nonneg (by linarith) hg0
    nlinarith [hsq, hG, hcmp, hpg, hg0, hgt, pow_le_pow_left₀ hpg hG 2]

/-- **Atlas 148, the analytic theorem.**  Every graphon of edge density
`p ∈ [1/2, 1]` satisfies `t(F₁₄₈,W) ≥ p(2p-1)²(3p²-3p+1)`.  The two intervals
meet at `p = 3/5`: below it the bound needs Fisher's sharp triangle profile,
above it nothing but Cauchy--Schwarz. -/
theorem homDensity_graph148_bound (W : Graphon Ω μ)
    (hp : 1 / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W * (2 * cliqueDensity 2 W - 1) ^ 2 *
        (3 * cliqueDensity 2 W ^ 2 - 3 * cliqueDensity 2 W + 1)
      ≤ homDensity graph148 W := by
  rcases le_or_gt (cliqueDensity 2 W) (3 / 5) with h | h
  · exact homDensity_graph148_low W hp h
  · exact homDensity_graph148_high W h.le

end Taeyoung.Methods.Atlas148
