import Taeyoung.Methods.Atlas148.Projection

/-!
# Atlas 148: the high-density interval

Integrating the fibrewise bound of `Projection.lean` over the spine variable
`x` gives, for every real `λ`,

```
T := ∫∫ (T_W F_x)(z)² ≥ G² + 2λΔ - λ²V,      V = ∫ v(x) ≤ pq,
```

using `∫g = G`, `∫(h - dg) = Δ`, and Jensen `∫g² ≥ (∫g)²`.

Choosing `λ = -cq` and inserting the linear estimate `p²G - qΔ ≥ pcf` of
`Linear.lean` turns the target into a perfect square:

```
T - pc²f ≥ (G - cp²)² ≥ 0,
```

because `f - q³ = p³`.  This replaces the note's final Cauchy--Schwarz in the
weighted two-dimensional space spanned by `(G₀, Δ₀) = (p²c, -pcq²)`; the
optimal `λ` is exactly the ratio that Cauchy--Schwarz would have produced, but
here nothing is divided by `V` and the vector never appears.

The result is `Atlas148.high_bound`, the note's high interval in full.  What it
bounds is the kernel form `T`; the peeling identity `t(F₁₄₈,W) = T` is proved
separately.
-/

open MeasureTheory

namespace Taeyoung.Methods.Atlas148

open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The kernel form of the density -/

/-- `‖T_W F_x‖²`. -/
noncomputable def fibNormSq (W : Graphon Ω μ) (x : Ω) : ℝ :=
  ∫ z, fibOp W x z ^ 2 ∂μ

/-- `T = ∫ ‖T_W F_x‖² dμ(x)`: the kernel form of the Atlas 148 density. -/
noncomputable def bigT (W : Graphon Ω μ) : ℝ := ∫ x, fibNormSq W x ∂μ

/-- `h(x) - d(x)g(x)`, the second projection coefficient. -/
noncomputable def devFib (W : Graphon Ω μ) (x : Ω) : ℝ :=
  hFib W x - degree W x * gFib W x

/-! ### Measurability and bounds of the fibre data -/

section Fibre

variable (W : Graphon Ω μ)

lemma gFib_nonneg (x : Ω) : 0 ≤ gFib W x :=
  integral_nonneg fun a ↦ mul_nonneg (degree_nonneg W a) (edgeK_nonneg W x a)

lemma gFib_le_one (x : Ω) : gFib W x ≤ 1 := by
  refine le_of_abs_le (abs_integral_le_of_bdd
    ((measurable_degree W).mul (measurable_row (measurable_edgeK W) x)) fun a ↦ ?_)
  rw [abs_of_nonneg (mul_nonneg (degree_nonneg W a) (edgeK_nonneg W x a))]
  exact mul_le_one₀ (degree_le_one W a) (edgeK_nonneg W x a) (edgeK_le_one W x a)

lemma measurable_gFib : Measurable (gFib W) := by
  have hg : StronglyMeasurable fun p : Ω × Ω ↦ degree W p.2 * edgeK W p.1 p.2 := by
    refine (?_ : Measurable _).stronglyMeasurable
    exact ((measurable_degree W).comp measurable_snd).mul (measurable_edgeK W)
  exact (hg.integral_prod_right' (ν := μ)).measurable

lemma hFib_nonneg (x : Ω) : 0 ≤ hFib W x :=
  integral_nonneg fun a ↦ mul_nonneg (edgeK_nonneg W x a) (pageOp_nonneg W le_rfl _ _)

lemma hFib_le_one (x : Ω) : hFib W x ≤ 1 := by
  refine le_of_abs_le (abs_integral_le_of_bdd
    ((measurable_row (measurable_edgeK W) x).mul
      (measurable_row (measurable_pageOp W le_rfl) x)) fun a ↦ ?_)
  rw [abs_of_nonneg (mul_nonneg (edgeK_nonneg W x a) (pageOp_nonneg W le_rfl _ _))]
  exact mul_le_one₀ (edgeK_le_one W x a) (pageOp_nonneg W le_rfl _ _)
    (pageOp_le_one W le_rfl _ _)

lemma measurable_hFib : Measurable (hFib W) := by
  have hg : StronglyMeasurable fun p : Ω × Ω ↦ edgeK W p.1 p.2 * pageOp W 0 p.1 p.2 := by
    refine (?_ : Measurable _).stronglyMeasurable
    exact (measurable_edgeK W).mul (measurable_pageOp W le_rfl)
  exact (hg.integral_prod_right' (ν := μ)).measurable

lemma measurable_rowSq : Measurable fun x ↦ ∫ z, W x z ^ 2 ∂μ := by
  have hg : StronglyMeasurable fun p : Ω × Ω ↦ W p.1 p.2 ^ 2 := by
    refine (?_ : Measurable _).stronglyMeasurable
    exact W.measurable.pow_const 2
  exact (hg.integral_prod_right' (ν := μ)).measurable

lemma measurable_vFib : Measurable (vFib W) :=
  (measurable_rowSq W).sub ((measurable_degree W).pow_const 2)

lemma vFib_nonneg (x : Ω) : 0 ≤ vFib W x := by
  rw [← integral_row_centered_sq W x]
  exact integral_nonneg fun z ↦ sq_nonneg _

lemma vFib_le_one (x : Ω) : vFib W x ≤ 1 := by
  have hb : (∫ z, W x z ^ 2 ∂μ) ≤ 1 := by
    refine le_of_abs_le (abs_integral_le_of_bdd
      ((measurable_row W.measurable x).pow_const 2) fun z ↦ ?_)
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (W.nonneg x z) (W.le_one x z)
  have := sq_nonneg (degree W x)
  rw [vFib]; linarith

lemma measurable_fibNormSq : Measurable (fibNormSq W) := by
  have hg : StronglyMeasurable fun p : Ω × Ω ↦ fibOp W p.1 p.2 ^ 2 := by
    refine (?_ : Measurable _).stronglyMeasurable
    exact (measurable_fibOp W).pow_const 2
  exact (hg.integral_prod_right' (ν := μ)).measurable

lemma fibNormSq_nonneg (x : Ω) : 0 ≤ fibNormSq W x :=
  integral_nonneg fun z ↦ sq_nonneg _

lemma fibNormSq_le_one (x : Ω) : fibNormSq W x ≤ 1 := by
  refine le_of_abs_le (abs_integral_le_of_bdd
    ((measurable_row (measurable_fibOp W) x).pow_const 2) fun z ↦ ?_)
  rw [abs_of_nonneg (sq_nonneg _)]
  exact pow_le_one₀ (fibOp_nonneg W x z) (fibOp_le_one W x z)

/-! ### Integrability -/

lemma integrable_gFib : Integrable (gFib W) μ :=
  integrable_of_bdd (measurable_gFib W) (C := 1) fun x ↦ by
    rw [abs_of_nonneg (gFib_nonneg W x)]; exact gFib_le_one W x

lemma integrable_gFib_sq : Integrable (fun x ↦ gFib W x ^ 2) μ :=
  integrable_of_bdd ((measurable_gFib W).pow_const 2) (C := 1) fun x ↦ by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (gFib_nonneg W x) (gFib_le_one W x)

lemma integrable_hFib : Integrable (hFib W) μ :=
  integrable_of_bdd (measurable_hFib W) (C := 1) fun x ↦ by
    rw [abs_of_nonneg (hFib_nonneg W x)]; exact hFib_le_one W x

lemma integrable_degMulG : Integrable (fun x ↦ degree W x * gFib W x) μ :=
  integrable_of_bdd ((measurable_degree W).mul (measurable_gFib W)) (C := 1) fun x ↦ by
    rw [abs_of_nonneg (mul_nonneg (degree_nonneg W x) (gFib_nonneg W x))]
    exact mul_le_one₀ (degree_le_one W x) (gFib_nonneg W x) (gFib_le_one W x)

lemma integrable_devFib : Integrable (devFib W) μ :=
  ((integrable_hFib W).sub (integrable_degMulG W)).congr (ae_of_all _ fun x ↦ rfl)

lemma integrable_vFib : Integrable (vFib W) μ :=
  integrable_of_bdd (measurable_vFib W) (C := 1) fun x ↦ by
    rw [abs_of_nonneg (vFib_nonneg W x)]; exact vFib_le_one W x

lemma integrable_fibNormSq : Integrable (fibNormSq W) μ :=
  integrable_of_bdd (measurable_fibNormSq W) (C := 1) fun x ↦ by
    rw [abs_of_nonneg (fibNormSq_nonneg W x)]; exact fibNormSq_le_one W x

end Fibre

/-! ### The three global identities -/

/-- `∫ g = G`. -/
theorem integral_gFib (W : Graphon Ω μ) : (∫ x, gFib W x ∂μ) = pawG W := by
  have hi : Integrable
      (Function.uncurry fun x a ↦ degree W a * edgeK W x a) (μ.prod μ) := by
    refine integrable_prod_of_bdd
      (((measurable_degree W).comp measurable_snd).mul (measurable_edgeK W))
      (C := 1) fun q ↦ ?_
    show |degree W q.2 * edgeK W q.1 q.2| ≤ 1
    rw [abs_of_nonneg (mul_nonneg (degree_nonneg W _) (edgeK_nonneg W _ _))]
    exact mul_le_one₀ (degree_le_one W _) (edgeK_nonneg W _ _) (edgeK_le_one W _ _)
  simp only [gFib]
  rw [integral_integral hi, pawG]
  refine integral_congr_ae (ae_of_all _ fun q ↦ ?_)
  show degree W q.2 * edgeK W q.1 q.2
      = W q.1 q.2 * pageOp W 0 q.1 q.2 * degree W q.2
  rw [edgeK]; ring

/-- `∫ h = D`. -/
theorem integral_hFib (W : Graphon Ω μ) : (∫ x, hFib W x ∂μ) = bigD W := by
  have hi : Integrable
      (Function.uncurry fun x a ↦ edgeK W x a * pageOp W 0 x a) (μ.prod μ) := by
    refine integrable_prod_of_bdd
      ((measurable_edgeK W).mul (measurable_pageOp W le_rfl)) (C := 1) fun q ↦ ?_
    show |edgeK W q.1 q.2 * pageOp W 0 q.1 q.2| ≤ 1
    rw [abs_of_nonneg (mul_nonneg (edgeK_nonneg W _ _) (pageOp_nonneg W le_rfl _ _))]
    exact mul_le_one₀ (edgeK_le_one W _ _) (pageOp_nonneg W le_rfl _ _)
      (pageOp_le_one W le_rfl _ _)
  simp only [hFib]
  rw [integral_integral hi, bigD]
  refine integral_congr_ae (ae_of_all _ fun q ↦ ?_)
  show edgeK W q.1 q.2 * pageOp W 0 q.1 q.2 = W q.1 q.2 * pageOp W 0 q.1 q.2 ^ 2
  rw [edgeK]; ring

/-- `∫ d·g = L`. -/
theorem integral_degMulG (W : Graphon Ω μ) :
    (∫ x, degree W x * gFib W x ∂μ) = bigL W := by
  have hi : Integrable
      (Function.uncurry fun x a ↦ degree W x * (degree W a * edgeK W x a))
      (μ.prod μ) := by
    refine integrable_prod_of_bdd (((measurable_degree W).comp measurable_fst).mul
      (((measurable_degree W).comp measurable_snd).mul (measurable_edgeK W)))
      (C := 1) fun q ↦ ?_
    have hin : 0 ≤ degree W q.2 * edgeK W q.1 q.2 :=
      mul_nonneg (degree_nonneg W _) (edgeK_nonneg W _ _)
    show |degree W q.1 * (degree W q.2 * edgeK W q.1 q.2)| ≤ 1
    rw [abs_of_nonneg (mul_nonneg (degree_nonneg W _) hin)]
    exact mul_le_one₀ (degree_le_one W _) hin
      (mul_le_one₀ (degree_le_one W _) (edgeK_nonneg W _ _) (edgeK_le_one W _ _))
  have hstep : (∫ x, degree W x * gFib W x ∂μ)
      = ∫ x, ∫ a, degree W x * (degree W a * edgeK W x a) ∂μ ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    show degree W x * gFib W x = ∫ a, degree W x * (degree W a * edgeK W x a) ∂μ
    rw [gFib, ← integral_const_mul]
  rw [hstep, integral_integral hi, bigL]
  refine integral_congr_ae (ae_of_all _ fun q ↦ ?_)
  show degree W q.1 * (degree W q.2 * edgeK W q.1 q.2)
      = W q.1 q.2 * pageOp W 0 q.1 q.2 * (degree W q.1 * degree W q.2)
  rw [edgeK]; ring

/-- `∫ (h - d·g) = Δ`. -/
theorem integral_devFib (W : Graphon Ω μ) :
    (∫ x, devFib W x ∂μ) = bigDelta W := by
  simp only [devFib]
  rw [integral_sub (integrable_hFib W) (integrable_degMulG W), integral_hFib,
    integral_degMulG, bigDelta]

/-- `V = ∫ v ≤ pq`. -/
theorem integral_vFib_le (W : Graphon Ω μ) :
    (∫ x, vFib W x ∂μ) ≤ cliqueDensity 2 W * (1 - cliqueDensity 2 W) := by
  have hW2i : Integrable (fun q : Ω × Ω ↦ W q.1 q.2 ^ 2) (μ.prod μ) :=
    integrable_prod_of_bdd (W.measurable.pow_const 2) (C := 1) fun q ↦ by
      show |W q.1 q.2 ^ 2| ≤ 1
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_one₀ (W.nonneg _ _) (W.le_one _ _)
  have hWi : Integrable (fun q : Ω × Ω ↦ W q.1 q.2) (μ.prod μ) :=
    integrable_prod_of_bdd W.measurable (C := 1) fun q ↦ by
      show |W q.1 q.2| ≤ 1
      rw [abs_of_nonneg (W.nonneg _ _)]; exact W.le_one _ _
  -- `∫∫ W² ≤ ∫∫ W = p`
  have hsq : (∫ x, ∫ z, W x z ^ 2 ∂μ ∂μ) ≤ cliqueDensity 2 W := by
    rw [integral_integral hW2i, ← integral_prod_edge W]
    exact integral_mono hW2i hWi fun q ↦ by
      nlinarith [W.nonneg q.1 q.2, W.le_one q.1 q.2]
  -- `∫ d² ≥ p²`
  have hd : cliqueDensity 2 W ^ 2 ≤ ∫ x, degree W x ^ 2 ∂μ := by
    rw [← integral_degree W]
    exact sq_integral_le (degree W) (integrable_degree W)
      (integrable_degree_pow W 2)
  have hrs : Integrable (fun x ↦ ∫ z, W x z ^ 2 ∂μ) μ :=
    integrable_of_bdd (measurable_rowSq W) (C := 1) fun x ↦ by
      have h0 : 0 ≤ ∫ z, W x z ^ 2 ∂μ := integral_nonneg fun z ↦ sq_nonneg _
      rw [abs_of_nonneg h0]
      refine le_of_abs_le (abs_integral_le_of_bdd
        ((measurable_row W.measurable x).pow_const 2) fun z ↦ ?_)
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_one₀ (W.nonneg x z) (W.le_one x z)
  have hsplit : (∫ x, vFib W x ∂μ)
      = (∫ x, ∫ z, W x z ^ 2 ∂μ ∂μ) - ∫ x, degree W x ^ 2 ∂μ := by
    simp only [vFib]
    exact integral_sub hrs (integrable_degree_pow W 2)
  rw [hsplit]
  nlinarith [hsq, hd]

/-! ### The high interval -/

set_option maxHeartbeats 1000000 in
/-- **The high-density bound.**  `T ≥ p(2p-1)²(3p²-3p+1)` for `p ∈ [3/5,1]`. -/
theorem high_bound (W : Graphon Ω μ) (hp0 : 3 / 5 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W * (2 * cliqueDensity 2 W - 1) ^ 2 *
        (3 * cliqueDensity 2 W ^ 2 - 3 * cliqueDensity 2 W + 1)
      ≤ bigT W := by
  set p := cliqueDensity 2 W with hpdef
  have hp1 : p ≤ 1 := cliqueDensity_le_one 2 W
  have hc : (0:ℝ) ≤ 2 * p - 1 := by linarith
  have hq : (0:ℝ) ≤ 1 - p := by linarith
  set lam := -((2 * p - 1) * (1 - p)) with hlam
  -- integrate the fibrewise bound
  have hcomb : Integrable (fun x ↦ gFib W x ^ 2 +
      (2 * lam * devFib W x - lam ^ 2 * vFib W x)) μ :=
    (((integrable_gFib_sq W).add
      ((((integrable_devFib W).const_mul (2 * lam)).sub
        ((integrable_vFib W).const_mul (lam ^ 2))).congr
          (ae_of_all _ fun x ↦ rfl))).congr (ae_of_all _ fun x ↦ rfl))
  have hmono : (∫ x, (gFib W x ^ 2 +
      (2 * lam * devFib W x - lam ^ 2 * vFib W x)) ∂μ) ≤ bigT W := by
    refine integral_mono hcomb (integrable_fibNormSq W) fun x ↦ ?_
    have := fibOp_sq_lower W x lam
    rw [fibNormSq]
    simp only [devFib]
    linarith
  -- expand the left-hand integral
  have hexp : (∫ x, (gFib W x ^ 2 +
      (2 * lam * devFib W x - lam ^ 2 * vFib W x)) ∂μ)
      = (∫ x, gFib W x ^ 2 ∂μ) + 2 * lam * bigDelta W
        - lam ^ 2 * ∫ x, vFib W x ∂μ := by
    have hA : Integrable (fun x ↦ 2 * lam * devFib W x) μ :=
      (integrable_devFib W).const_mul _
    have hB : Integrable (fun x ↦ lam ^ 2 * vFib W x) μ :=
      (integrable_vFib W).const_mul _
    have hAB : Integrable (fun x ↦ 2 * lam * devFib W x - lam ^ 2 * vFib W x) μ :=
      (hA.sub hB).congr (ae_of_all _ fun x ↦ rfl)
    rw [integral_add (integrable_gFib_sq W) hAB, integral_sub hA hB,
      integral_const_mul, integral_const_mul, integral_devFib]
    ring
  rw [hexp] at hmono
  -- Jensen on `g`, and the bound on `V`
  have hjen : pawG W ^ 2 ≤ ∫ x, gFib W x ^ 2 ∂μ := by
    rw [← integral_gFib W]
    exact sq_integral_le (gFib W) (integrable_gFib W) (integrable_gFib_sq W)
  have hV := integral_vFib_le W
  have hlam2 : (0:ℝ) ≤ lam ^ 2 := sq_nonneg _
  have hstep : pawG W ^ 2 + 2 * lam * bigDelta W - lam ^ 2 * (p * (1 - p)) ≤ bigT W := by
    nlinarith [hmono, hjen, mul_le_mul_of_nonneg_left hV hlam2]
  -- the linear estimate, and the perfect square
  have hlin := linear_estimate W hp0
  rw [← hpdef] at hlin
  nlinarith [hstep, hlin, sq_nonneg (pawG W - (2 * p - 1) * p ^ 2), hc, hq]

end Taeyoung.Methods.Atlas148
