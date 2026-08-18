import Taeyoung.Methods.Link.WeightedGoodmanRpow
import Taeyoung.Methods.PureChordal.WeightedCauchySchwarz

/-!
# The page operator of a triangle book

`notes/page_rooted_triangle_book_leaves.tex` factors the density of a
page-rooted leaf book through

```
H_s(x,y) = ∫ W(x,z)W(y,z)d(z)ˢ dμ(z),
```

one factor per page, the exponent being that page's number of private leaves.
Two facts about `H` carry the whole argument, and both are proved here.

* `integral_edge_pageOp` — pairing `H_s` against the edge `xy` and integrating
  collapses the two spine variables:

  ```
  ∫∫ W(x,y)·H_s(x,y) dμdμ = ∫ d(z)ˢ·τ(z) dμ(z),
  ```

  which is exactly the left-hand side of `weighted_rootedTriangle_rpow`.
* `sq_pageOp_le` — the compression `H_{s/2}² ≤ H₀·H_s`.  The note derives it
  from generalized Hölder at `m` factors; one Cauchy–Schwarz suffices, and the
  project already has it in the weighted form `(∫Aη)² ≤ (∫A)(∫Aη²)`, applied
  with `A = W(x,·)W(y,·)` and `η = d^{s/2}`.

No Hölder is needed at any number of pages.  The two-page rows (Atlas 41 at
`α = 1/2`, Atlas 114 at `α = 1`) are one application of `sq_pageOp_le'`, and
the three-page row (Atlas 138, `k = (1,0,0)`, `α = 1/3`) is two: `cube_pageOp_le`
chains `H_{1/3}² ≤ H₀H_{2/3}` with `H_{2/3}² ≤ H_{1/3}H₁`.
-/

open MeasureTheory

namespace Taeyoung.Methods.Link

open Taeyoung Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The operator -/

/-- `H_s(x,y) = ∫ W(x,z)W(y,z)d(z)ˢ dμ(z)`: the density of one page carrying
`s` private leaves, with its spine endpoints held fixed. -/
noncomputable def pageOp (W : Graphon Ω μ) (s : ℝ) (x y : Ω) : ℝ :=
  ∫ z, W x z * W y z * degree W z ^ s ∂μ

section Basic

variable (W : Graphon Ω μ) {s : ℝ}

lemma measurable_pageOp_integrand (hs : 0 ≤ s) (x y : Ω) :
    Measurable fun z ↦ W x z * W y z * degree W z ^ s :=
  ((measurable_row W.measurable x).mul (measurable_row W.measurable y)).mul
    (measurable_degree_rpow W hs)

lemma pageOp_integrand_nonneg (_hs : 0 ≤ s) (x y z : Ω) :
    0 ≤ W x z * W y z * degree W z ^ s :=
  mul_nonneg (mul_nonneg (W.nonneg x z) (W.nonneg y z)) (degree_rpow_nonneg W s z)

lemma pageOp_integrand_le_one (hs : 0 ≤ s) (x y z : Ω) :
    W x z * W y z * degree W z ^ s ≤ 1 :=
  mul_le_one₀ (mul_le_one₀ (W.le_one x z) (W.nonneg y z) (W.le_one y z))
    (degree_rpow_nonneg W s z) (degree_rpow_le_one W hs z)

lemma integrable_pageOp_integrand (hs : 0 ≤ s) (x y : Ω) :
    Integrable (fun z ↦ W x z * W y z * degree W z ^ s) μ :=
  integrable_of_bdd (measurable_pageOp_integrand W hs x y) (C := 1) fun z ↦ by
    rw [abs_of_nonneg (pageOp_integrand_nonneg W hs x y z)]
    exact pageOp_integrand_le_one W hs x y z

lemma pageOp_nonneg (hs : 0 ≤ s) (x y : Ω) : 0 ≤ pageOp W s x y :=
  integral_nonneg fun z ↦ pageOp_integrand_nonneg W hs x y z

lemma pageOp_le_one (hs : 0 ≤ s) (x y : Ω) : pageOp W s x y ≤ 1 := by
  calc pageOp W s x y ≤ ∫ _z : Ω, (1 : ℝ) ∂μ :=
        integral_mono (integrable_pageOp_integrand W hs x y) (integrable_const _)
          fun z ↦ pageOp_integrand_le_one W hs x y z
    _ = 1 := by simp

end Basic

/-- `H_s` is jointly measurable in its two spine arguments. -/
lemma measurable_pageOp (W : Graphon Ω μ) {s : ℝ} (hs : 0 ≤ s) :
    Measurable fun q : Ω × Ω ↦ pageOp W s q.1 q.2 := by
  have hg : StronglyMeasurable fun p : (Ω × Ω) × Ω ↦
      W p.1.1 p.2 * W p.1.2 p.2 * degree W p.2 ^ s := by
    refine (?_ : Measurable _).stronglyMeasurable
    exact ((W.measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (W.measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).mul
      ((measurable_degree_rpow W hs).comp measurable_snd)
  exact (hg.integral_prod_right' (ν := μ)).measurable

/-- The edge density, as an integral over the product measure. -/
lemma integral_prod_edge (W : Graphon Ω μ) :
    (∫ q : Ω × Ω, W q.1 q.2 ∂(μ.prod μ)) = cliqueDensity 2 W := by
  have hc : Integrable (Function.uncurry fun y z ↦ W y z) (μ.prod μ) :=
    integrable_prod_of_bdd W.measurable (C := 1) fun q ↦ by
      show |W q.1 q.2| ≤ 1
      rw [abs_of_nonneg (W.nonneg q.1 q.2)]; exact W.le_one q.1 q.2
  rw [← integral_integral hc, ← integral_degree]
  rfl

/-- **The codegree Goodman bound.**  `c(x,y) = H₀(x,y) ≥ d(x) + d(y) - 1`, from
`AB ≥ A + B - 1` on `[0,1]²` integrated in `z`.  This is the two-root family's
counterpart of `rootedTriangle_ge`, and with `c ≥ 0` it gives
`c ≥ max{d(x)+d(y)-1, 0}`. -/
theorem le_pageOp_zero (W : Graphon Ω μ) (x y : Ω) :
    degree W x + degree W y - 1 ≤ pageOp W 0 x y := by
  have hrowx : Measurable fun z ↦ W x z := measurable_row W.measurable x
  have hrowy : Measurable fun z ↦ W y z := measurable_row W.measurable y
  have hintx : Integrable (fun z ↦ W x z) μ :=
    integrable_of_bdd hrowx (C := 1) fun z ↦ by
      rw [abs_of_nonneg (W.nonneg x z)]; exact W.le_one x z
  have hinty : Integrable (fun z ↦ W y z) μ :=
    integrable_of_bdd hrowy (C := 1) fun z ↦ by
      rw [abs_of_nonneg (W.nonneg y z)]; exact W.le_one y z
  have hlin : Integrable (fun z ↦ W x z + W y z - 1) μ :=
    (hintx.add hinty).sub (integrable_const _)
  have hprod : Integrable (fun z ↦ W x z * W y z) μ := by
    refine (integrable_pageOp_integrand W (s := 0) le_rfl x y).congr
      (ae_of_all _ fun z ↦ ?_)
    simp only []
    rw [Real.rpow_zero, mul_one]
  have hmono : (∫ z, (W x z + W y z - 1) ∂μ) ≤ ∫ z, W x z * W y z ∂μ := by
    refine integral_mono hlin hprod fun z ↦ ?_
    nlinarith [mul_nonneg (sub_nonneg.mpr (W.le_one x z))
      (sub_nonneg.mpr (W.le_one y z))]
  have hval : (∫ z, (W x z + W y z - 1) ∂μ) = degree W x + degree W y - 1 := by
    have e1 := integral_sub (hintx.add hinty) (integrable_const (μ := μ) (1 : ℝ))
    have e2 := integral_add hintx hinty
    simp only [Pi.add_apply, Pi.sub_apply] at e1 e2
    rw [e1, e2]
    simp [degree]
  have hzero : pageOp W 0 x y = ∫ z, W x z * W y z ∂μ := by
    simp only [pageOp]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    simp only []
    rw [Real.rpow_zero, mul_one]
  rw [hzero, ← hval]
  exact hmono

/-! ### The compression -/

/-- **The page compression at two pages.**  `H_{s/2}² ≤ H₀·H_s`, by weighted
Cauchy–Schwarz with weight `W(x,·)W(y,·)` and `η = d^{s/2}`. -/
theorem sq_pageOp_le (W : Graphon Ω μ) {s : ℝ} (hs : 0 ≤ s) (x y : Ω) :
    pageOp W (s / 2) x y ^ 2 ≤ pageOp W 0 x y * pageOp W s x y := by
  have hhalf : (0 : ℝ) ≤ s / 2 := by linarith
  have hsq : ∀ z : Ω, (degree W z ^ (s / 2)) ^ 2 = degree W z ^ s := by
    intro z
    rw [← Real.rpow_natCast (degree W z ^ (s / 2)) 2,
      ← Real.rpow_mul (degree_nonneg W z)]
    norm_num
  have hA : Integrable (fun z ↦ W x z * W y z) μ := by
    refine (integrable_pageOp_integrand W (s := 0) le_rfl x y).congr
      (ae_of_all _ fun z ↦ ?_)
    simp only []
    rw [Real.rpow_zero, mul_one]
  have hAη : Integrable (fun z ↦ (W x z * W y z) * degree W z ^ (s / 2)) μ :=
    integrable_pageOp_integrand W hhalf x y
  have hAη2 : Integrable (fun z ↦ (W x z * W y z) * (degree W z ^ (s / 2)) ^ 2) μ := by
    refine (integrable_pageOp_integrand W hs x y).congr (ae_of_all _ fun z ↦ ?_)
    simp only []
    rw [← hsq z]
  have hcs := integral_mul_sq_le_integral_mul_integral_mul_sq
    (A := fun z ↦ W x z * W y z) (η := fun z ↦ degree W z ^ (s / 2))
    hA hAη hAη2 (fun z ↦ mul_nonneg (W.nonneg x z) (W.nonneg y z))
  have hA0 : (∫ z, W x z * W y z ∂μ) = pageOp W 0 x y := by
    simp only [pageOp]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    simp only []
    rw [Real.rpow_zero, mul_one]
  have hAs : (∫ z, (W x z * W y z) * (degree W z ^ (s / 2)) ^ 2 ∂μ) =
      pageOp W s x y := by
    simp only [pageOp]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    simp only []
    rw [hsq z]
  rw [hA0, hAs] at hcs
  exact hcs

lemma pageOp_zero_eq (W : Graphon Ω μ) (x y : Ω) :
    pageOp W 0 x y = ∫ z, W x z * W y z ∂μ := by
  simp only [pageOp]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  simp only []
  rw [Real.rpow_zero, mul_one]

/-- **The page compression between two exponents.**  `H_{(a+b)/2}² ≤ H_a·H_b`,
by weighted Cauchy–Schwarz with weight `W(x,·)W(y,·)d^a` and `η = d^{(b-a)/2}`.
Taking `a = 0` recovers `sq_pageOp_le`. -/
theorem sq_pageOp_le' (W : Graphon Ω μ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : 0 < b) (x y : Ω) :
    pageOp W ((a + b) / 2) x y ^ 2 ≤ pageOp W a x y * pageOp W b x y := by
  have hd : (0 : ℝ) ≤ (b - a) / 2 := by linarith
  have hmid : (0 : ℝ) ≤ (a + b) / 2 := by linarith
  have hkey : ∀ z : Ω,
      (W x z * W y z * degree W z ^ a) * degree W z ^ ((b - a) / 2) =
        W x z * W y z * degree W z ^ ((a + b) / 2) := by
    intro z
    have he : a + (b - a) / 2 = (a + b) / 2 := by ring
    rw [mul_assoc, ← Real.rpow_add' (degree_nonneg W z)
      (ne_of_gt (by linarith : (0 : ℝ) < a + (b - a) / 2)), he]
  have hkey2 : ∀ z : Ω,
      (W x z * W y z * degree W z ^ a) * (degree W z ^ ((b - a) / 2)) ^ 2 =
        W x z * W y z * degree W z ^ b := by
    intro z
    have hsq : (degree W z ^ ((b - a) / 2)) ^ 2 = degree W z ^ (b - a) := by
      rw [← Real.rpow_natCast (degree W z ^ ((b - a) / 2)) 2,
        ← Real.rpow_mul (degree_nonneg W z)]
      norm_num
    rw [hsq, mul_assoc, ← Real.rpow_add' (degree_nonneg W z)
      (ne_of_gt (by linarith : (0 : ℝ) < a + (b - a))), show a + (b - a) = b by ring]
  have hA : Integrable (fun z ↦ W x z * W y z * degree W z ^ a) μ :=
    integrable_pageOp_integrand W ha x y
  have hAη : Integrable (fun z ↦
      (W x z * W y z * degree W z ^ a) * degree W z ^ ((b - a) / 2)) μ := by
    refine (integrable_pageOp_integrand W hmid x y).congr (ae_of_all _ fun z ↦ ?_)
    simp only []
    rw [hkey z]
  have hAη2 : Integrable (fun z ↦
      (W x z * W y z * degree W z ^ a) * (degree W z ^ ((b - a) / 2)) ^ 2) μ := by
    refine (integrable_pageOp_integrand W hb.le x y).congr (ae_of_all _ fun z ↦ ?_)
    simp only []
    rw [hkey2 z]
  have hcs := integral_mul_sq_le_integral_mul_integral_mul_sq
    (A := fun z ↦ W x z * W y z * degree W z ^ a)
    (η := fun z ↦ degree W z ^ ((b - a) / 2)) hA hAη hAη2
    (fun z ↦ pageOp_integrand_nonneg W ha x y z)
  have e1 : (∫ z, (W x z * W y z * degree W z ^ a) *
      degree W z ^ ((b - a) / 2) ∂μ) = pageOp W ((a + b) / 2) x y := by
    simp only [pageOp]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    simp only []
    rw [hkey z]
  have e2 : (∫ z, (W x z * W y z * degree W z ^ a) *
      (degree W z ^ ((b - a) / 2)) ^ 2 ∂μ) = pageOp W b x y := by
    simp only [pageOp]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    simp only []
    rw [hkey2 z]
  rw [e1, e2] at hcs
  exact hcs

/-- **The three-page compression.**  `H_{1/3}³ ≤ H₀²·H₁`, from two applications
of `sq_pageOp_le'`: `H_{1/3}² ≤ H₀H_{2/3}` and `H_{2/3}² ≤ H_{1/3}H₁` give
`H_{1/3}⁴ ≤ H₀²H_{2/3}² ≤ H₀²H_{1/3}H₁`. -/
theorem cube_pageOp_le (W : Graphon Ω μ) (x y : Ω) :
    pageOp W (1 / 3) x y ^ 3 ≤ pageOp W 0 x y ^ 2 * pageOp W 1 x y := by
  have h1 : pageOp W (1 / 3) x y ^ 2 ≤ pageOp W 0 x y * pageOp W (2 / 3) x y := by
    have h := sq_pageOp_le' W (a := 0) (b := 2 / 3) le_rfl (by norm_num)
      (by norm_num) x y
    rwa [show ((0 : ℝ) + 2 / 3) / 2 = 1 / 3 by norm_num] at h
  have h2 : pageOp W (2 / 3) x y ^ 2 ≤
      pageOp W (1 / 3) x y * pageOp W 1 x y := by
    have h := sq_pageOp_le' W (a := 1 / 3) (b := 1) (by norm_num) (by norm_num)
      (by norm_num) x y
    rwa [show ((1 : ℝ) / 3 + 1) / 2 = 2 / 3 by norm_num] at h
  set A := pageOp W 0 x y with hA
  set B := pageOp W (1 / 3) x y with hB
  set C := pageOp W (2 / 3) x y with hC
  set D := pageOp W 1 x y with hD
  have hAn : 0 ≤ A := pageOp_nonneg W le_rfl x y
  have hBn : 0 ≤ B := pageOp_nonneg W (by norm_num) x y
  have hDn : 0 ≤ D := pageOp_nonneg W zero_le_one x y
  rcases eq_or_lt_of_le hBn with hB0 | hBpos
  · rw [← hB0, zero_pow (by norm_num : (3 : ℕ) ≠ 0)]
    exact mul_nonneg (sq_nonneg A) hDn
  · have h3 : B ^ 4 ≤ A ^ 2 * C ^ 2 := by
      have := pow_le_pow_left₀ (sq_nonneg B) h1 2
      nlinarith [this]
    have h4 : A ^ 2 * C ^ 2 ≤ A ^ 2 * (B * D) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg A)
    have h5 : B * B ^ 3 ≤ B * (A ^ 2 * D) := by nlinarith [h3, h4]
    exact le_of_mul_le_mul_left h5 hBpos

/-! ### Collapsing the spine -/

/-- **Pairing a page against its spine edge.**  Integrating `W(x,y)·H_s(x,y)`
over both spine variables leaves the degree-weighted rooted triangle — which is
the left-hand side of `weighted_rootedTriangle_rpow`. -/
theorem integral_edge_pageOp (W : Graphon Ω μ) {s : ℝ} (hs : 0 ≤ s) :
    (∫ q, W q.1 q.2 * pageOp W s q.1 q.2 ∂(μ.prod μ)) =
      ∫ z, degree W z ^ s * rootedTriangle W z ∂μ := by
  -- the triple integrand, as a function on `(Ω × Ω) × Ω`
  set g : (Ω × Ω) → Ω → ℝ :=
    fun q z ↦ W q.1 q.2 * (W q.1 z * W q.2 z * degree W z ^ s) with hg
  have hgm : Measurable (Function.uncurry g) := by
    refine ((W.measurable.comp measurable_fst).mul ?_)
    refine (((W.measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (W.measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).mul ?_)
    exact (measurable_degree_rpow W hs).comp measurable_snd
  have hgb : ∀ q z, |g q z| ≤ 1 := by
    intro q z
    have h0 : 0 ≤ g q z :=
      mul_nonneg (W.nonneg _ _) (pageOp_integrand_nonneg W hs q.1 q.2 z)
    rw [abs_of_nonneg h0]
    exact mul_le_one₀ (W.le_one _ _) (pageOp_integrand_nonneg W hs q.1 q.2 z)
      (pageOp_integrand_le_one W hs q.1 q.2 z)
  have hgi : Integrable (Function.uncurry g) ((μ.prod μ).prod μ) :=
    (integrable_const (μ := (μ.prod μ).prod μ) (1 : ℝ)).mono'
      hgm.aestronglyMeasurable
      (ae_of_all _ fun p ↦ by rw [Real.norm_eq_abs]; exact hgb p.1 p.2)
  -- pull the edge factor inside, then swap the two integrals
  have hstep : (∫ q, W q.1 q.2 * pageOp W s q.1 q.2 ∂(μ.prod μ)) =
      ∫ q, ∫ z, g q z ∂μ ∂(μ.prod μ) := by
    refine integral_congr_ae (ae_of_all _ fun q ↦ ?_)
    simp only [hg, pageOp]
    rw [← integral_const_mul]
  rw [hstep, integral_integral_swap hgi]
  -- the inner integral is `d(z)ˢ·τ(z)`
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  simp only []
  have hz : (∫ q, g q z ∂(μ.prod μ)) =
      degree W z ^ s * ∫ q, W z q.1 * W z q.2 * W q.1 q.2 ∂(μ.prod μ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun q ↦ ?_)
    simp only [hg]
    rw [W.symm q.1 z, W.symm q.2 z]
    ring
  rw [hz]
  congr 1
  have hτ : Integrable (Function.uncurry fun a b ↦ W z a * W z b * W a b)
      (μ.prod μ) := by
    refine integrable_prod_of_bdd ?_ (C := 1) ?_
    · exact (((W.measurable.comp (measurable_const.prodMk measurable_fst)).mul
        (W.measurable.comp (measurable_const.prodMk measurable_snd))).mul
        W.measurable)
    · intro q
      show |W z q.1 * W z q.2 * W q.1 q.2| ≤ 1
      have h0 : 0 ≤ W z q.1 * W z q.2 * W q.1 q.2 :=
        mul_nonneg (mul_nonneg (W.nonneg _ _) (W.nonneg _ _)) (W.nonneg _ _)
      rw [abs_of_nonneg h0]
      exact mul_le_one₀ (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _)
        (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _)
  rw [← integral_integral hτ]
  rfl

end Taeyoung.Methods.Link
