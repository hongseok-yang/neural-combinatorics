import Taeyoung.Methods.Link.PageOp
import Taeyoung.Methods.Link.WeightedGoodmanRpow

/-!
# The analytic core of the page-paw branch theorem

`notes/triangle_book_page_paw_branch.tex` bounds the two triangle books
`B_m^{new}` and `B_m^{page}` below by `p²(2p-1)^{m+1}`.  The catalogue needs
only `m = 2` — Atlas `139` and Atlas `137` — and at `m = 2` the proof needs no
genuine Hölder inequality: every step is the weighted Cauchy--Schwarz
`(∫Aη)² ≤ (∫A)(∫Aη²)` of `PureChordal.WeightedCauchySchwarz`, at four
different weights.

The note's page-orbit symmetrization is replaced here by one Cauchy--Schwarz on
the page variable.  Peeling gives the exact identity `t = ∫∫W·H₀·Λ_h`, where

```
Λ_h(x,y) = ∫ W(x,z)W(y,z)h(x,z) dμ(z)
```

is the *branch operator* — a page carrying the branch weight `h` rooted at the
spine endpoint `x` — and `h = H₁` for `B_2^{new}`, `h(x,z) = d(z)H₀(x,z)` for
`B_2^{page}`.  Cauchy--Schwarz on `z` with weight `W(x,·)W(y,·)` gives
`Λ_{√h}² ≤ H₀·Λ_h`, so `t ≥ ∫∫W·Λ_{√h}²`, which is what the symmetrization
step was there to produce.

The remaining three steps are:

* `sq_edge_le` — Cauchy--Schwarz on the spine edge, `(∫∫W·F)² ≤ p·∫∫W·F²`;
* `cube_edge_le` — edge Jensen at exponent `3/2`, `(∫∫W·F)³ ≤ p·(∫∫W·F√F)²`,
  itself two Cauchy--Schwarz applications at weights `W` and `W√F`;
* `rpow_mul_le_integral_third` — the scalar input `∫d^{1/3}τ ≥ p^{4/3}(2p-1)`,
  from `weighted_rootedTriangle_rpow` and `rpow_le_momentR`.

Chained, these give `t ≥ p^{-2}(∫d^{1/3}τ)³ ≥ p²(2p-1)³` for both graphs; the
only fractional exponent surviving to the end is the `p^{4/3}` of the scalar
core, cubed back to `p⁴` exactly as in `PageBook.Atlas138`.
-/

open MeasureTheory

namespace Taeyoung.Methods.PagePawBranch

open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The scalar core -/

/-- **The scalar core.**  `∫ d^{1/3} τ ≥ p^{4/3}(2p-1)` for `p ≥ 1/2`. -/
theorem rpow_mul_le_integral_third (W : Graphon Ω μ)
    (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ ((4 : ℝ) / 3) * (2 * cliqueDensity 2 W - 1)
      ≤ ∫ x, degree W x ^ ((1 : ℝ) / 3) * rootedTriangle W x ∂μ := by
  set p := cliqueDensity 2 W with hpdef
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp
  have h2p : (0 : ℝ) ≤ 2 * p - 1 := by linarith
  -- the weighted rooted-triangle inequality at `s = 1/3`
  have hwt := weighted_rootedTriangle_rpow W (s := (1 : ℝ) / 3) (by norm_num)
  -- Jensen at the same exponent
  have hjen : p ^ ((1 : ℝ) / 3 + 2) ≤ momentR W ((1 : ℝ) / 3 + 2) :=
    rpow_le_momentR W (by norm_num)
  -- combine
  have hstep : (2 * p - 1) * p ^ ((1 : ℝ) / 3 + 2)
      ≤ p * ∫ x, degree W x ^ ((1 : ℝ) / 3) * rootedTriangle W x ∂μ :=
    le_trans (mul_le_mul_of_nonneg_left hjen h2p) hwt
  -- `p^{7/3} = p^{4/3}·p`
  have hsplit : p ^ ((1 : ℝ) / 3 + 2) = p ^ ((4 : ℝ) / 3) * p := by
    rw [show (1 : ℝ) / 3 + 2 = 4 / 3 + 1 by norm_num, Real.rpow_add hp0,
      Real.rpow_one]
  rw [hsplit] at hstep
  -- cancel the common factor `p`
  have hstep' : p ^ ((4 : ℝ) / 3) * (2 * p - 1) * p
      ≤ (∫ x, degree W x ^ ((1 : ℝ) / 3) * rootedTriangle W x ∂μ) * p := by
    calc p ^ ((4 : ℝ) / 3) * (2 * p - 1) * p
        = (2 * p - 1) * (p ^ ((4 : ℝ) / 3) * p) := by ring
      _ ≤ p * ∫ x, degree W x ^ ((1 : ℝ) / 3) * rootedTriangle W x ∂μ := hstep
      _ = (∫ x, degree W x ^ ((1 : ℝ) / 3) * rootedTriangle W x ∂μ) * p := by ring
  exact le_of_mul_le_mul_right hstep' hp0

/-! ### The branch operator -/

section Branch

variable {h : Ω → Ω → ℝ}

/-- `Λ_h(x,y) = ∫ W(x,z)W(y,z)h(x,z) dμ(z)`: one page of the book, carrying an
arbitrary branch weight `h` rooted at the spine endpoint `x`.  Taking
`h = d(·)ˢ` recovers `pageOp W s`; the branch weights this file needs depend on
both arguments and so fall outside `pageOp`. -/
noncomputable def branchOp (W : Graphon Ω μ) (h : Ω → Ω → ℝ) (x y : Ω) : ℝ :=
  ∫ z, W x z * W y z * h x z ∂μ

lemma branchIntegrand_nonneg (W : Graphon Ω μ) (h0 : ∀ x y, 0 ≤ h x y)
    (x y z : Ω) : 0 ≤ W x z * W y z * h x z :=
  mul_nonneg (mul_nonneg (W.nonneg _ _) (W.nonneg _ _)) (h0 _ _)

lemma branchIntegrand_le_one (W : Graphon Ω μ) (h0 : ∀ x y, 0 ≤ h x y)
    (h1 : ∀ x y, h x y ≤ 1) (x y z : Ω) : W x z * W y z * h x z ≤ 1 :=
  mul_le_one₀ (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
    (h0 _ _) (h1 _ _)

lemma integrable_branchIntegrand (W : Graphon Ω μ)
    (hm : Measurable (Function.uncurry h)) (h0 : ∀ x y, 0 ≤ h x y)
    (h1 : ∀ x y, h x y ≤ 1) (x y : Ω) :
    Integrable (fun z ↦ W x z * W y z * h x z) μ :=
  integrable_of_bdd (((measurable_row W.measurable x).mul
    (measurable_row W.measurable y)).mul (measurable_row hm x)) (C := 1)
    fun z ↦ by
      rw [abs_of_nonneg (branchIntegrand_nonneg W h0 x y z)]
      exact branchIntegrand_le_one W h0 h1 x y z

lemma branchOp_nonneg (W : Graphon Ω μ) (h0 : ∀ x y, 0 ≤ h x y) (x y : Ω) :
    0 ≤ branchOp W h x y :=
  integral_nonneg fun z ↦ branchIntegrand_nonneg W h0 x y z

lemma branchOp_le_one (W : Graphon Ω μ) (hm : Measurable (Function.uncurry h))
    (h0 : ∀ x y, 0 ≤ h x y) (h1 : ∀ x y, h x y ≤ 1) (x y : Ω) :
    branchOp W h x y ≤ 1 := by
  refine le_of_abs_le (abs_integral_le_of_bdd (((measurable_row W.measurable x).mul
    (measurable_row W.measurable y)).mul (measurable_row hm x)) fun z ↦ ?_)
  rw [abs_of_nonneg (branchIntegrand_nonneg W h0 x y z)]
  exact branchIntegrand_le_one W h0 h1 x y z

lemma measurable_branchOp (W : Graphon Ω μ)
    (hm : Measurable (Function.uncurry h)) :
    Measurable fun q : Ω × Ω ↦ branchOp W h q.1 q.2 := by
  have hg : StronglyMeasurable fun p : (Ω × Ω) × Ω ↦
      W p.1.1 p.2 * W p.1.2 p.2 * h p.1.1 p.2 := by
    refine (?_ : Measurable _).stronglyMeasurable
    exact ((W.measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (W.measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).mul
      (hm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  exact (hg.integral_prod_right' (ν := μ)).measurable

/-! ### The square roots that appear as branch weights -/

lemma measurable_sqrt_kernel (hm : Measurable (Function.uncurry h)) :
    Measurable (Function.uncurry fun a b ↦ Real.sqrt (h a b)) :=
  Real.continuous_sqrt.measurable.comp hm

lemma sqrt_kernel_nonneg (a b : Ω) : 0 ≤ Real.sqrt (h a b) := Real.sqrt_nonneg _

lemma sqrt_kernel_le_one (h1 : ∀ x y, h x y ≤ 1) (a b : Ω) :
    Real.sqrt (h a b) ≤ 1 := Real.sqrt_le_one.mpr (h1 a b)

/-- **The branch compression.**  Weighted Cauchy--Schwarz on the page variable,
with weight `W(x,·)W(y,·)` and `η = √(h(x,·))`: `Λ_{√h}² ≤ H₀·Λ_h`.  This is
what the note obtains from page-orbit symmetrization followed by
arithmetic--geometric mean. -/
theorem sq_branchOp_le (W : Graphon Ω μ) (hm : Measurable (Function.uncurry h))
    (h0 : ∀ x y, 0 ≤ h x y) (h1 : ∀ x y, h x y ≤ 1) (x y : Ω) :
    branchOp W (fun a b ↦ Real.sqrt (h a b)) x y ^ 2
      ≤ pageOp W 0 x y * branchOp W h x y := by
  have hsm := measurable_sqrt_kernel hm
  have hs0 : ∀ a b : Ω, 0 ≤ Real.sqrt (h a b) := fun a b ↦ Real.sqrt_nonneg _
  have hs1 : ∀ a b : Ω, Real.sqrt (h a b) ≤ 1 := fun a b ↦ sqrt_kernel_le_one h1 a b
  have hsq : ∀ z : Ω, Real.sqrt (h x z) ^ 2 = h x z := fun z ↦ Real.sq_sqrt (h0 x z)
  have hA : Integrable (fun z ↦ W x z * W y z) μ :=
    integrable_of_bdd ((measurable_row W.measurable x).mul
      (measurable_row W.measurable y)) (C := 1) fun z ↦ by
        have h0' : 0 ≤ W x z * W y z := mul_nonneg (W.nonneg _ _) (W.nonneg _ _)
        rw [abs_of_nonneg h0']
        exact mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _)
  have hAη : Integrable (fun z ↦ W x z * W y z * Real.sqrt (h x z)) μ :=
    integrable_branchIntegrand W hsm hs0 hs1 x y
  have hAη2 : Integrable (fun z ↦ W x z * W y z * Real.sqrt (h x z) ^ 2) μ := by
    refine (integrable_branchIntegrand W hm h0 h1 x y).congr (ae_of_all _ fun z ↦ ?_)
    show W x z * W y z * h x z = W x z * W y z * Real.sqrt (h x z) ^ 2
    rw [hsq z]
  have hcs := integral_mul_sq_le_integral_mul_integral_mul_sq
    (A := fun z ↦ W x z * W y z) (η := fun z ↦ Real.sqrt (h x z))
    hA hAη hAη2 fun z ↦ mul_nonneg (W.nonneg _ _) (W.nonneg _ _)
  have e0 : (∫ z, W x z * W y z ∂μ) = pageOp W 0 x y := (pageOp_zero_eq W x y).symm
  have e2 : (∫ z, W x z * W y z * Real.sqrt (h x z) ^ 2 ∂μ) = branchOp W h x y := by
    rw [branchOp]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    show W x z * W y z * Real.sqrt (h x z) ^ 2 = W x z * W y z * h x z
    rw [hsq z]
  rw [e0, e2] at hcs
  exact hcs

end Branch

/-! ### Cauchy--Schwarz on the spine edge -/

section Edge

variable {F : Ω → Ω → ℝ}

lemma integrable_edge (W : Graphon Ω μ) (hFm : Measurable (Function.uncurry F))
    (hF0 : ∀ x y, 0 ≤ F x y) (hF1 : ∀ x y, F x y ≤ 1) :
    Integrable (fun q : Ω × Ω ↦ W q.1 q.2 * F q.1 q.2) (μ.prod μ) :=
  integrable_prod_of_bdd (W.measurable.mul hFm) (C := 1) fun q ↦ by
    have h0 : 0 ≤ W q.1 q.2 * F q.1 q.2 := mul_nonneg (W.nonneg _ _) (hF0 _ _)
    show |W q.1 q.2 * F q.1 q.2| ≤ 1
    rw [abs_of_nonneg h0]
    exact mul_le_one₀ (W.le_one _ _) (hF0 _ _) (hF1 _ _)

lemma cliqueDensity_two_nonneg (W : Graphon Ω μ) : 0 ≤ cliqueDensity 2 W := by
  rw [← integral_prod_edge W]
  exact integral_nonneg fun q ↦ W.nonneg _ _

/-- **Edge Cauchy--Schwarz.**  `(∫∫W·F)² ≤ p·∫∫W·F²`. -/
theorem sq_edge_le (W : Graphon Ω μ) (hFm : Measurable (Function.uncurry F))
    (hF0 : ∀ x y, 0 ≤ F x y) (hF1 : ∀ x y, F x y ≤ 1) :
    (∫ q, W q.1 q.2 * F q.1 q.2 ∂(μ.prod μ)) ^ 2
      ≤ cliqueDensity 2 W * ∫ q, W q.1 q.2 * F q.1 q.2 ^ 2 ∂(μ.prod μ) := by
  have hWi : Integrable (fun q : Ω × Ω ↦ W q.1 q.2) (μ.prod μ) :=
    integrable_prod_of_bdd W.measurable (C := 1) fun q ↦ by
      show |W q.1 q.2| ≤ 1
      rw [abs_of_nonneg (W.nonneg q.1 q.2)]; exact W.le_one q.1 q.2
  have hsq : Integrable (fun q : Ω × Ω ↦ W q.1 q.2 * F q.1 q.2 ^ 2) (μ.prod μ) :=
    integrable_edge W (hFm.pow_const 2) (fun x y ↦ pow_nonneg (hF0 x y) 2)
      fun x y ↦ pow_le_one₀ (hF0 x y) (hF1 x y)
  have hcs := integral_mul_sq_le_integral_mul_integral_mul_sq
    (μ := μ.prod μ) (A := fun q : Ω × Ω ↦ W q.1 q.2)
    (η := fun q : Ω × Ω ↦ F q.1 q.2) hWi (integrable_edge W hFm hF0 hF1) hsq
    fun q ↦ W.nonneg _ _
  rwa [integral_prod_edge] at hcs

/-- **Edge Jensen at exponent `3/2`.**  `(∫∫W·F)³ ≤ p·(∫∫W·F√F)²`.  Two
weighted Cauchy--Schwarz applications: at weight `W` with `η = √F` this is
`(∫W√F)² ≤ p·∫W·F`, and at weight `W√F` with the same `η` it is
`(∫W·F)² ≤ (∫W√F)(∫W·F√F)`; eliminating `∫W√F` gives the claim. -/
theorem cube_edge_le (W : Graphon Ω μ) (hFm : Measurable (Function.uncurry F))
    (hF0 : ∀ x y, 0 ≤ F x y) (hF1 : ∀ x y, F x y ≤ 1) :
    (∫ q, W q.1 q.2 * F q.1 q.2 ∂(μ.prod μ)) ^ 3
      ≤ cliqueDensity 2 W *
          (∫ q, W q.1 q.2 * (F q.1 q.2 * Real.sqrt (F q.1 q.2)) ∂(μ.prod μ)) ^ 2 := by
  have hp0 : 0 ≤ cliqueDensity 2 W := cliqueDensity_two_nonneg W
  have hrm := measurable_sqrt_kernel hFm
  have hr0 : ∀ x y : Ω, 0 ≤ Real.sqrt (F x y) := fun x y ↦ Real.sqrt_nonneg _
  have hr1 : ∀ x y : Ω, Real.sqrt (F x y) ≤ 1 := fun x y ↦ sqrt_kernel_le_one hF1 x y
  have hsq : ∀ x y : Ω, Real.sqrt (F x y) ^ 2 = F x y :=
    fun x y ↦ Real.sq_sqrt (hF0 x y)
  -- integrability of the integrands in play
  have hiW : Integrable (fun q : Ω × Ω ↦ W q.1 q.2) (μ.prod μ) :=
    integrable_prod_of_bdd W.measurable (C := 1) fun q ↦ by
      show |W q.1 q.2| ≤ 1
      rw [abs_of_nonneg (W.nonneg q.1 q.2)]; exact W.le_one q.1 q.2
  have hiS : Integrable (fun q : Ω × Ω ↦ W q.1 q.2 * Real.sqrt (F q.1 q.2))
      (μ.prod μ) := integrable_edge W hrm hr0 hr1
  have hiA : Integrable (fun q : Ω × Ω ↦ W q.1 q.2 * F q.1 q.2) (μ.prod μ) :=
    integrable_edge W hFm hF0 hF1
  have hiT : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * (F q.1 q.2 * Real.sqrt (F q.1 q.2))) (μ.prod μ) :=
    integrable_edge W (F := fun x y ↦ F x y * Real.sqrt (F x y)) (hFm.mul hrm)
      (fun x y ↦ mul_nonneg (hF0 x y) (hr0 x y))
      fun x y ↦ mul_le_one₀ (hF1 x y) (hr0 x y) (hr1 x y)
  -- first Cauchy--Schwarz: weight `W`, `η = √F`
  have hSA : (∫ q, W q.1 q.2 * Real.sqrt (F q.1 q.2) ∂(μ.prod μ)) ^ 2
      ≤ cliqueDensity 2 W * ∫ q, W q.1 q.2 * F q.1 q.2 ∂(μ.prod μ) := by
    have hcs := integral_mul_sq_le_integral_mul_integral_mul_sq
      (μ := μ.prod μ) (A := fun q : Ω × Ω ↦ W q.1 q.2)
      (η := fun q : Ω × Ω ↦ Real.sqrt (F q.1 q.2)) hiW hiS
      (hiA.congr (ae_of_all _ fun q ↦ by
        show W q.1 q.2 * F q.1 q.2 = W q.1 q.2 * Real.sqrt (F q.1 q.2) ^ 2
        rw [hsq q.1 q.2])) fun q ↦ W.nonneg _ _
    rw [integral_prod_edge] at hcs
    have e : (∫ q, W q.1 q.2 * Real.sqrt (F q.1 q.2) ^ 2 ∂(μ.prod μ))
        = ∫ q, W q.1 q.2 * F q.1 q.2 ∂(μ.prod μ) :=
      integral_congr_ae (ae_of_all _ fun q ↦ by
        show W q.1 q.2 * Real.sqrt (F q.1 q.2) ^ 2 = W q.1 q.2 * F q.1 q.2
        rw [hsq q.1 q.2])
    rwa [e] at hcs
  -- second Cauchy--Schwarz: weight `W√F`, same `η`
  have hAST : (∫ q, W q.1 q.2 * F q.1 q.2 ∂(μ.prod μ)) ^ 2
      ≤ (∫ q, W q.1 q.2 * Real.sqrt (F q.1 q.2) ∂(μ.prod μ)) *
        ∫ q, W q.1 q.2 * (F q.1 q.2 * Real.sqrt (F q.1 q.2)) ∂(μ.prod μ) := by
    have e1 : ∀ q : Ω × Ω, W q.1 q.2 * Real.sqrt (F q.1 q.2) *
        Real.sqrt (F q.1 q.2) = W q.1 q.2 * F q.1 q.2 := fun q ↦ by
      rw [mul_assoc, Real.mul_self_sqrt (hF0 q.1 q.2)]
    have e2 : ∀ q : Ω × Ω, W q.1 q.2 * Real.sqrt (F q.1 q.2) *
        Real.sqrt (F q.1 q.2) ^ 2 =
          W q.1 q.2 * (F q.1 q.2 * Real.sqrt (F q.1 q.2)) := fun q ↦ by
      rw [hsq q.1 q.2]; ring
    have hcs := integral_mul_sq_le_integral_mul_integral_mul_sq
      (μ := μ.prod μ) (A := fun q : Ω × Ω ↦ W q.1 q.2 * Real.sqrt (F q.1 q.2))
      (η := fun q : Ω × Ω ↦ Real.sqrt (F q.1 q.2)) hiS
      (hiA.congr (ae_of_all _ fun q ↦ (e1 q).symm))
      (hiT.congr (ae_of_all _ fun q ↦ (e2 q).symm))
      (fun q ↦ mul_nonneg (W.nonneg _ _) (hr0 _ _))
    rwa [integral_congr_ae (ae_of_all _ e1), integral_congr_ae (ae_of_all _ e2)] at hcs
  -- eliminate `∫W√F`
  have hSn : (0 : ℝ) ≤ ∫ q, W q.1 q.2 * Real.sqrt (F q.1 q.2) ∂(μ.prod μ) :=
    integral_nonneg fun q ↦ mul_nonneg (W.nonneg _ _) (hr0 _ _)
  have hAn : (0 : ℝ) ≤ ∫ q, W q.1 q.2 * F q.1 q.2 ∂(μ.prod μ) :=
    integral_nonneg fun q ↦ mul_nonneg (W.nonneg _ _) (hF0 _ _)
  have hTn : (0 : ℝ) ≤
      ∫ q, W q.1 q.2 * (F q.1 q.2 * Real.sqrt (F q.1 q.2)) ∂(μ.prod μ) :=
    integral_nonneg fun q ↦ mul_nonneg (W.nonneg _ _) (mul_nonneg (hF0 _ _) (hr0 _ _))
  rcases eq_or_lt_of_le hAn with hA0 | hApos
  · rw [← hA0, zero_pow (by norm_num : (3 : ℕ) ≠ 0)]
    positivity
  · have h3 : (∫ q, W q.1 q.2 * F q.1 q.2 ∂(μ.prod μ)) ^ 4 ≤
        (∫ q, W q.1 q.2 * Real.sqrt (F q.1 q.2) ∂(μ.prod μ)) ^ 2 *
          (∫ q, W q.1 q.2 * (F q.1 q.2 * Real.sqrt (F q.1 q.2)) ∂(μ.prod μ)) ^ 2 := by
      nlinarith [pow_le_pow_left₀ (sq_nonneg
        (∫ q, W q.1 q.2 * F q.1 q.2 ∂(μ.prod μ))) hAST 2]
    have h4 : (∫ q, W q.1 q.2 * Real.sqrt (F q.1 q.2) ∂(μ.prod μ)) ^ 2 *
        (∫ q, W q.1 q.2 * (F q.1 q.2 * Real.sqrt (F q.1 q.2)) ∂(μ.prod μ)) ^ 2 ≤
        (cliqueDensity 2 W * ∫ q, W q.1 q.2 * F q.1 q.2 ∂(μ.prod μ)) *
          (∫ q, W q.1 q.2 * (F q.1 q.2 * Real.sqrt (F q.1 q.2)) ∂(μ.prod μ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hSA (sq_nonneg _)
    have h5 : (∫ q, W q.1 q.2 * F q.1 q.2 ∂(μ.prod μ)) *
        (∫ q, W q.1 q.2 * F q.1 q.2 ∂(μ.prod μ)) ^ 3 ≤
        (∫ q, W q.1 q.2 * F q.1 q.2 ∂(μ.prod μ)) * (cliqueDensity 2 W *
          (∫ q, W q.1 q.2 * (F q.1 q.2 * Real.sqrt (F q.1 q.2)) ∂(μ.prod μ)) ^ 2) := by
      nlinarith [h3, h4]
    exact le_of_mul_le_mul_left h5 hApos

/-! ### Collapsing the spine with the leaf weight on a spine endpoint -/

/-- **Pairing the codegree kernel against a spine-degree weight.**  The same
collapse as `integral_edge_pageOp`, but with the leaf weight carried by the
spine endpoint `y` rather than by the page vertex:

```
∫∫ W(x,y)·d(y)ˢ·H₀(x,y) dμdμ = ∫ d(z)ˢ·τ(z) dμ(z).
```

This is the exact identity behind the exceptional-page estimate of the note. -/
theorem integral_edge_degree_pageOp (W : Graphon Ω μ) {s : ℝ} (hs : 0 ≤ s) :
    (∫ q, W q.1 q.2 * (degree W q.2 ^ s * pageOp W 0 q.1 q.2) ∂(μ.prod μ)) =
      ∫ z, degree W z ^ s * rootedTriangle W z ∂μ := by
  have hm : Measurable (Function.uncurry
      fun x y ↦ W x y * (degree W y ^ s * pageOp W 0 x y)) :=
    W.measurable.mul
      (((measurable_degree_rpow W hs).comp measurable_snd).mul
        (measurable_pageOp W le_rfl))
  have hb : ∀ q : Ω × Ω, |W q.1 q.2 * (degree W q.2 ^ s * pageOp W 0 q.1 q.2)| ≤ 1 := by
    intro q
    have h0 : 0 ≤ W q.1 q.2 * (degree W q.2 ^ s * pageOp W 0 q.1 q.2) :=
      mul_nonneg (W.nonneg _ _)
        (mul_nonneg (degree_rpow_nonneg W s _) (pageOp_nonneg W le_rfl _ _))
    rw [abs_of_nonneg h0]
    exact mul_le_one₀ (W.le_one _ _)
      (mul_nonneg (degree_rpow_nonneg W s _) (pageOp_nonneg W le_rfl _ _))
      (mul_le_one₀ (degree_rpow_le_one W hs _) (pageOp_nonneg W le_rfl _ _)
        (pageOp_le_one W le_rfl _ _))
  have hi : Integrable (Function.uncurry
      fun x y ↦ W x y * (degree W y ^ s * pageOp W 0 x y)) (μ.prod μ) :=
    integrable_prod_of_bdd hm hb
  -- the codegree kernel, paired with its spine edge and integrated in `x`
  have hτ : ∀ y : Ω, (∫ x, W x y * pageOp W 0 x y ∂μ) = rootedTriangle W y := by
    intro y
    rw [rootedTriangle]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    show W x y * pageOp W 0 x y = ∫ z, W y x * W y z * W x z ∂μ
    rw [pageOp_zero_eq, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    show W x y * (W x z * W y z) = W y x * W y z * W x z
    rw [W.symm x y]
    ring
  rw [← integral_integral hi, integral_integral_swap hi]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  show (∫ x, W x y * (degree W y ^ s * pageOp W 0 x y) ∂μ)
      = degree W y ^ s * rootedTriangle W y
  rw [← hτ y, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  show W x y * (degree W y ^ s * pageOp W 0 x y)
      = degree W y ^ s * (W x y * pageOp W 0 x y)
  ring

/-- **Collapsing the spine across a branch operator.**  Integrating the spine
edge against `Λ_g` exchanges the page variable for the second spine variable:

```
∫∫ W(x,y)·Λ_g(x,y) dμdμ = ∫∫ W(x,z)·g(x,z)·H₀(x,z) dμdμ.
```

This is the counterpart of `integral_edge_pageOp` for a branch weight that is
not a function of the page vertex alone. -/
theorem integral_edge_branchOp (W : Graphon Ω μ) {g : Ω → Ω → ℝ}
    (hgm : Measurable (Function.uncurry g)) (hg0 : ∀ x y, 0 ≤ g x y)
    (hg1 : ∀ x y, g x y ≤ 1) :
    (∫ q, W q.1 q.2 * branchOp W g q.1 q.2 ∂(μ.prod μ)) =
      ∫ q, W q.1 q.2 * (g q.1 q.2 * pageOp W 0 q.1 q.2) ∂(μ.prod μ) := by
  -- both sides are bounded, so both are integrable on the product
  have hiL : Integrable (Function.uncurry fun x y ↦ W x y * branchOp W g x y)
      (μ.prod μ) := by
    refine integrable_prod_of_bdd (W.measurable.mul (measurable_branchOp W hgm))
      (C := 1) fun q ↦ ?_
    have h0 : 0 ≤ W q.1 q.2 * branchOp W g q.1 q.2 :=
      mul_nonneg (W.nonneg _ _) (branchOp_nonneg W hg0 _ _)
    show |W q.1 q.2 * branchOp W g q.1 q.2| ≤ 1
    rw [abs_of_nonneg h0]
    exact mul_le_one₀ (W.le_one _ _) (branchOp_nonneg W hg0 _ _)
      (branchOp_le_one W hgm hg0 hg1 _ _)
  have hiR : Integrable
      (Function.uncurry fun x z ↦ W x z * (g x z * pageOp W 0 x z)) (μ.prod μ) := by
    refine integrable_prod_of_bdd
      (W.measurable.mul (hgm.mul (measurable_pageOp W le_rfl))) (C := 1) fun q ↦ ?_
    have hin : 0 ≤ g q.1 q.2 * pageOp W 0 q.1 q.2 :=
      mul_nonneg (hg0 _ _) (pageOp_nonneg W le_rfl _ _)
    show |W q.1 q.2 * (g q.1 q.2 * pageOp W 0 q.1 q.2)| ≤ 1
    rw [abs_of_nonneg (mul_nonneg (W.nonneg _ _) hin)]
    exact mul_le_one₀ (W.le_one _ _) hin
      (mul_le_one₀ (hg1 _ _) (pageOp_nonneg W le_rfl _ _) (pageOp_le_one W le_rfl _ _))
  -- the exchange, one spine endpoint at a time
  have key : ∀ x : Ω, (∫ y, W x y * branchOp W g x y ∂μ)
      = ∫ z, W x z * (g x z * pageOp W 0 x z) ∂μ := by
    intro x
    have hi : Integrable
        (Function.uncurry fun y z ↦ W x y * (W x z * W y z * g x z)) (μ.prod μ) := by
      refine integrable_prod_of_bdd
        (((measurable_row W.measurable x).comp measurable_fst).mul
          ((((measurable_row W.measurable x).comp measurable_snd).mul
            W.measurable).mul ((measurable_row hgm x).comp measurable_snd)))
        (C := 1) fun q ↦ ?_
      have hin : 0 ≤ W x q.2 * W q.1 q.2 * g x q.2 :=
        mul_nonneg (mul_nonneg (W.nonneg _ _) (W.nonneg _ _)) (hg0 _ _)
      show |W x q.1 * (W x q.2 * W q.1 q.2 * g x q.2)| ≤ 1
      rw [abs_of_nonneg (mul_nonneg (W.nonneg _ _) hin)]
      exact mul_le_one₀ (W.le_one _ _) hin
        (mul_le_one₀ (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
          (hg0 _ _) (hg1 _ _))
    calc (∫ y, W x y * branchOp W g x y ∂μ)
        = ∫ y, ∫ z, W x y * (W x z * W y z * g x z) ∂μ ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
          show W x y * branchOp W g x y = ∫ z, W x y * (W x z * W y z * g x z) ∂μ
          rw [branchOp, ← integral_const_mul]
      _ = ∫ z, ∫ y, W x y * (W x z * W y z * g x z) ∂μ ∂μ := integral_integral_swap hi
      _ = ∫ z, W x z * (g x z * pageOp W 0 x z) ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
          show (∫ y, W x y * (W x z * W y z * g x z) ∂μ)
              = W x z * (g x z * pageOp W 0 x z)
          rw [pageOp_zero_eq, ← integral_const_mul, ← integral_const_mul]
          refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
          show W x y * (W x z * W y z * g x z) = W x z * (g x z * (W x y * W z y))
          rw [W.symm z y]
          ring
  rw [← integral_integral hiL, ← integral_integral hiR]
  exact integral_congr_ae (ae_of_all _ key)

/-! ### The branch bound -/

/-- **The page-paw branch bound.**  Any book of the family whose density peels
to `∫∫W·H₀·Λ_h` clears the target `p²(2p-1)³`, provided a comparison kernel `F`
satisfies the pointwise compression `F√F ≤ √h·H₀` and the scalar bound
`∫∫W·F ≥ p^{4/3}(2p-1)`.  The two scoped rows differ only in `h` and `F`. -/
theorem branch_bound (W : Graphon Ω μ) (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W)
    {h F : Ω → Ω → ℝ} (hm : Measurable (Function.uncurry h))
    (h0 : ∀ x y, 0 ≤ h x y) (h1 : ∀ x y, h x y ≤ 1)
    (hFm : Measurable (Function.uncurry F)) (hF0 : ∀ x y, 0 ≤ F x y)
    (hF1 : ∀ x y, F x y ≤ 1)
    (hkey : ∀ x z, F x z * Real.sqrt (F x z)
      ≤ Real.sqrt (h x z) * pageOp W 0 x z)
    (hbase : cliqueDensity 2 W ^ ((4 : ℝ) / 3) * (2 * cliqueDensity 2 W - 1)
      ≤ ∫ q, W q.1 q.2 * F q.1 q.2 ∂(μ.prod μ)) :
    cliqueDensity 2 W ^ 2 * (2 * cliqueDensity 2 W - 1) ^ 3
      ≤ ∫ q, W q.1 q.2 * pageOp W 0 q.1 q.2 * branchOp W h q.1 q.2 ∂(μ.prod μ) := by
  set p := cliqueDensity 2 W with hpdef
  have hppos : (0 : ℝ) < p := by linarith
  have h2p : (0 : ℝ) ≤ 2 * p - 1 := by linarith
  have hrm := measurable_sqrt_kernel hm
  have hr0 : ∀ x y : Ω, 0 ≤ Real.sqrt (h x y) := fun x y ↦ Real.sqrt_nonneg _
  have hr1 : ∀ x y : Ω, Real.sqrt (h x y) ≤ 1 := fun x y ↦ sqrt_kernel_le_one h1 x y
  have hRm := measurable_branchOp W hrm
  have hR0 : ∀ x y : Ω, 0 ≤ branchOp W (fun a b ↦ Real.sqrt (h a b)) x y :=
    fun x y ↦ branchOp_nonneg W hr0 x y
  have hR1 : ∀ x y : Ω, branchOp W (fun a b ↦ Real.sqrt (h a b)) x y ≤ 1 :=
    fun x y ↦ branchOp_le_one W hrm hr0 hr1 x y
  -- the density integrand, and the one obtained from the branch compression
  have hit : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * pageOp W 0 q.1 q.2 * branchOp W h q.1 q.2) (μ.prod μ) := by
    refine integrable_prod_of_bdd ((W.measurable.mul
      (measurable_pageOp W le_rfl)).mul (measurable_branchOp W hm)) (C := 1) fun q ↦ ?_
    have hn : 0 ≤ W q.1 q.2 * pageOp W 0 q.1 q.2 * branchOp W h q.1 q.2 :=
      mul_nonneg (mul_nonneg (W.nonneg _ _) (pageOp_nonneg W le_rfl _ _))
        (branchOp_nonneg W h0 _ _)
    show |W q.1 q.2 * pageOp W 0 q.1 q.2 * branchOp W h q.1 q.2| ≤ 1
    rw [abs_of_nonneg hn]
    exact mul_le_one₀ (mul_le_one₀ (W.le_one _ _) (pageOp_nonneg W le_rfl _ _)
      (pageOp_le_one W le_rfl _ _)) (branchOp_nonneg W h0 _ _)
      (branchOp_le_one W hm h0 h1 _ _)
  have hisq : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * branchOp W (fun a b ↦ Real.sqrt (h a b)) q.1 q.2 ^ 2) (μ.prod μ) :=
    integrable_edge W (F := fun x y ↦ branchOp W (fun a b ↦ Real.sqrt (h a b)) x y ^ 2)
      (hRm.pow_const 2) (fun x y ↦ pow_nonneg (hR0 x y) 2)
      fun x y ↦ pow_le_one₀ (hR0 x y) (hR1 x y)
  -- step 1: the branch compression, integrated
  have hstep1 : (∫ q, W q.1 q.2 *
      branchOp W (fun a b ↦ Real.sqrt (h a b)) q.1 q.2 ^ 2 ∂(μ.prod μ))
      ≤ ∫ q, W q.1 q.2 * pageOp W 0 q.1 q.2 * branchOp W h q.1 q.2 ∂(μ.prod μ) := by
    refine integral_mono hisq hit fun q ↦ ?_
    calc W q.1 q.2 * branchOp W (fun a b ↦ Real.sqrt (h a b)) q.1 q.2 ^ 2
        ≤ W q.1 q.2 * (pageOp W 0 q.1 q.2 * branchOp W h q.1 q.2) :=
          mul_le_mul_of_nonneg_left (sq_branchOp_le W hm h0 h1 q.1 q.2) (W.nonneg _ _)
      _ = W q.1 q.2 * pageOp W 0 q.1 q.2 * branchOp W h q.1 q.2 := by ring
  -- step 2: Cauchy--Schwarz on the spine edge
  have hstep2 := sq_edge_le W (F := fun x y ↦
    branchOp W (fun a b ↦ Real.sqrt (h a b)) x y) hRm hR0 hR1
  -- step 3: the exchange identity
  have hstep3 := integral_edge_branchOp W (g := fun a b ↦ Real.sqrt (h a b))
    hrm hr0 hr1
  -- step 4: the pointwise comparison, integrated
  have hiT : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * (F q.1 q.2 * Real.sqrt (F q.1 q.2))) (μ.prod μ) :=
    integrable_edge W (F := fun x y ↦ F x y * Real.sqrt (F x y))
      (hFm.mul (measurable_sqrt_kernel hFm))
      (fun x y ↦ mul_nonneg (hF0 x y) (Real.sqrt_nonneg _))
      fun x y ↦ mul_le_one₀ (hF1 x y) (Real.sqrt_nonneg _)
        (sqrt_kernel_le_one hF1 x y)
  have hiU : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * (Real.sqrt (h q.1 q.2) * pageOp W 0 q.1 q.2)) (μ.prod μ) :=
    integrable_edge W (F := fun x y ↦ Real.sqrt (h x y) * pageOp W 0 x y)
      (hrm.mul (measurable_pageOp W le_rfl))
      (fun x y ↦ mul_nonneg (hr0 x y) (pageOp_nonneg W le_rfl x y))
      fun x y ↦ mul_le_one₀ (hr1 x y) (pageOp_nonneg W le_rfl x y)
        (pageOp_le_one W le_rfl x y)
  have hstep4 : (∫ q, W q.1 q.2 * (F q.1 q.2 * Real.sqrt (F q.1 q.2)) ∂(μ.prod μ))
      ≤ ∫ q, W q.1 q.2 * branchOp W (fun a b ↦ Real.sqrt (h a b)) q.1 q.2
          ∂(μ.prod μ) := by
    rw [hstep3]
    exact integral_mono hiT hiU fun q ↦
      mul_le_mul_of_nonneg_left (hkey q.1 q.2) (W.nonneg _ _)
  -- step 5: edge Jensen at exponent 3/2
  have hstep5 := cube_edge_le W hFm hF0 hF1
  -- assemble
  set A := ∫ q, W q.1 q.2 * F q.1 q.2 ∂(μ.prod μ) with hAdef
  set T := ∫ q, W q.1 q.2 * (F q.1 q.2 * Real.sqrt (F q.1 q.2)) ∂(μ.prod μ) with hTdef
  set U := ∫ q, W q.1 q.2 * branchOp W (fun a b ↦ Real.sqrt (h a b)) q.1 q.2
    ∂(μ.prod μ) with hUdef
  set V := ∫ q, W q.1 q.2 *
    branchOp W (fun a b ↦ Real.sqrt (h a b)) q.1 q.2 ^ 2 ∂(μ.prod μ) with hVdef
  set t := ∫ q, W q.1 q.2 * pageOp W 0 q.1 q.2 * branchOp W h q.1 q.2 ∂(μ.prod μ)
    with htdef
  have hTn : 0 ≤ T := integral_nonneg fun q ↦
    mul_nonneg (W.nonneg _ _) (mul_nonneg (hF0 _ _) (Real.sqrt_nonneg _))
  have hTU : T ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ hTn hstep4 2
  have hchain : A ^ 3 ≤ p ^ 2 * t := by
    calc A ^ 3 ≤ p * T ^ 2 := hstep5
      _ ≤ p * U ^ 2 := mul_le_mul_of_nonneg_left hTU hppos.le
      _ ≤ p * (p * V) := mul_le_mul_of_nonneg_left hstep2 hppos.le
      _ ≤ p * (p * t) := by
          have := mul_le_mul_of_nonneg_left hstep1 hppos.le
          exact mul_le_mul_of_nonneg_left this hppos.le
      _ = p ^ 2 * t := by ring
  -- the scalar input, cubed
  have hbn : 0 ≤ p ^ ((4 : ℝ) / 3) * (2 * p - 1) :=
    mul_nonneg (Real.rpow_nonneg hppos.le _) h2p
  have hcubed := pow_le_pow_left₀ hbn hbase 3
  have h43 : (p ^ ((4 : ℝ) / 3)) ^ (3 : ℕ) = p ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast (p ^ ((4 : ℝ) / 3)) 3, ← Real.rpow_mul hppos.le,
      show (4 : ℝ) / 3 * (3 : ℕ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [mul_pow, h43] at hcubed
  have hfin : p ^ 2 * (p ^ 2 * (2 * p - 1) ^ 3) ≤ p ^ 2 * t := by
    calc p ^ 2 * (p ^ 2 * (2 * p - 1) ^ 3) = p ^ 4 * (2 * p - 1) ^ 3 := by ring
      _ ≤ A ^ 3 := hcubed
      _ ≤ p ^ 2 * t := hchain
  exact le_of_mul_le_mul_left hfin (by positivity)

end Edge

end Taeyoung.Methods.PagePawBranch
