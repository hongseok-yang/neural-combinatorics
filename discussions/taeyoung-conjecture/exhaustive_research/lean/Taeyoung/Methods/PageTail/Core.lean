import Taeyoung.Methods.BookTail.Core

/-!
# Triangle books with a two-edge tail on a page: the analytic core

`notes/triangle_book_page_two_edge_tail.tex`.  Moving the tail from a spine
endpoint to a page changes the density from `∫∫ W·A·S^m` to

```
t(P_m,W) = ∫∫ W(x,y)·G(x,y)·S(x,y)^{m-1},
G(x,y) = ∫ W(x,z)W(y,z)A(z)dz,   S(x,y) = ∫ W(x,z)W(y,z)dz,
```

so the weight `A = T_W d` now sits *inside* one page rather than outside all of
them.  The target is unchanged, `Φ = p³(2p-1)^m`.

The note handles this by averaging over the page orbit and applying AM–GM,
which distributes `A` over all `m` pages with exponent `1/m`; at `m = 2`, the
only scoped case, that average is a single weighted Cauchy–Schwarz,

```
R(x,y)² ≤ S(x,y)·G(x,y),      R(x,y) = ∫ W(x,z)W(y,z)√(A(z))dz.
```

A second Cauchy–Schwarz on `μ ⊗ μ` with weight `W` then reduces everything to
the fractionally weighted rooted triangle `∫√A·τ`, and the whole row rests on

```
∫ √(A(z))·τ(z) dz ≥ p²(2p-1).
```

**The route here differs from the note's.**  The note gets that from convexity
and monotonicity of `f_{p,α}(a) = a^α max{2a-p,0}` — proved by comparing
one-sided derivatives across `a = p/2` — followed by Jensen at `∫A ≥ p²`.  As in
`Methods/TwoRoot/Core.lean`, the formalization proves the affine minorant that
Jensen would have produced instead, and never mentions `ConvexOn`:

```
p²(2p-1) + (3p - ½)(a - p²) ≤ √a·max{2a-p,0}      for a ≥ 0, p ∈ [1/2,1].
```

Substituting `a = s²` makes both cases polynomial.  Above the truncation the
difference factors as `2(s-p)²(s + p/2 + ¼)`; below it the line is at most
`-p(p - ½)² ≤ 0`.  So the only calculus in the note is replaced by two
`nlinarith` certificates.
-/

open MeasureTheory

namespace Taeyoung.Methods.PageTail

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PureChordal Taeyoung.Methods.BookTail

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The page operator with an arbitrary vertex weight

`Link.pageOp` carries the weight `d^s`.  The page that bears the tail carries
`A = T_W d` instead, and the Cauchy–Schwarz that splits it carries `√A`, so the
weight has to become a parameter. -/

/-- `H_φ(x,y) = ∫ W(x,z)W(y,z)φ(z)dz`. -/
noncomputable def pageWeightOp (W : Graphon Ω μ) (φ : Ω → ℝ) (x y : Ω) : ℝ :=
  ∫ z, W x z * W y z * φ z ∂μ

section Weight

variable (W : Graphon Ω μ) {φ : Ω → ℝ}
  (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1)

include hφm in
lemma measurable_pageWeightOp_integrand (x y : Ω) :
    Measurable fun z ↦ W x z * W y z * φ z :=
  ((measurable_row W.measurable x).mul (measurable_row W.measurable y)).mul hφm

include hφ0 in
lemma pageWeightOp_integrand_nonneg (x y z : Ω) : 0 ≤ W x z * W y z * φ z :=
  mul_nonneg (mul_nonneg (W.nonneg x z) (W.nonneg y z)) (hφ0 z)

include hφ0 hφ1 in
lemma pageWeightOp_integrand_le_one (x y z : Ω) : W x z * W y z * φ z ≤ 1 :=
  mul_le_one₀ (mul_le_one₀ (W.le_one x z) (W.nonneg y z) (W.le_one y z))
    (hφ0 z) (hφ1 z)

include hφm hφ0 hφ1 in
lemma integrable_pageWeightOp_integrand (x y : Ω) :
    Integrable (fun z ↦ W x z * W y z * φ z) μ :=
  integrable_of_bdd (measurable_pageWeightOp_integrand W hφm x y) (C := 1)
    fun z ↦ by
      rw [abs_of_nonneg (pageWeightOp_integrand_nonneg W hφ0 x y z)]
      exact pageWeightOp_integrand_le_one W hφ0 hφ1 x y z

include hφ0 in
lemma pageWeightOp_nonneg (x y : Ω) : 0 ≤ pageWeightOp W φ x y :=
  integral_nonneg fun z ↦ pageWeightOp_integrand_nonneg W hφ0 x y z

include hφm hφ0 hφ1 in
lemma pageWeightOp_le_one (x y : Ω) : pageWeightOp W φ x y ≤ 1 := by
  calc pageWeightOp W φ x y ≤ ∫ _z : Ω, (1 : ℝ) ∂μ :=
        integral_mono (integrable_pageWeightOp_integrand W hφm hφ0 hφ1 x y)
          (integrable_const _) fun z ↦
          pageWeightOp_integrand_le_one W hφ0 hφ1 x y z
    _ = 1 := by simp

include hφm in
lemma measurable_pageWeightOp :
    Measurable fun q : Ω × Ω ↦ pageWeightOp W φ q.1 q.2 := by
  have hg : StronglyMeasurable fun r : (Ω × Ω) × Ω ↦
      W r.1.1 r.2 * W r.1.2 r.2 * φ r.2 := by
    refine (?_ : Measurable _).stronglyMeasurable
    exact ((W.measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (W.measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).mul
      (hφm.comp measurable_snd)
  exact (hg.integral_prod_right' (ν := μ)).measurable

include hφm hφ0 hφ1 in
/-- **Pairing a weighted page against its spine edge.**  The clone of
`Link.integral_edge_pageOp` with `d^s` replaced by `φ`. -/
theorem integral_edge_pageWeightOp :
    (∫ q, W q.1 q.2 * pageWeightOp W φ q.1 q.2 ∂(μ.prod μ)) =
      ∫ z, φ z * rootedTriangle W z ∂μ := by
  set g : (Ω × Ω) → Ω → ℝ :=
    fun q z ↦ W q.1 q.2 * (W q.1 z * W q.2 z * φ z) with hg
  have hgm : Measurable (Function.uncurry g) := by
    refine ((W.measurable.comp measurable_fst).mul ?_)
    refine (((W.measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (W.measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).mul ?_)
    exact hφm.comp measurable_snd
  have hgb : ∀ q z, |g q z| ≤ 1 := by
    intro q z
    have h0 : 0 ≤ g q z :=
      mul_nonneg (W.nonneg _ _) (pageWeightOp_integrand_nonneg W hφ0 q.1 q.2 z)
    rw [abs_of_nonneg h0]
    exact mul_le_one₀ (W.le_one _ _)
      (pageWeightOp_integrand_nonneg W hφ0 q.1 q.2 z)
      (pageWeightOp_integrand_le_one W hφ0 hφ1 q.1 q.2 z)
  have hgi : Integrable (Function.uncurry g) ((μ.prod μ).prod μ) :=
    (integrable_const (μ := (μ.prod μ).prod μ) (1 : ℝ)).mono'
      hgm.aestronglyMeasurable
      (ae_of_all _ fun r ↦ by rw [Real.norm_eq_abs]; exact hgb r.1 r.2)
  have hstep : (∫ q, W q.1 q.2 * pageWeightOp W φ q.1 q.2 ∂(μ.prod μ)) =
      ∫ q, ∫ z, g q z ∂μ ∂(μ.prod μ) := by
    refine integral_congr_ae (ae_of_all _ fun q ↦ ?_)
    simp only [hg, pageWeightOp]
    rw [← integral_const_mul]
  rw [hstep, integral_integral_swap hgi]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  simp only []
  have hz : (∫ q, g q z ∂(μ.prod μ)) =
      φ z * ∫ q, W z q.1 * W z q.2 * W q.1 q.2 ∂(μ.prod μ) := by
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

end Weight

/-! ### `√A` as a page weight -/

/-- `√(A(x))`, the weight the Cauchy–Schwarz splits `A` into. -/
noncomputable def sqrtPathOp (W : Graphon Ω μ) (x : Ω) : ℝ :=
  Real.sqrt (pathOp W x)

section SqrtBasic

variable (W : Graphon Ω μ)

lemma measurable_sqrtPathOp : Measurable (sqrtPathOp W) :=
  Real.continuous_sqrt.measurable.comp (measurable_pathOp W)

lemma sqrtPathOp_nonneg (x : Ω) : 0 ≤ sqrtPathOp W x := Real.sqrt_nonneg _

lemma sqrtPathOp_le_one (x : Ω) : sqrtPathOp W x ≤ 1 := by
  rw [sqrtPathOp, show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (pathOp_le_one W x)

lemma sq_sqrtPathOp (x : Ω) : sqrtPathOp W x ^ 2 = pathOp W x :=
  Real.sq_sqrt (pathOp_nonneg W x)

end SqrtBasic

/-! ### The splitting Cauchy–Schwarz: `R² ≤ S·G` -/

/-- Weighted Cauchy–Schwarz inside a page, with weight `W(x,·)W(y,·)`: the
`√A`-page squared is dominated by the plain page times the `A`-page. -/
theorem sq_pageWeightOp_sqrt_le (W : Graphon Ω μ) (x y : Ω) :
    pageWeightOp W (sqrtPathOp W) x y ^ 2 ≤
      pageOp W 0 x y * pageWeightOp W (pathOp W) x y := by
  have hwm : Measurable fun z ↦ W x z * W y z :=
    (measurable_row W.measurable x).mul (measurable_row W.measurable y)
  have hw0 : ∀ z, 0 ≤ W x z * W y z := fun z ↦
    mul_nonneg (W.nonneg x z) (W.nonneg y z)
  have hw1 : ∀ z, W x z * W y z ≤ 1 := fun z ↦
    mul_le_one₀ (W.le_one x z) (W.nonneg y z) (W.le_one y z)
  have hwi : Integrable (fun z ↦ W x z * W y z) μ :=
    integrable_of_bdd hwm (C := 1) fun z ↦ by
      rw [abs_of_nonneg (hw0 z)]; exact hw1 z
  have hwsi : Integrable (fun z ↦ W x z * W y z * sqrtPathOp W z) μ :=
    integrable_pageWeightOp_integrand W (measurable_sqrtPathOp W)
      (sqrtPathOp_nonneg W) (sqrtPathOp_le_one W) x y
  have hwsq : Integrable (fun z ↦ W x z * W y z * sqrtPathOp W z ^ 2) μ := by
    refine Integrable.congr (integrable_pageWeightOp_integrand W
      (measurable_pathOp W) (pathOp_nonneg W) (pathOp_le_one W) x y)
      (ae_of_all _ fun z ↦ ?_)
    show W x z * W y z * pathOp W z = W x z * W y z * sqrtPathOp W z ^ 2
    rw [sq_sqrtPathOp]
  have hcs := integral_mul_sq_le_integral_mul_integral_mul_sq (μ := μ)
    (A := fun z ↦ W x z * W y z) (η := sqrtPathOp W) hwi hwsi hwsq hw0
  have hG : (∫ z, W x z * W y z * sqrtPathOp W z ^ 2 ∂μ) =
      pageWeightOp W (pathOp W) x y := by
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    show W x z * W y z * sqrtPathOp W z ^ 2 = W x z * W y z * pathOp W z
    rw [sq_sqrtPathOp]
  have hS : (∫ z, W x z * W y z ∂μ) = pageOp W 0 x y :=
    (pageOp_zero_eq W x y).symm
  rw [hG, hS] at hcs
  exact hcs

/-! ### The affine minorant replacing Jensen -/

/-- **The tangent line under `a ↦ √a·max{2a-p,0}` at `a = p²`.**  Above the
truncation the difference is `2(s-p)²(s + p/2 + ¼)` after `a = s²`; below it the
line has already fallen to `-p(p-½)² ≤ 0`. -/
theorem tangent_sqrt {p a : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (ha : 0 ≤ a) :
    p ^ 2 * (2 * p - 1) + (3 * p - 1 / 2) * (a - p ^ 2) ≤
      Real.sqrt a * max (2 * a - p) 0 := by
  set s := Real.sqrt a with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = a := Real.sq_sqrt ha
  rcases le_or_gt p (2 * a) with hcase | hcase
  · rw [max_eq_left (by linarith)]
    have hfac : 0 ≤ 2 * (s - p) ^ 2 * (s + p / 2 + 1 / 4) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith [hfac, hs2]
  · rw [max_eq_right (by linarith), mul_zero]
    nlinarith [sq_nonneg (p - 1 / 2), hcase, hp]

/-- **The fractionally weighted rooted-triangle bound**, `∫√A·τ ≥ p²(2p-1)`. -/
theorem sqrt_weighted_rootedTriangle (W : Graphon Ω μ)
    (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 2 * (2 * cliqueDensity 2 W - 1) ≤
      ∫ x, sqrtPathOp W x * rootedTriangle W x ∂μ := by
  set p := cliqueDensity 2 W with hpdef
  have hp1 : p ≤ 1 := cliqueDensity_le_one 2 W
  -- the affine minorant, as an integrand
  have hlinint : Integrable
      (fun x ↦ (3 * p - 1 / 2) * pathOp W x +
        (p ^ 2 * (2 * p - 1) - (3 * p - 1 / 2) * p ^ 2)) μ :=
    ((integrable_pathOp W).const_mul _).add (integrable_const _)
  have hτint : Integrable (fun x ↦ sqrtPathOp W x * rootedTriangle W x) μ :=
    integrable_of_bdd ((measurable_sqrtPathOp W).mul
      (measurable_rootedTriangle W)) (C := 1) fun x ↦ by
      rw [abs_of_nonneg (mul_nonneg (sqrtPathOp_nonneg W x)
        (rootedTriangle_nonneg W x))]
      exact mul_le_one₀ (sqrtPathOp_le_one W x) (rootedTriangle_nonneg W x)
        (rootedTriangle_le_one W x)
  -- pointwise: the line is under `√A·max{2A-p,0}`, which is under `√A·τ`
  have hpt : ∀ x, (3 * p - 1 / 2) * pathOp W x +
      (p ^ 2 * (2 * p - 1) - (3 * p - 1 / 2) * p ^ 2) ≤
        sqrtPathOp W x * rootedTriangle W x := by
    intro x
    have htan := tangent_sqrt (a := pathOp W x) hp hp1 (pathOp_nonneg W x)
    have hmax : max (2 * pathOp W x - p) 0 ≤ rootedTriangle W x :=
      max_le (rootedTriangle_ge W x) (rootedTriangle_nonneg W x)
    have hstep : Real.sqrt (pathOp W x) * max (2 * pathOp W x - p) 0 ≤
        sqrtPathOp W x * rootedTriangle W x :=
      mul_le_mul_of_nonneg_left hmax (sqrtPathOp_nonneg W x)
    linarith [htan, hstep]
  have hmono := integral_mono hlinint hτint hpt
  -- the line integrates to `(3p - ½)·M + c`, and `M ≥ p²`
  have hval : (∫ x, (3 * p - 1 / 2) * pathOp W x +
      (p ^ 2 * (2 * p - 1) - (3 * p - 1 / 2) * p ^ 2) ∂μ) =
      (3 * p - 1 / 2) * (∫ x, pathOp W x ∂μ) +
        (p ^ 2 * (2 * p - 1) - (3 * p - 1 / 2) * p ^ 2) := by
    rw [integral_add ((integrable_pathOp W).const_mul _) (integrable_const _),
      integral_const_mul, integral_const]
    simp
  rw [hval] at hmono
  have hM : p ^ 2 ≤ ∫ x, pathOp W x ∂μ := sq_le_integral_pathOp W
  nlinarith [hmono, hM]

end Taeyoung.Methods.PageTail
