import Taeyoung.Methods.GeometricMean
import Taeyoung.Methods.Link.PageOp
import Taeyoung.Methods.AffineProduct

/-!
# Two-root triangle-leaf books: the analytic core

`notes/two_root_triangle_leaf_cones.tex`.  The family `B_{m,a,b}` has a spine
`u,v`, `m` pages adjacent to both, `a` private leaves on `u` and `b` on `v`.
Peeling every leaf and every page turns its density into

```
t(B_{m,a,b}, W) = ∫∫ W(x,y)·d(x)^a·d(y)^b·H₀(x,y)^m,
```

with `H₀` the page operator at exponent `0`.  With `n = a+b` the target is
`Φ = p^{n+1}(2p-1)^m`.

This file proves the bound

```
∫∫ W(x,y)·Z(x,y)^n·H₀(x,y)^m ≥ p^{n+1}(2p-1)^m,        Z = √(d(x)d(y)),
```

for every `n` and every `m ≥ 1`, at every admissible density `p ≥ 1/2`.  Each
row then only has to peel its own graph and match `d(x)^a d(y)^b` against `Z^n`
— an equality when `a = b`, and one more AM–GM when they differ.

Three inputs, all already available:

* `Link.le_pageOp_zero`: `H₀(x,y) ≥ d(x)+d(y)-1`, from `AB ≥ A+B-1`;
* `GeometricMean.two_mul_geoMean_le`: `d(x)+d(y) ≥ 2Z`, so `H₀ ≥ 2Z-1`, and
  `H₀ ≥ 0` upgrades that to the truncation `H₀ ≥ max{2Z-1,0}`;
* `GeometricMean.sq_le_integral_geoIntegrand`: `∫∫ W·Z ≥ p²`.

What remains is Jensen for `f_{n,m}(z) = zⁿ·max{2z-1,0}^m` under the edge-biased
measure, and it is done by the tangent-line trick rather than by convexity:
`affineProd_tangent` at the root list `1^n 2^m` supplies the affine minorant
through `p` wherever `z ≥ 1/2`, and below `1/2` the truncated `f` vanishes while
the same line — evaluated at `1/2`, where it is already `≤ f(1/2) = 0` — only
decreases.  So no `ConvexOn`, no one-sided derivatives, and no case split on the
sign of `2z-1` inside the integral.
-/

open MeasureTheory

namespace Taeyoung.Methods.TwoRoot

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.GeometricMean

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The root list `1^n 2^m` -/

/-- The roots of `χ_{B_{m,a,b}}` other than `0`: `1` with multiplicity `n`, `2`
with multiplicity `m`. -/
def rootList (n m : ℕ) : List ℝ :=
  List.replicate n 1 ++ List.replicate m 2

@[simp] lemma affineProd_replicate_two (m : ℕ) (z : ℝ) :
    affineProd (List.replicate m 2) z = (2 * z - 1) ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [List.replicate_succ, affineProd_cons, ih, pow_succ]
      ring_nf

lemma affineProd_rootList (n m : ℕ) (z : ℝ) :
    affineProd (rootList n m) z = z ^ n * (2 * z - 1) ^ m := by
  rw [rootList, affineProd_append, affineProd_replicate_one,
    affineProd_replicate_two]

lemma rootList_nonneg (n m : ℕ) : ∀ k ∈ rootList n m, (0 : ℝ) ≤ k := by
  intro k hk
  rw [rootList, List.mem_append] at hk
  rcases hk with h | h
  · rw [List.eq_of_mem_replicate h]; norm_num
  · rw [List.eq_of_mem_replicate h]; norm_num

lemma rootList_factor_nonneg {n m : ℕ} {z : ℝ} (hz : (1 : ℝ) / 2 ≤ z) :
    ∀ k ∈ rootList n m, (0 : ℝ) ≤ 1 - k * (1 - z) := by
  intro k hk
  rw [rootList, List.mem_append] at hk
  rcases hk with h | h
  · rw [List.eq_of_mem_replicate h]; linarith
  · rw [List.eq_of_mem_replicate h]; linarith

/-! ### The truncated tangent minorant -/

/-- **The affine minorant of `f_{n,m}(z) = zⁿ·max{2z-1,0}^m` through `p`.**  It
is `affineProd_tangent` above the threshold and a monotonicity argument below
it: at `z = 1/2` the tangent line is already at most `f(1/2) = 0`, and it is
nondecreasing because `affineProdDeriv ≥ 0`. -/
theorem tangent_trunc {n m : ℕ} (hm : 0 < m) {p w : ℝ} (hp : (1 : ℝ) / 2 ≤ p) :
    affineProd (rootList n m) p + affineProdDeriv (rootList n m) p * (w - p) ≤
      w ^ n * max (2 * w - 1) 0 ^ m := by
  have hk := rootList_nonneg n m
  have hc := rootList_factor_nonneg (n := n) (m := m) hp
  have hD : 0 ≤ affineProdDeriv (rootList n m) p := affineProdDeriv_nonneg hk hc
  rcases le_or_gt ((1 : ℝ) / 2) w with hcase | hcase
  · -- above the threshold the truncation is inactive
    have hmax : max (2 * w - 1) 0 = 2 * w - 1 := max_eq_left (by linarith)
    rw [hmax, ← affineProd_rootList]
    exact affineProd_tangent hk hc (rootList_factor_nonneg hcase)
  · -- below it the target vanishes and the line has already crossed zero
    have hmax : max (2 * w - 1) 0 = 0 := max_eq_right (by linarith)
    have hhalf : affineProd (rootList n m) p +
        affineProdDeriv (rootList n m) p * (1 / 2 - p) ≤ 0 := by
      have h := affineProd_tangent (ks := rootList n m) (c := p) (w := 1 / 2)
        hk hc (rootList_factor_nonneg le_rfl)
      have hz : affineProd (rootList n m) ((1 : ℝ) / 2) = 0 := by
        rw [affineProd_rootList, show 2 * ((1 : ℝ) / 2) - 1 = 0 by ring,
          zero_pow hm.ne', mul_zero]
      rwa [hz] at h
    have hmono : affineProdDeriv (rootList n m) p * (w - p) ≤
        affineProdDeriv (rootList n m) p * (1 / 2 - p) :=
      mul_le_mul_of_nonneg_left (by linarith) hD
    rw [hmax, zero_pow hm.ne', mul_zero]
    linarith

/-! ### Jensen under the edge-biased measure -/

/-- The truncated integrand `W·Zⁿ·max{2Z-1,0}^m`. -/
noncomputable def truncIntegrand (W : Graphon Ω μ) (n m : ℕ) (q : Ω × Ω) : ℝ :=
  W q.1 q.2 * (geoMean W q ^ n * max (2 * geoMean W q - 1) 0 ^ m)

lemma measurable_truncIntegrand (W : Graphon Ω μ) (n m : ℕ) :
    Measurable (truncIntegrand W n m) :=
  W.measurable.mul (((measurable_geoMean W).pow_const n).mul
    ((((measurable_geoMean W).const_mul 2).sub measurable_const).max
      measurable_const |>.pow_const m))

lemma truncIntegrand_nonneg (W : Graphon Ω μ) (n m : ℕ) (q : Ω × Ω) :
    0 ≤ truncIntegrand W n m q :=
  mul_nonneg (W.nonneg _ _)
    (mul_nonneg (pow_nonneg (geoMean_nonneg W q) n)
      (pow_nonneg (le_max_right _ _) m))

lemma truncIntegrand_le_one (W : Graphon Ω μ) (n m : ℕ) (q : Ω × Ω) :
    truncIntegrand W n m q ≤ 1 := by
  have hZ : geoMean W q ^ n ≤ 1 :=
    pow_le_one₀ (geoMean_nonneg W q) (geoMean_le_one W q)
  have hmax : max (2 * geoMean W q - 1) 0 ^ m ≤ 1 :=
    pow_le_one₀ (le_max_right _ _)
      (max_le (by linarith [geoMean_le_one W q]) zero_le_one)
  exact mul_le_one₀ (W.le_one _ _)
    (mul_nonneg (pow_nonneg (geoMean_nonneg W q) n)
      (pow_nonneg (le_max_right _ _) m))
    (mul_le_one₀ hZ (pow_nonneg (le_max_right _ _) m) hmax)

lemma integrable_truncIntegrand (W : Graphon Ω μ) (n m : ℕ) :
    Integrable (truncIntegrand W n m) (μ.prod μ) :=
  integrable_prod_of_bdd (measurable_truncIntegrand W n m) (C := 1) fun q ↦ by
    rw [abs_of_nonneg (truncIntegrand_nonneg W n m q)]
    exact truncIntegrand_le_one W n m q

/-- **Jensen for `f_{n,m}` under the edge-biased measure.**  The tangent line
through `p` integrates to `Φ` exactly, because its slope is nonnegative and the
biased mean of `Z` is at least `p`. -/
theorem target_le_integral_truncIntegrand (W : Graphon Ω μ) (n m : ℕ)
    (hm : 0 < m) (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ (n + 1) * (2 * cliqueDensity 2 W - 1) ^ m ≤
      ∫ q, truncIntegrand W n m q ∂(μ.prod μ) := by
  set p := cliqueDensity 2 W with hpdef
  set A := affineProd (rootList n m) p with hAdef
  set B := affineProdDeriv (rootList n m) p with hBdef
  have hB : 0 ≤ B :=
    affineProdDeriv_nonneg (rootList_nonneg n m) (rootList_factor_nonneg hp)
  -- the tangent line, as an integrand
  have hlin : ∀ q : Ω × Ω, W q.1 q.2 * (A + B * (geoMean W q - p)) =
      A * W q.1 q.2 + B * geoIntegrand W q - B * p * W q.1 q.2 := by
    intro q
    rw [geoIntegrand]
    ring
  have hWint : Integrable (fun q : Ω × Ω ↦ W q.1 q.2) (μ.prod μ) :=
    integrable_prod_of_bdd W.measurable (C := 1) fun q ↦ by
      rw [abs_of_nonneg (W.nonneg q.1 q.2)]; exact W.le_one q.1 q.2
  have hlinint : Integrable
      (fun q : Ω × Ω ↦ W q.1 q.2 * (A + B * (geoMean W q - p))) (μ.prod μ) := by
    refine Integrable.congr ?_ (ae_of_all _ fun q ↦ (hlin q).symm)
    exact ((hWint.const_mul A).add
      ((integrable_geoIntegrand W).const_mul B)).sub (hWint.const_mul (B * p))
  -- its integral is `A·p + B·(∫WZ - p²) ≥ A·p`
  have hval : (∫ q, W q.1 q.2 * (A + B * (geoMean W q - p)) ∂(μ.prod μ)) =
      A * p + B * (∫ q, geoIntegrand W q ∂(μ.prod μ)) - B * p * p := by
    have hedge : (∫ q, W q.1 q.2 ∂(μ.prod μ)) = p := by
      rw [integral_prod_edge, hpdef]
    have e1 : (∫ q, W q.1 q.2 * (A + B * (geoMean W q - p)) ∂(μ.prod μ)) =
        (∫ q, (A * W q.1 q.2 + B * geoIntegrand W q) ∂(μ.prod μ)) -
          ∫ q, B * p * W q.1 q.2 ∂(μ.prod μ) := by
      rw [integral_congr_ae (ae_of_all _ hlin)]
      exact integral_sub
        ((hWint.const_mul A).add ((integrable_geoIntegrand W).const_mul B))
        (hWint.const_mul (B * p))
    have e2 : (∫ q, (A * W q.1 q.2 + B * geoIntegrand W q) ∂(μ.prod μ)) =
        (∫ q, A * W q.1 q.2 ∂(μ.prod μ)) +
          ∫ q, B * geoIntegrand W q ∂(μ.prod μ) :=
      integral_add (hWint.const_mul A) ((integrable_geoIntegrand W).const_mul B)
    rw [e1, e2]
    simp only [integral_const_mul, hedge]
  have hgeo : p ^ 2 ≤ ∫ q, geoIntegrand W q ∂(μ.prod μ) :=
    sq_le_integral_geoIntegrand W
  have hlow : A * p ≤ ∫ q, W q.1 q.2 * (A + B * (geoMean W q - p)) ∂(μ.prod μ) := by
    rw [hval]
    nlinarith [mul_le_mul_of_nonneg_left hgeo hB]
  -- the tangent line lies under the truncated integrand
  have hmono : (∫ q, W q.1 q.2 * (A + B * (geoMean W q - p)) ∂(μ.prod μ)) ≤
      ∫ q, truncIntegrand W n m q ∂(μ.prod μ) := by
    refine integral_mono hlinint (integrable_truncIntegrand W n m) fun q ↦ ?_
    exact mul_le_mul_of_nonneg_left
      (tangent_trunc hm hp) (W.nonneg _ _)
  refine le_trans (le_of_eq ?_) (le_trans hlow hmono)
  rw [hAdef, affineProd_rootList, pow_succ]
  ring

/-! ### Replacing the truncation by the page operator -/

/-- The genuine integrand `W·Zⁿ·H₀^m`. -/
noncomputable def pageIntegrand (W : Graphon Ω μ) (n m : ℕ) (q : Ω × Ω) : ℝ :=
  W q.1 q.2 * (geoMean W q ^ n * pageOp W 0 q.1 q.2 ^ m)

lemma measurable_pageIntegrand (W : Graphon Ω μ) (n m : ℕ) :
    Measurable (pageIntegrand W n m) :=
  W.measurable.mul (((measurable_geoMean W).pow_const n).mul
    ((measurable_pageOp W le_rfl).pow_const m))

lemma pageIntegrand_nonneg (W : Graphon Ω μ) (n m : ℕ) (q : Ω × Ω) :
    0 ≤ pageIntegrand W n m q :=
  mul_nonneg (W.nonneg _ _)
    (mul_nonneg (pow_nonneg (geoMean_nonneg W q) n)
      (pow_nonneg (pageOp_nonneg W le_rfl _ _) m))

lemma pageIntegrand_le_one (W : Graphon Ω μ) (n m : ℕ) (q : Ω × Ω) :
    pageIntegrand W n m q ≤ 1 := by
  have hZ : geoMean W q ^ n ≤ 1 :=
    pow_le_one₀ (geoMean_nonneg W q) (geoMean_le_one W q)
  have hH : pageOp W 0 q.1 q.2 ^ m ≤ 1 :=
    pow_le_one₀ (pageOp_nonneg W le_rfl _ _) (pageOp_le_one W le_rfl _ _)
  exact mul_le_one₀ (W.le_one _ _)
    (mul_nonneg (pow_nonneg (geoMean_nonneg W q) n)
      (pow_nonneg (pageOp_nonneg W le_rfl _ _) m))
    (mul_le_one₀ hZ (pow_nonneg (pageOp_nonneg W le_rfl _ _) m) hH)

lemma integrable_pageIntegrand (W : Graphon Ω μ) (n m : ℕ) :
    Integrable (pageIntegrand W n m) (μ.prod μ) :=
  integrable_prod_of_bdd (measurable_pageIntegrand W n m) (C := 1) fun q ↦ by
    rw [abs_of_nonneg (pageIntegrand_nonneg W n m q)]
    exact pageIntegrand_le_one W n m q

/-- `H₀ ≥ max{2Z-1,0}`: the two-vertex lower bound composed with AM–GM. -/
lemma max_le_pageOp_zero (W : Graphon Ω μ) (q : Ω × Ω) :
    max (2 * geoMean W q - 1) 0 ≤ pageOp W 0 q.1 q.2 := by
  refine max_le ?_ (pageOp_nonneg W le_rfl _ _)
  have h1 := le_pageOp_zero W q.1 q.2
  have h2 := two_mul_geoMean_le W q
  linarith

/-- **The core bound.**  For every `n` and every `m ≥ 1`, at every admissible
density. -/
theorem target_le_integral_pageIntegrand (W : Graphon Ω μ) (n m : ℕ)
    (hm : 0 < m) (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ (n + 1) * (2 * cliqueDensity 2 W - 1) ^ m ≤
      ∫ q, pageIntegrand W n m q ∂(μ.prod μ) := by
  refine le_trans (target_le_integral_truncIntegrand W n m hm hp) ?_
  refine integral_mono (integrable_truncIntegrand W n m)
    (integrable_pageIntegrand W n m) fun q ↦ ?_
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_
    (pow_nonneg (geoMean_nonneg W q) n)) (W.nonneg _ _)
  exact pow_le_pow_left₀ (le_max_right _ _) (max_le_pageOp_zero W q) m

end Taeyoung.Methods.TwoRoot
