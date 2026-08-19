import Taeyoung.Methods.Atlas178.Scalar
import Taeyoung.Methods.K4Tail.Link
import Taeyoung.Methods.TriangleDensity

/-!
# Atlas 178: the link reduction

`notes/atlas178_half_degree_weighted_k4.tex` §2–§4, transported to a point of
the graphon.  Three pointwise facts are needed that the earlier rows did not
use.

* `rootedTriangle_le_sq_degree` — `τ ≤ d²`, the upper face `g₈` of the rooted
  feasible polygon.
* `pathOp_sub_le_rootedTriangle` — `τ ≥ a - d + d²`, the slack `g₆`.  It is the
  companion of `Link.rootedTriangle_ge` with the linearisation applied to the
  *other* pair of edges: `W(x,z)W(y,z) ≥ W(x,z) + W(y,z) - 1`, weighted by
  `W(x,y)`.
* `rootedTriangle_mul_le_degree_mul_rootedK4` — `τ(2τ - d²) ≤ d·κ₄`, Goodman
  inside the link.  This is exactly the step inside `K4Tail.mul_rootedK4_ge`,
  isolated here because Atlas 178 needs it *before* the truncation.
-/

open MeasureTheory

namespace Taeyoung.Methods.Atlas178

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link Taeyoung.Methods.K4Tail
  Taeyoung.Methods.CliqueLeaf Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The upper face `τ ≤ d²` -/

/-- `τ(x) ≤ d(x)²`: drop the opposite edge `W(y,z)`. -/
lemma rootedTriangle_le_sq_degree (W : Graphon Ω μ) (x : Ω) :
    rootedTriangle W x ≤ degree W x ^ 2 := by
  have hrowx : Measurable fun b ↦ W x b := measurable_row W.measurable x
  have hinner : ∀ y, (∫ z, W x y * W x z * W y z ∂μ) ≤ W x y * degree W x := by
    intro y
    have hint : Integrable (fun z ↦ W x y * W x z * W y z) μ :=
      integrable_of_bdd
        ((measurable_const.mul hrowx).mul (measurable_row W.measurable y))
        (C := 1) fun z ↦ by
          rw [abs_of_nonneg (mul_nonneg (mul_nonneg (W.nonneg x y)
            (W.nonneg x z)) (W.nonneg y z))]
          exact mul_le_one₀ (mul_le_one₀ (W.le_one x y) (W.nonneg x z)
            (W.le_one x z)) (W.nonneg y z) (W.le_one y z)
    have hint2 : Integrable (fun z ↦ W x y * W x z) μ :=
      integrable_of_bdd (measurable_const.mul hrowx) (C := 1) fun z ↦ by
        rw [abs_of_nonneg (mul_nonneg (W.nonneg x y) (W.nonneg x z))]
        exact mul_le_one₀ (W.le_one x y) (W.nonneg x z) (W.le_one x z)
    calc ∫ z, W x y * W x z * W y z ∂μ ≤ ∫ z, W x y * W x z ∂μ := by
          refine integral_mono hint hint2 fun z ↦ ?_
          have := mul_le_of_le_one_right
            (mul_nonneg (W.nonneg x y) (W.nonneg x z)) (W.le_one y z)
          linarith [this]
      _ = W x y * degree W x := by rw [integral_const_mul]; rfl
  have houter : Integrable (fun y ↦ ∫ z, W x y * W x z * W y z ∂μ) μ := by
    refine integrable_of_bdd ?_ (C := 1) fun y ↦ ?_
    · exact measurable_integral_right
        (((hrowx.comp measurable_fst).mul (hrowx.comp measurable_snd)).mul
          W.measurable)
    · refine abs_integral_le_of_bdd
        ((measurable_const.mul hrowx).mul (measurable_row W.measurable y))
        fun z ↦ ?_
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (W.nonneg x y)
        (W.nonneg x z)) (W.nonneg y z))]
      exact mul_le_one₀ (mul_le_one₀ (W.le_one x y) (W.nonneg x z)
        (W.le_one x z)) (W.nonneg y z) (W.le_one y z)
  have hint3 : Integrable (fun y ↦ W x y * degree W x) μ :=
    (integrable_of_bdd (measurable_row W.measurable x) (C := 1) fun y ↦ by
      rw [abs_of_nonneg (W.nonneg x y)]; exact W.le_one x y).mul_const _
  calc rootedTriangle W x = ∫ y, ∫ z, W x y * W x z * W y z ∂μ ∂μ := rfl
    _ ≤ ∫ y, W x y * degree W x ∂μ := integral_mono houter hint3 hinner
    _ = degree W x ^ 2 := by rw [integral_mul_const]; rw [sq]; rfl

/-! ### The slack `g₆ = τ - a + d - d²` -/

/-- `τ(x) ≥ a(x) - d(x) + d(x)²`, from `W(x,z)W(y,z) ≥ W(x,z) + W(y,z) - 1`
weighted by `W(x,y)`. -/
theorem pathOp_sub_le_rootedTriangle (W : Graphon Ω μ) (x : Ω) :
    pathOp W x - degree W x + degree W x ^ 2 ≤ rootedTriangle W x := by
  have hWm : Measurable (Function.uncurry W.toFun) := W.measurable
  have hrowx : Measurable fun b ↦ W x b := measurable_row W.measurable x
  have hfst : Measurable fun q : Ω × Ω ↦ W x q.1 := hrowx.comp measurable_fst
  have hsnd : Measurable fun q : Ω × Ω ↦ W x q.2 := hrowx.comp measurable_snd
  have hgm : Measurable (Function.uncurry fun y z ↦ W x y * W x z * W y z) :=
    (hfst.mul hsnd).mul hWm
  have hlm : Measurable
      (Function.uncurry fun y z ↦ W x y * (W x z + W y z - 1)) :=
    hfst.mul ((hsnd.add hWm).sub measurable_const)
  have hgb : ∀ y z, |W x y * W x z * W y z| ≤ 1 := by
    intro y z
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (W.nonneg x y) (W.nonneg x z))
      (W.nonneg y z))]
    exact mul_le_one₀ (mul_le_one₀ (W.le_one x y) (W.nonneg x z)
      (W.le_one x z)) (W.nonneg y z) (W.le_one y z)
  have hlb : ∀ y z, |W x y * (W x z + W y z - 1)| ≤ 1 := by
    intro y z
    have h1 := W.nonneg x y; have h2 := W.le_one x y
    have h3 := W.nonneg x z; have h4 := W.le_one x z
    have h5 := W.nonneg y z; have h6 := W.le_one y z
    rw [abs_le]
    constructor <;> nlinarith
  have hpt : ∀ y z, W x y * (W x z + W y z - 1) ≤ W x y * W x z * W y z := by
    intro y z
    have hab : W x z + W y z - 1 ≤ W x z * W y z := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (W.le_one x z))
        (sub_nonneg.mpr (W.le_one y z))]
    have := mul_le_mul_of_nonneg_left hab (W.nonneg x y)
    nlinarith [this]
  -- the linearised double integral is `d² + a - d`
  have hlint : Integrable
      (Function.uncurry fun y z ↦ W x y * (W x z + W y z - 1)) (μ.prod μ) :=
    integrable_uncurry_of_bdd hlm hlb
  have ha : Integrable (fun q : Ω × Ω ↦ W x q.1 * W x q.2) (μ.prod μ) := by
    refine integrable_prod_of_bdd (hfst.mul hsnd) (C := 1) fun q ↦ ?_
    rw [abs_of_nonneg (mul_nonneg (W.nonneg x q.1) (W.nonneg x q.2))]
    exact mul_le_one₀ (W.le_one x q.1) (W.nonneg x q.2) (W.le_one x q.2)
  have hb : Integrable (fun q : Ω × Ω ↦ W x q.1 * W q.1 q.2) (μ.prod μ) := by
    refine integrable_prod_of_bdd (hfst.mul hWm) (C := 1) fun q ↦ ?_
    rw [abs_of_nonneg (mul_nonneg (W.nonneg x q.1) (W.nonneg q.1 q.2))]
    exact mul_le_one₀ (W.le_one x q.1) (W.nonneg q.1 q.2) (W.le_one q.1 q.2)
  have hc : Integrable (fun q : Ω × Ω ↦ W x q.1) (μ.prod μ) := by
    refine integrable_prod_of_bdd hfst (C := 1) fun q ↦ ?_
    rw [abs_of_nonneg (W.nonneg x q.1)]; exact W.le_one x q.1
  have hlin : (∫ y, ∫ z, W x y * (W x z + W y z - 1) ∂μ ∂μ) =
      degree W x ^ 2 + pathOp W x - degree W x := by
    rw [integral_integral hlint]
    have hcongr : ∀ q : Ω × Ω, W x q.1 * (W x q.2 + W q.1 q.2 - 1) =
        W x q.1 * W x q.2 + W x q.1 * W q.1 q.2 - W x q.1 := by
      intro q; ring
    rw [integral_congr_ae (ae_of_all _ hcongr)]
    have e1 := integral_sub (ha.add hb) hc
    have e2 := integral_add ha hb
    simp only [Pi.add_apply] at e1 e2
    rw [e1, e2]
    have hA : (∫ q : Ω × Ω, W x q.1 * W x q.2 ∂(μ.prod μ)) = degree W x ^ 2 := by
      have ha' : Integrable (Function.uncurry fun y z ↦ W x y * W x z)
          (μ.prod μ) := ha
      rw [← integral_integral ha']
      have : (∫ y, ∫ z, W x y * W x z ∂μ ∂μ) = ∫ y, W x y * degree W x ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
        simp only []
        rw [integral_const_mul]; rfl
      rw [this, integral_mul_const, sq]; rfl
    have hB : (∫ q : Ω × Ω, W x q.1 * W q.1 q.2 ∂(μ.prod μ)) = pathOp W x := by
      have hb' : Integrable (Function.uncurry fun y z ↦ W x y * W y z)
          (μ.prod μ) := hb
      rw [← integral_integral hb']
      refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      simp only []
      rw [integral_const_mul]; rfl
    have hC : (∫ _q : Ω × Ω, W x _q.1 ∂(μ.prod μ)) = degree W x := by
      have hc' : Integrable (Function.uncurry fun y _z : Ω ↦ W x y) (μ.prod μ) :=
        hc
      rw [← integral_integral hc']
      refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      simp
    rw [hA, hB, hC]
  have hmono : (∫ y, ∫ z, W x y * (W x z + W y z - 1) ∂μ ∂μ) ≤
      rootedTriangle W x := by
    refine integral_mono (integrable_integral_right hlm hlb)
      (integrable_integral_right hgm hgb) fun y ↦ ?_
    exact integral_mono (integrable_of_bdd (measurable_row hlm y) (hlb y))
      (integrable_of_bdd (measurable_row hgm y) (hgb y)) fun z ↦ hpt y z
  rw [hlin] at hmono
  linarith [hmono]

/-! ### Goodman inside the link, untruncated -/

/-- `τ(x)·(2τ(x) - d(x)²) ≤ d(x)·κ₄(x)`.  Goodman applied to the link graphon
at `x`, scaled back by `d(x)⁴`; the degenerate case `d(x) = 0` is settled by
`τ ≤ d²`. -/
theorem rootedTriangle_mul_le_degree_mul_rootedK4 (W : Graphon Ω μ) (x : Ω) :
    rootedTriangle W x * (2 * rootedTriangle W x - degree W x ^ 2) ≤
      degree W x * rootedK4 W x := by
  rcases eq_or_lt_of_le (degree_nonneg W x) with hd0 | hdpos
  · have hdz : degree W x = 0 := hd0.symm
    have hτ : rootedTriangle W x = 0 :=
      le_antisymm (by
        have := rootedTriangle_le_sq_degree W x
        rw [hdz] at this; simpa using this) (rootedTriangle_nonneg W x)
    rw [hdz, hτ]; simp
  · haveI := isProbabilityMeasure_linkMeasure W hdpos
    have hτ : degree W x ^ 2 * cliqueDensity 2 (linkGraphon W x) =
        rootedTriangle W x := by
      rw [← rootedDensity_top_two W x, cliqueDensity,
        rootedDensity_eq (⊤ : SimpleGraph (Fin 2)) W hdpos]
    have hκ : rootedK4 W x =
        degree W x ^ 3 * cliqueDensity 3 (linkGraphon W x) := by
      rw [rootedK4, cliqueDensity, rootedDensity_eq _ W hdpos]
    have hgood := goodman (linkGraphon W x)
    have hpow : (0 : ℝ) ≤ degree W x ^ 4 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hgood hpow
    have heq : rootedTriangle W x * (2 * rootedTriangle W x - degree W x ^ 2) =
        degree W x ^ 4 * (cliqueDensity 2 (linkGraphon W x) *
          (2 * cliqueDensity 2 (linkGraphon W x) - 1)) := by
      rw [← hτ]; ring
    have heq2 : degree W x * rootedK4 W x =
        degree W x ^ 4 * cliqueDensity 3 (linkGraphon W x) := by
      rw [hκ]; ring
    rw [heq, heq2]
    exact hmul

end Taeyoung.Methods.Atlas178
