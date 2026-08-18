import Taeyoung.Methods.PagePawBranch.Core
import Taeyoung.Methods.PageBook.Atlas41

/-!
# The two scoped page-paw branch rows

`B_2^{new}` (Atlas 139) and `B_2^{page}` (Atlas 137): a two-page triangle book
on the spine `a,b`, with a triangle glued along the page edge `a z₁` at a new
vertex `u`, and one leaf — at `u` for `B_2^{new}`, at `z₁` for `B_2^{page}`.

Both are labelled here so that peeling reads off the shared shape

```
t = ∫∫ W(a,b)·H₀(a,b)·Λ_h(a,b),
```

with spine `0,1`, exceptional page `2`, ordinary page `3`, glued vertex `4` and
leaf `5`.  The two branch weights are

* `h(x,z) = H₁(x,z)` for `B_2^{new}` — the leaf sits on the glued vertex, so
  the vertex integrates to a degree factor inside the page operator;
* `h(x,z) = d(z)·H₀(x,z)` for `B_2^{page}` — the leaf sits on the page itself.

`Core.branch_bound` then finishes both, given the pointwise compression
`F√F ≤ √h·H₀` for a comparison kernel `F` with `∫∫W·F = ∫d^{1/3}τ`.  For
`B_2^{new}` that compression is `PageOp.cube_pageOp_le`; for `B_2^{page}` it is
an identity, both sides being `d(z)^{1/2}H₀(x,z)^{3/2}`.

Both graphs have `χ_H(x) = x(x-1)²(x-2)³` and hence the target `p²(2p-1)³`,
the same as `PageBook.Atlas138`, and the same three-step attachment tower over
`K₃` produces it.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.PagePawBranch

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PawCone Taeyoung.Methods.ForestCone
  Taeyoung.Methods.BaseCone Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Folding the peeled integrals back into `branchOp` -/

lemma branchOp_pageOp (W : Graphon Ω μ) (s : ℝ) (x y : Ω) :
    (∫ z, W x z * W y z * pageOp W s x z ∂μ)
      = branchOp W (fun a b ↦ pageOp W s a b) x y := rfl

lemma branchOp_degree_pageOp (W : Graphon Ω μ) (x y : Ω) :
    (∫ z, W x z * W y z * (degree W z * pageOp W 0 x z) ∂μ)
      = branchOp W (fun a b ↦ degree W b * pageOp W 0 a b) x y := rfl

lemma eq_of_sq_eq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ^ 2 = b ^ 2) : a = b :=
  le_antisymm (le_of_pow_le_pow_left₀ two_ne_zero hb hab.le)
    (le_of_pow_le_pow_left₀ two_ne_zero ha hab.ge)

/-! ### The two pointwise compressions -/

/-- `B_2^{new}`: the comparison kernel is `H_{1/3}`, and the compression is the
three-page Hölder `H_{1/3}³ ≤ H₀²H₁` of `PageOp.cube_pageOp_le`. -/
lemma key_new (W : Graphon Ω μ) (x z : Ω) :
    pageOp W (1 / 3) x z * Real.sqrt (pageOp W (1 / 3) x z)
      ≤ Real.sqrt (pageOp W 1 x z) * pageOp W 0 x z := by
  have hF : 0 ≤ pageOp W (1 / 3) x z := pageOp_nonneg W (by norm_num) x z
  have h1 : 0 ≤ pageOp W 1 x z := pageOp_nonneg W zero_le_one x z
  have h0 : 0 ≤ pageOp W 0 x z := pageOp_nonneg W le_rfl x z
  refine le_of_pow_le_pow_left₀ (n := 2) two_ne_zero
    (mul_nonneg (Real.sqrt_nonneg _) h0) ?_
  have e1 : (pageOp W (1 / 3) x z * Real.sqrt (pageOp W (1 / 3) x z)) ^ 2
      = pageOp W (1 / 3) x z ^ 3 := by
    rw [mul_pow, Real.sq_sqrt hF]; ring
  have e2 : (Real.sqrt (pageOp W 1 x z) * pageOp W 0 x z) ^ 2
      = pageOp W 0 x z ^ 2 * pageOp W 1 x z := by
    rw [mul_pow, Real.sq_sqrt h1]; ring
  rw [e1, e2]
  exact cube_pageOp_le W x z

/-- `B_2^{page}`: the comparison kernel is `d(z)^{1/3}H₀(x,z)`, and the
compression is an identity — both sides are `d(z)^{1/2}H₀(x,z)^{3/2}`. -/
lemma key_page (W : Graphon Ω μ) (x z : Ω) :
    degree W z ^ ((1 : ℝ) / 3) * pageOp W 0 x z *
        Real.sqrt (degree W z ^ ((1 : ℝ) / 3) * pageOp W 0 x z)
      = Real.sqrt (degree W z * pageOp W 0 x z) * pageOp W 0 x z := by
  have hd : 0 ≤ degree W z := degree_nonneg W z
  have h0 : 0 ≤ pageOp W 0 x z := pageOp_nonneg W le_rfl x z
  have hr : 0 ≤ degree W z ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hd _
  have hA : 0 ≤ degree W z ^ ((1 : ℝ) / 3) * pageOp W 0 x z := mul_nonneg hr h0
  have hcube : (degree W z ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = degree W z := by
    rw [← Real.rpow_natCast (degree W z ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hd,
      show (1 : ℝ) / 3 * (3 : ℕ) = 1 by norm_num, Real.rpow_one]
  refine eq_of_sq_eq_of_nonneg (mul_nonneg hA (Real.sqrt_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) h0) ?_
  have e1 : (degree W z ^ ((1 : ℝ) / 3) * pageOp W 0 x z *
      Real.sqrt (degree W z ^ ((1 : ℝ) / 3) * pageOp W 0 x z)) ^ 2
      = degree W z * pageOp W 0 x z ^ 3 := by
    rw [mul_pow, Real.sq_sqrt hA]
    calc (degree W z ^ ((1 : ℝ) / 3) * pageOp W 0 x z) ^ 2 *
          (degree W z ^ ((1 : ℝ) / 3) * pageOp W 0 x z)
        = (degree W z ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) * pageOp W 0 x z ^ 3 := by ring
      _ = degree W z * pageOp W 0 x z ^ 3 := by rw [hcube]
  have e2 : (Real.sqrt (degree W z * pageOp W 0 x z) * pageOp W 0 x z) ^ 2
      = degree W z * pageOp W 0 x z ^ 3 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hd h0)]; ring
  rw [e1, e2]

/-! ### The graph `B_2^{new}`, Atlas 139 -/

/-- Spine `0,1`; exceptional page `2`; ordinary page `3`; the glued vertex `4`
on the page edge `0-2`; the leaf `5` at the glued vertex. -/
def bookNew : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 4), (4, 5)]

instance : DecidableRel bookNew.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_bookNew :
    bookNew.edgeFinset =
      {s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(1, 2), s(1, 3), s(2, 4), s(4, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_bookNew (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight bookNew W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 0) (x 3) * W (x 0) (x 4) *
        W (x 1) (x 2) * W (x 1) (x 3) * W (x 2) (x 4) * W (x 4) (x 5) := by
  rw [graphWeight, edgeFinset_bookNew]
  simp
  ring

lemma graphWeight_bookNew_cons (W : Graphon Ω μ) (a0 a1 a2 a3 a4 a5 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight bookNew W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
        (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y)))))) =
      W a0 a1 * W a0 a2 * W a0 a3 * W a0 a4 * W a1 a2 * W a1 a3 * W a2 a4 *
        W a4 a5 := by
  rw [graphWeight_bookNew]
  rfl

/-- **The density of `B_2^{new}` factors through the branch operator.** -/
theorem homDensity_bookNew (W : Graphon Ω μ) :
    homDensity bookNew W =
      ∫ a0, ∫ a1, W a0 a1 * pageOp W 0 a0 a1 *
        branchOp W (fun a b ↦ pageOp W 1 a b) a0 a1 ∂μ ∂μ := by
  have hm : Measurable (graphWeight bookNew W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight bookNew W x| ≤ 1 := fun x ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 5 → Ω ↦ graphWeight bookNew W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω ↦ graphWeight bookNew W (Fin.cons a0 (Fin.cons a1 y)))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  have hstep2 : ∀ a2 : Ω,
      (∫ y : Fin 3 → Ω,
          graphWeight bookNew W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)))
        ∂assignmentMeasure (Fin 3) μ) =
        (W a0 a1 * pageOp W 0 a0 a1) *
          (W a0 a2 * W a1 a2 * pageOp W 1 a0 a2) := by
    intro a2
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 3 → Ω ↦
        graphWeight bookNew W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
      (hm.comp ((measurable_fin_cons a0).comp
        ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
      fun y ↦ hb _]
    have hstep3 : ∀ a3 : Ω,
        (∫ y : Fin 2 → Ω,
            graphWeight bookNew W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
          ∂assignmentMeasure (Fin 2) μ) =
          (W a0 a1 * W a0 a2 * W a1 a2 * pageOp W 1 a0 a2) *
            (W a0 a3 * W a1 a3 * degree W a3 ^ (0 : ℝ)) := by
      intro a3
      rw [integral_assignmentMeasure_succ
        (fun y : Fin 2 → Ω ↦ graphWeight bookNew W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
        (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
          ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
        fun y ↦ hb _]
      have hstep4 : ∀ a4 : Ω,
          (∫ y : Fin 1 → Ω,
              graphWeight bookNew W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
                (Fin.cons a3 (Fin.cons a4 y)))))
            ∂assignmentMeasure (Fin 1) μ) =
            (W a0 a1 * W a0 a2 * W a1 a2 * (W a0 a3 * W a1 a3)) *
              (W a0 a4 * W a2 a4 * degree W a4 ^ (1 : ℝ)) := by
        intro a4
        rw [integral_assignmentMeasure_succ
          (fun y : Fin 1 → Ω ↦ graphWeight bookNew W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
              (Fin.cons a3 (Fin.cons a4 y))))))
          (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
            ((measurable_fin_cons a2).comp ((measurable_fin_cons a3).comp
              (measurable_fin_cons a4))))))
          fun y ↦ hb _]
        have hval : ∀ a5 : Ω,
            (∫ y : Fin 0 → Ω, graphWeight bookNew W
                (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                  (Fin.cons a4 (Fin.cons a5 y))))))
              ∂assignmentMeasure (Fin 0) μ) =
              ((W a0 a1 * W a0 a2 * W a1 a2 * (W a0 a3 * W a1 a3)) *
                (W a0 a4 * W a2 a4)) * W a4 a5 := by
          intro a5
          rw [show (∫ y : Fin 0 → Ω, graphWeight bookNew W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                (Fin.cons a4 (Fin.cons a5 y))))))
                ∂assignmentMeasure (Fin 0) μ) =
              W a0 a1 * W a0 a2 * W a0 a3 * W a0 a4 * W a1 a2 * W a1 a3 *
                W a2 a4 * W a4 a5 by simp [graphWeight_bookNew_cons]]
          ring
        rw [integral_congr_ae (ae_of_all _ hval), integral_const_mul,
          Real.rpow_one]
        show _ * degree W a4 = _
        ring
      rw [integral_congr_ae (ae_of_all _ hstep4), integral_const_mul, ← pageOp,
        Real.rpow_zero]
      ring
    rw [integral_congr_ae (ae_of_all _ hstep3), integral_const_mul, ← pageOp]
    ring
  rw [integral_congr_ae (ae_of_all _ hstep2), integral_const_mul,
    branchOp_pageOp W 1 a0 a1]

/-! ### The graph `B_2^{page}`, Atlas 137 -/

/-- The same book, with the leaf `5` moved from the glued vertex `4` to the
exceptional page `2`. -/
def bookPage : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 4), (2, 5)]

instance : DecidableRel bookPage.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_bookPage :
    bookPage.edgeFinset =
      {s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(1, 2), s(1, 3), s(2, 4), s(2, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_bookPage (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight bookPage W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 0) (x 3) * W (x 0) (x 4) *
        W (x 1) (x 2) * W (x 1) (x 3) * W (x 2) (x 4) * W (x 2) (x 5) := by
  rw [graphWeight, edgeFinset_bookPage]
  simp
  ring

lemma graphWeight_bookPage_cons (W : Graphon Ω μ) (a0 a1 a2 a3 a4 a5 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight bookPage W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
        (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y)))))) =
      W a0 a1 * W a0 a2 * W a0 a3 * W a0 a4 * W a1 a2 * W a1 a3 * W a2 a4 *
        W a2 a5 := by
  rw [graphWeight_bookPage]
  rfl

/-- **The density of `B_2^{page}` factors through the branch operator.** -/
theorem homDensity_bookPage (W : Graphon Ω μ) :
    homDensity bookPage W =
      ∫ a0, ∫ a1, W a0 a1 * pageOp W 0 a0 a1 *
        branchOp W (fun a b ↦ degree W b * pageOp W 0 a b) a0 a1 ∂μ ∂μ := by
  have hm : Measurable (graphWeight bookPage W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight bookPage W x| ≤ 1 := fun x ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 5 → Ω ↦ graphWeight bookPage W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω ↦ graphWeight bookPage W (Fin.cons a0 (Fin.cons a1 y)))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  have hstep2 : ∀ a2 : Ω,
      (∫ y : Fin 3 → Ω,
          graphWeight bookPage W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)))
        ∂assignmentMeasure (Fin 3) μ) =
        (W a0 a1 * pageOp W 0 a0 a1) *
          (W a0 a2 * W a1 a2 * (degree W a2 * pageOp W 0 a0 a2)) := by
    intro a2
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 3 → Ω ↦
        graphWeight bookPage W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
      (hm.comp ((measurable_fin_cons a0).comp
        ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
      fun y ↦ hb _]
    have hstep3 : ∀ a3 : Ω,
        (∫ y : Fin 2 → Ω,
            graphWeight bookPage W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
          ∂assignmentMeasure (Fin 2) μ) =
          (W a0 a1 * W a0 a2 * W a1 a2 *
              (degree W a2 * pageOp W 0 a0 a2)) *
            (W a0 a3 * W a1 a3 * degree W a3 ^ (0 : ℝ)) := by
      intro a3
      rw [integral_assignmentMeasure_succ
        (fun y : Fin 2 → Ω ↦ graphWeight bookPage W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
        (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
          ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
        fun y ↦ hb _]
      have hstep4 : ∀ a4 : Ω,
          (∫ y : Fin 1 → Ω,
              graphWeight bookPage W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
                (Fin.cons a3 (Fin.cons a4 y)))))
            ∂assignmentMeasure (Fin 1) μ) =
            (W a0 a1 * W a0 a2 * W a1 a2 * (W a0 a3 * W a1 a3) *
                degree W a2) *
              (W a0 a4 * W a2 a4 * degree W a4 ^ (0 : ℝ)) := by
        intro a4
        rw [integral_assignmentMeasure_succ
          (fun y : Fin 1 → Ω ↦ graphWeight bookPage W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
              (Fin.cons a3 (Fin.cons a4 y))))))
          (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
            ((measurable_fin_cons a2).comp ((measurable_fin_cons a3).comp
              (measurable_fin_cons a4))))))
          fun y ↦ hb _]
        have hval : ∀ a5 : Ω,
            (∫ y : Fin 0 → Ω, graphWeight bookPage W
                (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                  (Fin.cons a4 (Fin.cons a5 y))))))
              ∂assignmentMeasure (Fin 0) μ) =
              ((W a0 a1 * W a0 a2 * W a1 a2 * (W a0 a3 * W a1 a3)) *
                (W a0 a4 * W a2 a4)) * W a2 a5 := by
          intro a5
          rw [show (∫ y : Fin 0 → Ω, graphWeight bookPage W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                (Fin.cons a4 (Fin.cons a5 y))))))
                ∂assignmentMeasure (Fin 0) μ) =
              W a0 a1 * W a0 a2 * W a0 a3 * W a0 a4 * W a1 a2 * W a1 a3 *
                W a2 a4 * W a2 a5 by simp [graphWeight_bookPage_cons]]
          ring
        rw [integral_congr_ae (ae_of_all _ hval), integral_const_mul,
          Real.rpow_zero]
        show _ * degree W a2 = _
        ring
      rw [integral_congr_ae (ae_of_all _ hstep4), integral_const_mul, ← pageOp,
        Real.rpow_zero]
      ring
    rw [integral_congr_ae (ae_of_all _ hstep3), integral_const_mul, ← pageOp]
    ring
  rw [integral_congr_ae (ae_of_all _ hstep2), integral_const_mul,
    branchOp_degree_pageOp W a0 a1]

/-! ### The two bounds -/

/-- The peeled density, as an integral over the product measure. -/
lemma integral_prod_of_branch (W : Graphon Ω μ) {h : Ω → Ω → ℝ}
    (hm : Measurable (Function.uncurry h)) (h0 : ∀ x y, 0 ≤ h x y)
    (h1 : ∀ x y, h x y ≤ 1) :
    (∫ a0, ∫ a1, W a0 a1 * pageOp W 0 a0 a1 * branchOp W h a0 a1 ∂μ ∂μ) =
      ∫ q, W q.1 q.2 * pageOp W 0 q.1 q.2 * branchOp W h q.1 q.2 ∂(μ.prod μ) := by
  refine integral_integral ?_
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

/-- **`B_2^{new}` dominates its target.** -/
theorem bookNew_bound (W : Graphon Ω μ) (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 2 * (2 * cliqueDensity 2 W - 1) ^ 3 ≤
      homDensity bookNew W := by
  have hm : Measurable (Function.uncurry fun a b : Ω ↦ pageOp W 1 a b) :=
    measurable_pageOp W zero_le_one
  have hFm : Measurable (Function.uncurry fun a b : Ω ↦ pageOp W (1 / 3) a b) :=
    measurable_pageOp W (by norm_num)
  have hbase : cliqueDensity 2 W ^ ((4 : ℝ) / 3) * (2 * cliqueDensity 2 W - 1)
      ≤ ∫ q, W q.1 q.2 * pageOp W (1 / 3) q.1 q.2 ∂(μ.prod μ) := by
    rw [integral_edge_pageOp W (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    exact rpow_mul_le_integral_third W hp
  rw [homDensity_bookNew, integral_prod_of_branch W hm
    (fun x y ↦ pageOp_nonneg W zero_le_one x y)
    fun x y ↦ pageOp_le_one W zero_le_one x y]
  exact branch_bound W hp hm (fun x y ↦ pageOp_nonneg W zero_le_one x y)
    (fun x y ↦ pageOp_le_one W zero_le_one x y) hFm
    (fun x y ↦ pageOp_nonneg W (by norm_num) x y)
    (fun x y ↦ pageOp_le_one W (by norm_num) x y) (key_new W) hbase

/-- **`B_2^{page}` dominates its target.** -/
theorem bookPage_bound (W : Graphon Ω μ) (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 2 * (2 * cliqueDensity 2 W - 1) ^ 3 ≤
      homDensity bookPage W := by
  have hm : Measurable (Function.uncurry
      fun a b : Ω ↦ degree W b * pageOp W 0 a b) :=
    ((measurable_degree W).comp measurable_snd).mul (measurable_pageOp W le_rfl)
  have h0 : ∀ x y : Ω, 0 ≤ degree W y * pageOp W 0 x y := fun x y ↦
    mul_nonneg (degree_nonneg W y) (pageOp_nonneg W le_rfl x y)
  have h1 : ∀ x y : Ω, degree W y * pageOp W 0 x y ≤ 1 := fun x y ↦
    mul_le_one₀ (degree_le_one W y) (pageOp_nonneg W le_rfl x y)
      (pageOp_le_one W le_rfl x y)
  have hFm : Measurable (Function.uncurry
      fun a b : Ω ↦ degree W b ^ ((1 : ℝ) / 3) * pageOp W 0 a b) :=
    ((measurable_degree_rpow W (by norm_num)).comp measurable_snd).mul
      (measurable_pageOp W le_rfl)
  have hF0 : ∀ x y : Ω, 0 ≤ degree W y ^ ((1 : ℝ) / 3) * pageOp W 0 x y := fun x y ↦
    mul_nonneg (degree_rpow_nonneg W _ y) (pageOp_nonneg W le_rfl x y)
  have hF1 : ∀ x y : Ω, degree W y ^ ((1 : ℝ) / 3) * pageOp W 0 x y ≤ 1 := fun x y ↦
    mul_le_one₀ (degree_rpow_le_one W (by norm_num) y) (pageOp_nonneg W le_rfl x y)
      (pageOp_le_one W le_rfl x y)
  have hbase : cliqueDensity 2 W ^ ((4 : ℝ) / 3) * (2 * cliqueDensity 2 W - 1)
      ≤ ∫ q, W q.1 q.2 *
          (degree W q.2 ^ ((1 : ℝ) / 3) * pageOp W 0 q.1 q.2) ∂(μ.prod μ) := by
    rw [integral_edge_degree_pageOp W (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    exact rpow_mul_le_integral_third W hp
  rw [homDensity_bookPage, integral_prod_of_branch W hm h0 h1]
  exact branch_bound W hp hm h0 h1 hFm hF0 hF1
    (fun x z ↦ (key_page W x z).le) hbase

/-! ### Chromatic data -/

lemma affineProd_pagePaw (z : ℝ) :
    affineProd [0, 1, 1, 2, 2, 2] z = z ^ 2 * (2 * z - 1) ^ 3 := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_cons, affineProd_nil]
  ring

/-- The attachment tower shared by the two rows, up to the last clique. -/
abbrev towerBase : SimpleGraph (Option (Option (Fin 3))) :=
  attachVertex (attachVertex (⊤ : SimpleGraph (Fin 3)) {0, 1}) {some 0, some 2}

def isoNew : attachVertex towerBase {none} ≃g bookNew where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

def isoPage : attachVertex towerBase {some (some 2)} ≃g bookPage where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

lemma towerBase_chrom : IsChromaticPolynomial towerBase
    ((X - C ((2 : ℕ) : ℝ)) * ((X - C ((2 : ℕ) : ℝ)) *
      ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ)))) := by
  have h := isChromaticPolynomial_attachVertex
    (isClique_attach_pair {0, 1} (by decide : (0 : Fin 3) ≠ 2))
    (isChromaticPolynomial_attachVertex (isCliqueTop _)
      (isChromaticPolynomial_top 3))
  rwa [show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide,
    show (({some 0, some 2} : Finset (Option (Fin 3))).card) = 2 from by decide] at h

lemma towerBase_count (k : ℕ) :
    properAssignmentCount towerBase k = (k - 2) * ((k - 2) * k.descFactorial 3) := by
  rw [properAssignmentCount_attachVertex
      (isClique_attach_pair {0, 1} (by decide : (0 : Fin 3) ≠ 2)),
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide,
    show (({some 0, some 2} : Finset (Option (Fin 3))).card) = 2 from by decide]

lemma hpoly_pagePaw :
    ((([0, 1, 1, 2, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) * ((X - C ((2 : ℕ) : ℝ)) *
        ((X - C ((2 : ℕ) : ℝ)) * ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ)))) := by
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
  ring

theorem chromNew : IsChromaticPolynomial bookNew
    ((([0, 1, 1, 2, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := bookNew) isoNew
    (isClique_singleton _ none) towerBase_chrom
  rw [Finset.card_singleton] at h
  rw [hpoly_pagePaw]
  exact h

theorem chromPage : IsChromaticPolynomial bookPage
    ((([0, 1, 1, 2, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := bookPage) isoPage
    (isClique_singleton _ (some (some 2))) towerBase_chrom
  rw [Finset.card_singleton] at h
  rw [hpoly_pagePaw]
  exact h

theorem countNew (k : ℕ) :
    properAssignmentCount bookNew k =
      (k - 1) * ((k - 2) * ((k - 2) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := bookNew) isoNew
      (isClique_singleton _ none) k, Finset.card_singleton, towerBase_count]

theorem countPage (k : ℕ) :
    properAssignmentCount bookPage k =
      (k - 1) * ((k - 2) * ((k - 2) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := bookPage) isoPage
      (isClique_singleton _ (some (some 2))) k, Finset.card_singleton,
    towerBase_count]

theorem numNew : IsChromaticNumber bookNew 3 where
  positive := by rw [countNew]; decide
  zero_below k hk := by
    rw [countNew, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero, Nat.mul_zero]

theorem numPage : IsChromaticNumber bookPage 3 where
  positive := by rw [countPage]; decide
  zero_below k hk := by
    rw [countPage, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero, Nat.mul_zero]

/-! ### The catalogue propositions -/

/-- **`B_2^{new}` (Atlas 139) satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_bookNew : Taeyoung.SatisfiesLowerBound bookNew := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = (([0, 1, 1, 2, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := bookNew) hP chromNew
  have hreq : r = 3 := IsChromaticNumber.unique (H := bookNew) hr numNew
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := bookNew_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 2, 2, 2] (by norm_num) hone,
      affineProd_pagePaw]
    exact hkey

/-- **`B_2^{page}` (Atlas 137) satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_bookPage : Taeyoung.SatisfiesLowerBound bookPage := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = (([0, 1, 1, 2, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := bookPage) hP chromPage
  have hreq : r = 3 := IsChromaticNumber.unique (H := bookPage) hr numPage
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := bookPage_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 2, 2, 2] (by norm_num) hone,
      affineProd_pagePaw]
    exact hkey

end Taeyoung.Methods.PagePawBranch
