import Taeyoung.Methods.Atlas160.Link
import Taeyoung.Methods.AffineProduct
import Taeyoung.Methods.K4Tail.Rows

/-!
# Atlas 160: the page reduction and the row

`notes/atlas160_k4_paw_edge_supporting_plane.tex` §1 and §4.

The graph is a `K₄` on `0,1,2,3` carrying a page vertex `4` on the clique edge
`01`, with a pendant leaf `5` on the page.  Integrating the leaf and then the
page leaves the two-variable weight

```
B(x,y) = ∫ W(x,z)W(y,z)d(z) dμ(z),
```

and `rs ≥ r + s - 1` gives `B(x,y) ≥ A(x) + A(y) - p` pointwise.  The page
reduction is that inequality integrated against the `K₄` weight.

**The comparison is arranged so that only two coordinates ever move.**  After
peeling `a₀` and `a₁` the remaining clique integral is the pair weight

```
pairK(x,y) = ∫∫ W(x,y)W(x,a₂)W(x,a₃)W(y,a₂)W(y,a₃)W(a₂,a₃),
```

a nonnegative factor that the tail never touches.  Every density in the
reduction is `∫∫ pairK · (something)`, so the monotonicity step is a two-level
`integral_mono` and the splitting step a two-level `integral_add`; no four-fold
nesting occurs.

The two tail placements — the path at `0` and the path at `1` — are the same
graph up to the transposition `0 ↔ 1`, so `Foundation.homDensity_iso` identifies
their densities and the reduction closes on `∫ (2A - p)·κ₄`, which is where
`Atlas160/Link.lean` takes over.
-/

open MeasureTheory

namespace Taeyoung.Methods.Atlas160

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link Taeyoung.Methods.K4Tail
  Taeyoung.Methods.BookTail Taeyoung.Methods.PawCone
  Taeyoung.Methods.BaseCone Taeyoung.Methods.CliqueLeaf
open Finset Polynomial

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The page weight -/

/-- `B(x,y) = ∫ W(x,z)W(y,z)d(z)`, the leaf-and-page factor. -/
noncomputable def pageB (W : Graphon Ω μ) (x y : Ω) : ℝ :=
  ∫ z, W x z * W y z * degree W z ∂μ

lemma pageB_nonneg (W : Graphon Ω μ) (x y : Ω) : 0 ≤ pageB W x y :=
  integral_nonneg fun z ↦ by
    have := W.nonneg x z; have := W.nonneg y z; have := degree_nonneg W z
    positivity

lemma pageB_le_one (W : Graphon Ω μ) (x y : Ω) : pageB W x y ≤ 1 := by
  have hint : Integrable (fun z ↦ W x z * W y z * degree W z) μ :=
    integrable_of_bdd (((measurable_row W.measurable x).mul
      (measurable_row W.measurable y)).mul (measurable_degree W)) (C := 1)
      fun z ↦ by
        rw [abs_of_nonneg (by
          have := W.nonneg x z; have := W.nonneg y z
          have := degree_nonneg W z; positivity)]
        exact mul_le_one₀ (mul_le_one₀ (W.le_one x z) (W.nonneg y z)
          (W.le_one y z)) (degree_nonneg W z) (degree_le_one W z)
  calc pageB W x y ≤ ∫ _z : Ω, (1 : ℝ) ∂μ := by
        refine integral_mono hint (integrable_const _) fun z ↦ ?_
        exact mul_le_one₀ (mul_le_one₀ (W.le_one x z) (W.nonneg y z)
          (W.le_one y z)) (degree_nonneg W z) (degree_le_one W z)
    _ = 1 := by simp

lemma measurable_pageB (W : Graphon Ω μ) :
    Measurable (Function.uncurry (pageB W)) := by
  have h : StronglyMeasurable (Function.uncurry fun q : Ω × Ω ↦ fun z ↦
      W q.1 z * W q.2 z * degree W z) := by
    refine (?_ : Measurable _).stronglyMeasurable
    exact ((W.measurable.comp ((measurable_fst.comp measurable_fst).prodMk
      measurable_snd)).mul (W.measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).mul
      ((measurable_degree W).comp measurable_snd)
  exact (h.integral_prod_right' (ν := μ)).measurable

/-- **The page bound.**  `rs ≥ r + s - 1` applied to `W(x,z)` and `W(y,z)`,
weighted by `d(z) ≥ 0`. -/
theorem pathOp_add_sub_le_pageB (W : Graphon Ω μ) (x y : Ω) :
    pathOp W x + pathOp W y - cliqueDensity 2 W ≤ pageB W x y := by
  have e1 : Integrable (fun z ↦ W x z * degree W z + W y z * degree W z) μ :=
    ((integrable_row_mul_degree W x).add
      (integrable_row_mul_degree W y)).congr (ae_of_all _ fun _ ↦ rfl)
  have hi1 : Integrable (fun z ↦ W x z * degree W z + W y z * degree W z -
      degree W z) μ :=
    (e1.sub (integrable_degree W)).congr (ae_of_all _ fun _ ↦ rfl)
  have hi2 : Integrable (fun z ↦ W x z * W y z * degree W z) μ :=
    integrable_of_bdd (((measurable_row W.measurable x).mul
      (measurable_row W.measurable y)).mul (measurable_degree W)) (C := 1)
      fun z ↦ by
        rw [abs_of_nonneg (by
          have := W.nonneg x z; have := W.nonneg y z
          have := degree_nonneg W z; positivity)]
        exact mul_le_one₀ (mul_le_one₀ (W.le_one x z) (W.nonneg y z)
          (W.le_one y z)) (degree_nonneg W z) (degree_le_one W z)
  have hmono : (∫ z, (W x z * degree W z + W y z * degree W z - degree W z) ∂μ) ≤
      pageB W x y := by
    refine integral_mono hi1 hi2 fun z ↦ ?_
    show W x z * degree W z + W y z * degree W z - degree W z ≤
      W x z * W y z * degree W z
    have hprod : 0 ≤ degree W z * ((1 - W x z) * (1 - W y z)) :=
      mul_nonneg (degree_nonneg W z)
        (mul_nonneg (by linarith [W.le_one x z]) (by linarith [W.le_one y z]))
    nlinarith [hprod]
  have hval : (∫ z, (W x z * degree W z + W y z * degree W z - degree W z) ∂μ) =
      pathOp W x + pathOp W y - cliqueDensity 2 W := by
    rw [integral_sub e1 (integrable_degree W),
      integral_add (integrable_row_mul_degree W x)
        (integrable_row_mul_degree W y), integral_degree W]
    rfl
  rw [hval] at hmono
  exact hmono

/-! ### The pair weight -/

/-- `pairK(x,y)`, the `K₄` weight with the two page-bearing coordinates fixed. -/
noncomputable def pairK (W : Graphon Ω μ) (x y : Ω) : ℝ :=
  ∫ a2, ∫ a3, W x y * W x a2 * W x a3 * (W y a2 * W y a3 * W a2 a3) ∂μ ∂μ

lemma pairK_nonneg (W : Graphon Ω μ) (x y : Ω) : 0 ≤ pairK W x y :=
  integral_nonneg fun a2 ↦ integral_nonneg fun a3 ↦ by
    have := W.nonneg x y; have := W.nonneg x a2; have := W.nonneg x a3
    have := W.nonneg y a2; have := W.nonneg y a3; have := W.nonneg a2 a3
    positivity

lemma pairK_le_one (W : Graphon Ω μ) (x y : Ω) : pairK W x y ≤ 1 := by
  have hb : ∀ a2 a3 : Ω,
      W x y * W x a2 * W x a3 * (W y a2 * W y a3 * W a2 a3) ≤ 1 := by
    intro a2 a3
    refine mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (W.le_one x y) (W.nonneg x a2)
      (W.le_one x a2)) (W.nonneg x a3) (W.le_one x a3)) ?_ ?_
    · have := W.nonneg y a2; have := W.nonneg y a3; have := W.nonneg a2 a3
      positivity
    · exact mul_le_one₀ (mul_le_one₀ (W.le_one y a2) (W.nonneg y a3)
        (W.le_one y a3)) (W.nonneg a2 a3) (W.le_one a2 a3)
  have hinner : ∀ a2 : Ω,
      (∫ a3, W x y * W x a2 * W x a3 * (W y a2 * W y a3 * W a2 a3) ∂μ) ≤ 1 := by
    intro a2
    have hint : Integrable (fun a3 ↦ W x y * W x a2 * W x a3 *
        (W y a2 * W y a3 * W a2 a3)) μ :=
      integrable_of_bdd ((((measurable_const.mul measurable_const).mul
        (measurable_row W.measurable x)).mul ((measurable_const.mul
        (measurable_row W.measurable y)).mul
        (measurable_row W.measurable a2)))) (C := 1) fun a3 ↦ by
          rw [abs_of_nonneg (by
            have := W.nonneg x y; have := W.nonneg x a2; have := W.nonneg x a3
            have := W.nonneg y a2; have := W.nonneg y a3
            have := W.nonneg a2 a3; positivity)]
          exact hb a2 a3
    calc (∫ a3, W x y * W x a2 * W x a3 * (W y a2 * W y a3 * W a2 a3) ∂μ)
        ≤ ∫ _a3 : Ω, (1 : ℝ) ∂μ :=
          integral_mono hint (integrable_const _) fun a3 ↦ hb a2 a3
      _ = 1 := by simp
  have hint2 : Integrable (fun a2 ↦ ∫ a3, W x y * W x a2 * W x a3 *
      (W y a2 * W y a3 * W a2 a3) ∂μ) μ := by
    refine integrable_of_bdd ?_ (C := 1) fun a2 ↦ ?_
    · have h : StronglyMeasurable (Function.uncurry fun a2 a3 : Ω ↦
          W x y * W x a2 * W x a3 * (W y a2 * W y a3 * W a2 a3)) := by
        refine (?_ : Measurable _).stronglyMeasurable
        refine Measurable.mul ?_ ?_
        · exact (measurable_const.mul
            ((measurable_row W.measurable x).comp measurable_fst)).mul
            ((measurable_row W.measurable x).comp measurable_snd)
        · exact (((measurable_row W.measurable y).comp measurable_fst).mul
            ((measurable_row W.measurable y).comp measurable_snd)).mul
            (W.measurable.comp (measurable_fst.prodMk measurable_snd))
      exact (h.integral_prod_right' (ν := μ)).measurable
    · rw [abs_of_nonneg (integral_nonneg fun a3 ↦ by
        have := W.nonneg x y; have := W.nonneg x a2; have := W.nonneg x a3
        have := W.nonneg y a2; have := W.nonneg y a3; have := W.nonneg a2 a3
        positivity)]
      exact hinner a2
  calc pairK W x y ≤ ∫ _a2 : Ω, (1 : ℝ) ∂μ :=
        integral_mono hint2 (integrable_const _) hinner
    _ = 1 := by simp

lemma measurable_pairK (W : Graphon Ω μ) :
    Measurable (Function.uncurry (pairK W)) := by
  have h2 : StronglyMeasurable (Function.uncurry fun q : (Ω × Ω) × Ω ↦
      fun a3 : Ω ↦ W q.1.1 q.1.2 * W q.1.1 q.2 * W q.1.1 a3 *
        (W q.1.2 q.2 * W q.1.2 a3 * W q.2 a3)) := by
    refine (?_ : Measurable _).stronglyMeasurable
    have mx : Measurable fun r : ((Ω × Ω) × Ω) × Ω ↦ r.1.1.1 :=
      measurable_fst.comp (measurable_fst.comp measurable_fst)
    have my : Measurable fun r : ((Ω × Ω) × Ω) × Ω ↦ r.1.1.2 :=
      measurable_snd.comp (measurable_fst.comp measurable_fst)
    have m2 : Measurable fun r : ((Ω × Ω) × Ω) × Ω ↦ r.1.2 :=
      measurable_snd.comp measurable_fst
    have m3 : Measurable fun r : ((Ω × Ω) × Ω) × Ω ↦ r.2 := measurable_snd
    exact (((W.measurable.comp (mx.prodMk my)).mul
      (W.measurable.comp (mx.prodMk m2))).mul
      (W.measurable.comp (mx.prodMk m3))).mul
      (((W.measurable.comp (my.prodMk m2)).mul
        (W.measurable.comp (my.prodMk m3))).mul
        (W.measurable.comp (m2.prodMk m3)))
  have h1 : StronglyMeasurable (Function.uncurry fun q : Ω × Ω ↦ fun a2 : Ω ↦
      ∫ a3, W q.1 q.2 * W q.1 a2 * W q.1 a3 * (W q.2 a2 * W q.2 a3 * W a2 a3)
        ∂μ) := by
    refine (?_ : Measurable _).stronglyMeasurable
    exact (h2.integral_prod_right' (ν := μ)).measurable
  exact (h1.integral_prod_right' (ν := μ)).measurable

/-- `∫ pairK(x,·) = κ₄(x)`: restoring the second clique coordinate. -/
theorem integral_pairK (W : Graphon Ω μ) (x : Ω) :
    (∫ y, pairK W x y ∂μ) = rootedK4 W x := by
  rw [rootedK4_eq]
  simp only [pairK]

/-- The pair weight is symmetric: the `K₄` does not distinguish its vertices. -/
theorem pairK_symm (W : Graphon Ω μ) (x y : Ω) : pairK W x y = pairK W y x := by
  simp only [pairK]
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  refine integral_congr_ae (ae_of_all _ fun a3 ↦ ?_)
  rw [W.symm x y]
  ring

/-! ### The graph -/

/-- Atlas 160: `K₄` on `0,1,2,3`, a page vertex `4` on the clique edge `01`, and
a pendant leaf `5` on the page. -/
def graph160 : SimpleGraph (Fin 6) :=
  graphFromEdges 6
    [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (0, 4), (1, 4), (4, 5)]

instance : DecidableRel graph160.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_graph160 :
    graph160.edgeFinset =
      {s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(2, 3), s(0, 4), s(1, 4),
        s(4, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_graph160 (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight graph160 W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 0) (x 3) * W (x 1) (x 2) *
        W (x 1) (x 3) * W (x 2) (x 3) * W (x 0) (x 4) * W (x 1) (x 4) *
        W (x 4) (x 5) := by
  rw [graphWeight, edgeFinset_graph160]
  simp
  ring

lemma graphWeight_graph160_cons (W : Graphon Ω μ) (a0 a1 a2 a3 a4 a5 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight graph160 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
        (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y)))))) =
      W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a3 * W a2 a3 * W a0 a4 *
        W a1 a4 * W a4 a5 := by
  rw [graphWeight_graph160]
  rfl

/-! ### The density identity -/

set_option maxHeartbeats 1000000 in
/-- **The density of Atlas 160 is `∫∫ pairK·B`.** -/
theorem homDensity_graph160 (W : Graphon Ω μ) :
    homDensity graph160 W =
      ∫ a0, ∫ a1, pairK W a0 a1 * pageB W a0 a1 ∂μ ∂μ := by
  have hm : Measurable (graphWeight graph160 W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight graph160 W x| ≤ 1 := fun x ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 5 → Ω ↦ graphWeight graph160 W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω ↦ graphWeight graph160 W (Fin.cons a0 (Fin.cons a1 y)))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  -- the two clique coordinates
  have hstep2 : ∀ a2 : Ω,
      (∫ y : Fin 3 → Ω, graphWeight graph160 W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)))
        ∂assignmentMeasure (Fin 3) μ) =
        ∫ a3, W a0 a1 * W a0 a2 * W a0 a3 * (W a1 a2 * W a1 a3 * W a2 a3) *
          pageB W a0 a1 ∂μ := by
    intro a2
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 3 → Ω ↦
        graphWeight graph160 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
      (hm.comp ((measurable_fin_cons a0).comp
        ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
      fun y ↦ hb _]
    refine integral_congr_ae (ae_of_all _ fun a3 ↦ ?_)
    simp only []
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 2 → Ω ↦ graphWeight graph160 W
        (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
      (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
        ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
      fun y ↦ hb _]
    have hstep4 : ∀ a4 : Ω,
        (∫ y : Fin 1 → Ω, graphWeight graph160 W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
              (Fin.cons a4 y)))))
          ∂assignmentMeasure (Fin 1) μ) =
          (W a0 a1 * W a0 a2 * W a0 a3 * (W a1 a2 * W a1 a3 * W a2 a3)) *
            (W a0 a4 * W a1 a4 * degree W a4) := by
      intro a4
      rw [integral_assignmentMeasure_succ
        (fun y : Fin 1 → Ω ↦ graphWeight graph160 W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
            (Fin.cons a4 y))))))
        (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
          ((measurable_fin_cons a2).comp ((measurable_fin_cons a3).comp
            (measurable_fin_cons a4))))))
        fun y ↦ hb _]
      have hval : ∀ a5 : Ω,
          (∫ y : Fin 0 → Ω, graphWeight graph160 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                (Fin.cons a4 (Fin.cons a5 y))))))
            ∂assignmentMeasure (Fin 0) μ) =
            (W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a3 * W a2 a3 *
              W a0 a4 * W a1 a4) * W a4 a5 := by
        intro a5
        rw [show (∫ y : Fin 0 → Ω, graphWeight graph160 W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
              (Fin.cons a4 (Fin.cons a5 y))))))
              ∂assignmentMeasure (Fin 0) μ) =
            W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a3 * W a2 a3 *
              W a0 a4 * W a1 a4 * W a4 a5 by simp [graphWeight_graph160_cons]]
      rw [integral_congr_ae (ae_of_all _ hval), integral_const_mul]
      show (W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a3 * W a2 a3 *
          W a0 a4 * W a1 a4) * degree W a4 =
        (W a0 a1 * W a0 a2 * W a0 a3 * (W a1 a2 * W a1 a3 * W a2 a3)) *
          (W a0 a4 * W a1 a4 * degree W a4)
      ring
    rw [integral_congr_ae (ae_of_all _ hstep4), integral_const_mul]
    rfl
  rw [integral_congr_ae (ae_of_all _ hstep2)]
  -- pull the page factor out of the two remaining clique integrals
  have h3 : ∀ a2 : Ω,
      (∫ a3, W a0 a1 * W a0 a2 * W a0 a3 * (W a1 a2 * W a1 a3 * W a2 a3) *
          pageB W a0 a1 ∂μ) =
        pageB W a0 a1 * ∫ a3, W a0 a1 * W a0 a2 * W a0 a3 *
          (W a1 a2 * W a1 a3 * W a2 a3) ∂μ := by
    intro a2
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun a3 ↦ by ring)
  rw [integral_congr_ae (ae_of_all _ h3), integral_const_mul]
  show pageB W a0 a1 * pairK W a0 a1 = pairK W a0 a1 * pageB W a0 a1
  ring

/-! ### Integrability against the pair weight -/

section PairIntegrals

variable {W : Graphon Ω μ} {f : Ω → Ω → ℝ} {C : ℝ}

private lemma pairK_mul_bdd (hfb : ∀ x y, |f x y| ≤ C) (x y : Ω) :
    |pairK W x y * f x y| ≤ C := by
  rw [abs_mul, abs_of_nonneg (pairK_nonneg W x y)]
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hfb x y)
  calc pairK W x y * |f x y| ≤ 1 * |f x y| :=
        mul_le_mul_of_nonneg_right (pairK_le_one W x y) (abs_nonneg _)
    _ = |f x y| := one_mul _
    _ ≤ C := hfb x y

private lemma integrable_pairK_mul (hfm : Measurable (Function.uncurry f))
    (hfb : ∀ x y, |f x y| ≤ C) (x : Ω) :
    Integrable (fun y ↦ pairK W x y * f x y) μ :=
  integrable_of_bdd
    (((measurable_pairK W).comp (measurable_const.prodMk measurable_id)).mul
      (hfm.comp (measurable_const.prodMk measurable_id))) (C := C)
    fun y ↦ pairK_mul_bdd hfb x y

private lemma measurable_pairK_inner (hfm : Measurable (Function.uncurry f)) :
    Measurable fun x ↦ ∫ y, pairK W x y * f x y ∂μ := by
  have h : StronglyMeasurable (Function.uncurry fun x y : Ω ↦
      pairK W x y * f x y) := by
    refine (?_ : Measurable _).stronglyMeasurable
    exact (measurable_pairK W).mul hfm
  exact (h.integral_prod_right' (ν := μ)).measurable

private lemma integrable_pairK_outer (hfm : Measurable (Function.uncurry f))
    (hfb : ∀ x y, |f x y| ≤ C) :
    Integrable (fun x ↦ ∫ y, pairK W x y * f x y ∂μ) μ := by
  refine integrable_of_bdd (measurable_pairK_inner hfm) (C := C) fun x ↦ ?_
  calc |∫ y, pairK W x y * f x y ∂μ| ≤ ∫ y, |pairK W x y * f x y| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _y : Ω, C ∂μ :=
        integral_mono (integrable_pairK_mul hfm hfb x).abs (integrable_const C)
          fun y ↦ pairK_mul_bdd hfb x y
    _ = C := by simp

end PairIntegrals

/-- Integrability of the bare pair weight. -/
private lemma integrable_pairK_self (W : Graphon Ω μ) (x : Ω) :
    Integrable (fun y ↦ pairK W x y) μ :=
  integrable_of_bdd
    ((measurable_pairK W).comp (measurable_const.prodMk measurable_id))
    (C := 1) fun y ↦ by
      rw [abs_of_nonneg (pairK_nonneg W x y)]; exact pairK_le_one W x y

private lemma integrable_pairK_self_outer (W : Graphon Ω μ) :
    Integrable (fun x ↦ ∫ y, pairK W x y ∂μ) μ := by
  have hmeas : Measurable fun x ↦ ∫ y, pairK W x y ∂μ := by
    have h : StronglyMeasurable (Function.uncurry fun x y : Ω ↦ pairK W x y) :=
      (measurable_pairK W).stronglyMeasurable
    exact (h.integral_prod_right' (ν := μ)).measurable
  refine integrable_of_bdd hmeas (C := 1) fun x ↦ ?_
  calc |∫ y, pairK W x y ∂μ| ≤ ∫ y, |pairK W x y| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _y : Ω, (1 : ℝ) ∂μ :=
        integral_mono (integrable_pairK_self W x).abs (integrable_const 1)
          fun y ↦ by
            rw [abs_of_nonneg (pairK_nonneg W x y)]; exact pairK_le_one W x y
    _ = 1 := by simp

/-! ### The page reduction -/

/-- The three pieces of the reduction, each an integral against `κ₄`. -/
theorem integral_pairK_fst (W : Graphon Ω μ) :
    (∫ a0, ∫ a1, pairK W a0 a1 * pathOp W a0 ∂μ ∂μ) =
      ∫ a, rootedK4 W a * pathOp W a ∂μ := by
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  have h : (∫ a1, pairK W a0 a1 * pathOp W a0 ∂μ) =
      pathOp W a0 * ∫ a1, pairK W a0 a1 ∂μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun a1 ↦ by ring)
  rw [h, integral_pairK]
  ring

theorem integral_pairK_const (W : Graphon Ω μ) :
    (∫ a0, ∫ a1, pairK W a0 a1 ∂μ ∂μ) = ∫ a, rootedK4 W a ∂μ :=
  integral_congr_ae (ae_of_all _ fun a0 ↦ integral_pairK W a0)

theorem integral_pairK_snd (W : Graphon Ω μ) :
    (∫ a0, ∫ a1, pairK W a0 a1 * pathOp W a1 ∂μ ∂μ) =
      ∫ a, rootedK4 W a * pathOp W a ∂μ := by
  have hmeas : Measurable (Function.uncurry fun a0 a1 : Ω ↦
      pairK W a0 a1 * pathOp W a1) :=
    (measurable_pairK W).mul ((measurable_pathOp W).comp measurable_snd)
  have hint : Integrable (Function.uncurry fun a0 a1 : Ω ↦
      pairK W a0 a1 * pathOp W a1) (μ.prod μ) := by
    refine integrable_of_bdd hmeas (C := 1) fun q ↦ ?_
    show |pairK W q.1 q.2 * pathOp W q.2| ≤ 1
    rw [abs_of_nonneg (mul_nonneg (pairK_nonneg W q.1 q.2) (pathOp_nonneg W q.2))]
    exact mul_le_one₀ (pairK_le_one W q.1 q.2) (pathOp_nonneg W q.2)
      (pathOp_le_one W q.2)
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  have h : (∫ a0, pairK W a0 a1 * pathOp W a1 ∂μ) =
      pathOp W a1 * ∫ a0, pairK W a1 a0 ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
    show pairK W a0 a1 * pathOp W a1 = pathOp W a1 * pairK W a1 a0
    rw [pairK_symm W a0 a1]; ring
  rw [h, integral_pairK]
  ring

set_option maxHeartbeats 800000 in
/-- **The page reduction.**  `t(H,W) ≥ ∫ (2A - p)·κ₄`. -/
theorem signed_le_homDensity_graph160 (W : Graphon Ω μ) :
    (∫ a, (2 * pathOp W a - cliqueDensity 2 W) * rootedK4 W a ∂μ) ≤
      homDensity graph160 W := by
  set p := cliqueDensity 2 W with hpdef
  -- the comparison function
  have hgm : Measurable (Function.uncurry fun x y : Ω ↦
      pathOp W x + pathOp W y - p) :=
    (((measurable_pathOp W).comp measurable_fst).add
      ((measurable_pathOp W).comp measurable_snd)).sub measurable_const
  have hgb : ∀ x y : Ω, |pathOp W x + pathOp W y - p| ≤ 3 := by
    intro x y
    have h1 := pathOp_nonneg W x; have h2 := pathOp_le_one W x
    have h3 := pathOp_nonneg W y; have h4 := pathOp_le_one W y
    have h5 : 0 ≤ p := cliqueDensity_nonneg 2 W
    have h6 : p ≤ 1 := cliqueDensity_le_one 2 W
    rw [abs_le]; constructor <;> linarith
  have hBm : Measurable (Function.uncurry (pageB W)) := measurable_pageB W
  have hBb : ∀ x y : Ω, |pageB W x y| ≤ 3 := fun x y ↦ by
    rw [abs_of_nonneg (pageB_nonneg W x y)]
    linarith [pageB_le_one W x y]
  -- two-level monotonicity
  have hmono : (∫ a0, ∫ a1, pairK W a0 a1 * (pathOp W a0 + pathOp W a1 - p)
      ∂μ ∂μ) ≤ ∫ a0, ∫ a1, pairK W a0 a1 * pageB W a0 a1 ∂μ ∂μ := by
    refine integral_mono (integrable_pairK_outer hgm hgb)
      (integrable_pairK_outer hBm hBb) fun a0 ↦ ?_
    refine integral_mono (integrable_pairK_mul hgm hgb a0)
      (integrable_pairK_mul hBm hBb a0) fun a1 ↦ ?_
    exact mul_le_mul_of_nonneg_left (pathOp_add_sub_le_pageB W a0 a1)
      (pairK_nonneg W a0 a1)
  -- two-level linearity
  have hsplit : (∫ a0, ∫ a1, pairK W a0 a1 * (pathOp W a0 + pathOp W a1 - p)
      ∂μ ∂μ) =
      (∫ a0, ∫ a1, pairK W a0 a1 * pathOp W a0 ∂μ ∂μ) +
        (∫ a0, ∫ a1, pairK W a0 a1 * pathOp W a1 ∂μ ∂μ) -
        p * ∫ a0, ∫ a1, pairK W a0 a1 ∂μ ∂μ := by
    have hf1 : Measurable (Function.uncurry fun x y : Ω ↦ pathOp W x) :=
      (measurable_pathOp W).comp measurable_fst
    have hf2 : Measurable (Function.uncurry fun x y : Ω ↦ pathOp W y) :=
      (measurable_pathOp W).comp measurable_snd
    have hb1 : ∀ x y : Ω, |pathOp W x| ≤ 3 := fun x _ ↦ by
      rw [abs_of_nonneg (pathOp_nonneg W x)]; linarith [pathOp_le_one W x]
    have hb2 : ∀ x y : Ω, |pathOp W y| ≤ 3 := fun _ y ↦ by
      rw [abs_of_nonneg (pathOp_nonneg W y)]; linarith [pathOp_le_one W y]
    have hinner : ∀ a0 : Ω,
        (∫ a1, pairK W a0 a1 * (pathOp W a0 + pathOp W a1 - p) ∂μ) =
          (∫ a1, pairK W a0 a1 * pathOp W a0 ∂μ) +
            (∫ a1, pairK W a0 a1 * pathOp W a1 ∂μ) -
            p * ∫ a1, pairK W a0 a1 ∂μ := by
      intro a0
      have e1 : Integrable (fun a1 ↦ pairK W a0 a1 * pathOp W a0 +
          pairK W a0 a1 * pathOp W a1) μ :=
        ((integrable_pairK_mul hf1 hb1 a0).add
          (integrable_pairK_mul hf2 hb2 a0)).congr (ae_of_all _ fun _ ↦ rfl)
      have e2 : Integrable (fun a1 ↦ p * pairK W a0 a1) μ :=
        (integrable_pairK_self W a0).const_mul _
      have hfun : ∀ a1 : Ω, pairK W a0 a1 * (pathOp W a0 + pathOp W a1 - p) =
          (pairK W a0 a1 * pathOp W a0 + pairK W a0 a1 * pathOp W a1) -
            p * pairK W a0 a1 := fun a1 ↦ by ring
      rw [integral_congr_ae (ae_of_all _ hfun), integral_sub e1 e2,
        integral_add (integrable_pairK_mul hf1 hb1 a0)
          (integrable_pairK_mul hf2 hb2 a0), integral_const_mul]
    rw [integral_congr_ae (ae_of_all _ hinner)]
    have o1 : Integrable (fun a0 ↦ (∫ a1, pairK W a0 a1 * pathOp W a0 ∂μ) +
        ∫ a1, pairK W a0 a1 * pathOp W a1 ∂μ) μ :=
      ((integrable_pairK_outer hf1 hb1).add
        (integrable_pairK_outer hf2 hb2)).congr (ae_of_all _ fun _ ↦ rfl)
    have o2 : Integrable (fun a0 ↦ p * ∫ a1, pairK W a0 a1 ∂μ) μ :=
      (integrable_pairK_self_outer W).const_mul _
    have hfun2 : ∀ a0 : Ω,
        ((∫ a1, pairK W a0 a1 * pathOp W a0 ∂μ) +
            (∫ a1, pairK W a0 a1 * pathOp W a1 ∂μ) -
            p * ∫ a1, pairK W a0 a1 ∂μ) =
          ((∫ a1, pairK W a0 a1 * pathOp W a0 ∂μ) +
            ∫ a1, pairK W a0 a1 * pathOp W a1 ∂μ) -
            p * ∫ a1, pairK W a0 a1 ∂μ := fun _ ↦ rfl
    rw [integral_congr_ae (ae_of_all _ hfun2), integral_sub o1 o2,
      integral_add (integrable_pairK_outer hf1 hb1)
        (integrable_pairK_outer hf2 hb2), integral_const_mul]
  -- assemble
  rw [homDensity_graph160]
  refine le_trans ?_ hmono
  rw [hsplit, integral_pairK_fst, integral_pairK_snd, integral_pairK_const]
  have hcomb : (∫ a, (2 * pathOp W a - p) * rootedK4 W a ∂μ) =
      (∫ a, rootedK4 W a * pathOp W a ∂μ) +
        (∫ a, rootedK4 W a * pathOp W a ∂μ) -
        p * ∫ a, rootedK4 W a ∂μ := by
    have hi1 : Integrable (fun a ↦ rootedK4 W a * pathOp W a) μ :=
      integrable_of_bdd ((measurable_rootedK4 W).mul (measurable_pathOp W))
        (C := 1) fun a ↦ by
          rw [abs_of_nonneg (mul_nonneg (rootedK4_nonneg W a)
            (pathOp_nonneg W a))]
          exact mul_le_one₀ (rootedK4_le_one W a) (pathOp_nonneg W a)
            (pathOp_le_one W a)
    have hi2 : Integrable (fun a ↦ rootedK4 W a) μ :=
      integrable_of_bdd (measurable_rootedK4 W) (C := 1) fun a ↦ by
        rw [abs_of_nonneg (rootedK4_nonneg W a)]; exact rootedK4_le_one W a
    have hfun : ∀ a : Ω, (2 * pathOp W a - p) * rootedK4 W a =
        (rootedK4 W a * pathOp W a + rootedK4 W a * pathOp W a) -
          p * rootedK4 W a := fun a ↦ by ring
    have e1 : Integrable (fun a ↦ rootedK4 W a * pathOp W a +
        rootedK4 W a * pathOp W a) μ :=
      (hi1.add hi1).congr (ae_of_all _ fun _ ↦ rfl)
    have e2 : Integrable (fun a ↦ p * rootedK4 W a) μ := hi2.const_mul _
    rw [integral_congr_ae (ae_of_all _ hfun), integral_sub e1 e2,
      integral_add hi1 hi1, integral_const_mul]
  rw [hcomb]

/-! ### Integrating the supporting plane -/

/-- `∫ L_p(d,A) = T_p`: the two corrections have mean zero, because `∫d = p` and
`∫A = ∫d²`. -/
theorem integral_plane (W : Graphon Ω μ) :
    (∫ x, plane (cliqueDensity 2 W) (degree W x) (pathOp W x) ∂μ) =
      targetT (cliqueDensity 2 W) := by
  set p := cliqueDensity 2 W with hpdef
  have hd := integrable_degree W
  have hA := integrable_pathOp W
  have hd2 := integrable_degree_pow W 2
  have i0 : Integrable (fun _ : Ω ↦ targetT p -
      p * (2 * p - 1) * (30 * p ^ 2 - 15 * p - 2) * p) μ := integrable_const _
  have i1 : Integrable (fun x : Ω ↦
      p * (2 * p - 1) * (30 * p ^ 2 - 15 * p - 2) * degree W x) μ :=
    hd.const_mul _
  have i2 : Integrable (fun x : Ω ↦
      4 * p * (2 * p - 1) * (5 * p - 3) * pathOp W x) μ := hA.const_mul _
  have i3 : Integrable (fun x : Ω ↦
      4 * p * (2 * p - 1) * (5 * p - 3) * degree W x ^ 2) μ := hd2.const_mul _
  have hfun : ∀ x : Ω, plane p (degree W x) (pathOp W x) =
      (targetT p - p * (2 * p - 1) * (30 * p ^ 2 - 15 * p - 2) * p) +
        p * (2 * p - 1) * (30 * p ^ 2 - 15 * p - 2) * degree W x +
        4 * p * (2 * p - 1) * (5 * p - 3) * pathOp W x -
        4 * p * (2 * p - 1) * (5 * p - 3) * degree W x ^ 2 := by
    intro x
    simp only [plane]
    ring
  have e1 := integral_sub ((i0.add i1).add i2) i3
  have e2 := integral_add (i0.add i1) i2
  have e3 := integral_add i0 i1
  simp only [Pi.add_apply] at e1 e2 e3
  rw [integral_congr_ae (ae_of_all _ hfun), e1, e2, e3, integral_const,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_degree, integral_pathOp, moment]
  simp
  rw [← hpdef]
  ring

/-! ### The bound -/

/-- **Atlas 160 dominates its target.** -/
theorem graph160_bound (W : Graphon Ω μ)
    (hp : (2 : ℝ) / 3 ≤ cliqueDensity 2 W) :
    targetT (cliqueDensity 2 W) ≤ homDensity graph160 W := by
  set p := cliqueDensity 2 W with hpdef
  have hint1 : Integrable (fun x ↦ plane p (degree W x) (pathOp W x)) μ := by
    have hsplit : ∀ x : Ω, plane p (degree W x) (pathOp W x) =
        targetT p + p * (2 * p - 1) * (30 * p ^ 2 - 15 * p - 2) * degree W x +
          4 * p * (2 * p - 1) * (5 * p - 3) * pathOp W x -
          4 * p * (2 * p - 1) * (5 * p - 3) * degree W x ^ 2 -
          p * (2 * p - 1) * (30 * p ^ 2 - 15 * p - 2) * p := by
      intro x; simp only [plane]; ring
    refine Integrable.congr ?_ (ae_of_all _ fun x ↦ (hsplit x).symm)
    exact ((((integrable_const _).add ((integrable_degree W).const_mul _)).add
      ((integrable_pathOp W).const_mul _)).sub
      ((integrable_degree_pow W 2).const_mul _)).sub (integrable_const _)
  have hint2 : Integrable (fun x ↦ (2 * pathOp W x - p) * rootedK4 W x) μ := by
    refine integrable_of_bdd (((measurable_const.mul
      (measurable_pathOp W)).sub measurable_const).mul
      (measurable_rootedK4 W)) (C := 3) fun x ↦ ?_
    rw [abs_mul, abs_of_nonneg (rootedK4_nonneg W x)]
    have h1 : |2 * pathOp W x - p| ≤ 3 := by
      have := pathOp_nonneg W x; have := pathOp_le_one W x
      have := cliqueDensity_nonneg 2 W; have := cliqueDensity_le_one 2 W
      rw [abs_le]; constructor <;> linarith
    calc |2 * pathOp W x - p| * rootedK4 W x ≤ |2 * pathOp W x - p| * 1 :=
          mul_le_mul_of_nonneg_left (rootedK4_le_one W x) (abs_nonneg _)
      _ = |2 * pathOp W x - p| := mul_one _
      _ ≤ 3 := h1
  have hmono : (∫ x, plane p (degree W x) (pathOp W x) ∂μ) ≤
      ∫ x, (2 * pathOp W x - p) * rootedK4 W x ∂μ :=
    integral_mono hint1 hint2 fun x ↦ plane_le_signed W hp x
  rw [integral_plane W] at hmono
  exact le_trans hmono (signed_le_homDensity_graph160 W)

/-! ### Chromatic data and the catalogue proposition -/

lemma affineProd_160 (z : ℝ) :
    affineProd [0, 1, 1, 2, 2, 3] z = z ^ 2 * (2 * z - 1) ^ 2 * (3 * z - 2) := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_cons, affineProd_nil]
  ring

/-- `K₄` on `{0,1,2,3}`, then the page `4` on the clique edge `{0,1}`, then the
leaf `5` on `{4}`. -/
def equiv160 : Option (Option (Fin 4)) ≃ Fin 6 where
  toFun a := match a with
    | none => 5
    | some none => 4
    | some (some i) => ![0, 1, 2, 3] i
  invFun j := ![some (some 0), some (some 1), some (some 2), some (some 3),
    some none, none] j
  left_inv := by decide
  right_inv := by decide

def iso160 :
    attachVertex (attachVertex (⊤ : SimpleGraph (Fin 4)) {0, 1}) {none} ≃g
      graph160 where
  toEquiv := equiv160
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom160 : IsChromaticPolynomial graph160
    ((([0, 1, 1, 2, 2, 3] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := graph160) iso160
    (isClique_singleton _ none)
    (isChromaticPolynomial_attachVertex (isCliqueTop _)
      (isChromaticPolynomial_top 4))
  rw [show ((({0, 1} : Finset (Fin 4))).card) = 2 from by decide,
    Finset.card_singleton] at h
  have hpoly :
      ((([0, 1, 1, 2, 2, 3] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) *
        ((X - C ((2 : ℕ) : ℝ)) * ∏ i ∈ range 4, ((X : ℝ[X]) - C (i : ℝ))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count160 (k : ℕ) :
    properAssignmentCount graph160 k = (k - 1) * ((k - 2) * k.descFactorial 4) := by
  rw [properAssignmentCount_of_attachIso (H' := graph160) iso160
      (isClique_singleton _ none) k,
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show ((({0, 1} : Finset (Fin 4))).card) = 2 from by decide,
    Finset.card_singleton]

theorem num160 : IsChromaticNumber graph160 4 where
  positive := by rw [count160]; decide
  zero_below k hk := by
    rw [count160, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero]

/-- **Atlas 160 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_160 : Taeyoung.SatisfiesLowerBound graph160 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P =
      (([0, 1, 1, 2, 2, 3] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := graph160) hP chrom160
  have hreq : r = 4 := IsChromaticNumber.unique (H := graph160) hr num160
  subst hPeq
  subst hreq
  have hp : (2 : ℝ) / 3 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := graph160_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    simp only [targetT] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 2, 2, 3] (by norm_num) hone,
      affineProd_160]
    simpa only [targetT] using hkey

end Taeyoung.Methods.Atlas160
