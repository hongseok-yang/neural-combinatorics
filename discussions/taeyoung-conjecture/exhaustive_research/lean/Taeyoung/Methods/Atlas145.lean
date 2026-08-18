import Taeyoung.Methods.Atlas148.Chromatic

/-!
# Atlas 145: two triangle pages on one edge of a 4-cycle

`notes/c4_triangle_page_concentration.tex` compares two placements of two
triangle pages on a `4`-cycle: both on one cycle edge (Atlas 145) or one on
each of two adjacent cycle edges (Atlas 148).  It proves

```
t(H_same, W) - t(H_adj, W) = ½ ∫ (A - B)² dΛ ≥ 0
```

for the `4`-cycle measure `dΛ`, and then quotes the Atlas 148 theorem.

The formalization takes a shorter route to the same inequality.  Label the
`4`-cycle so that the two *opposite* corners `x₀, x₂` are the outer
integration variables; the remaining two cycle vertices `x₁, x₃` then
integrate independently, and for fixed `x₀, x₂` the three quantities

```
P = ∫ W(x₀,u)W(u,x₂) du,
Q = ∫ W(x₀,u)W(u,x₂)·S(x₀,u) du,
R = ∫ W(x₀,u)W(u,x₂)·S(x₀,u)² du
```

satisfy `t(H_adj) = ∫∫ Q²` and `t(H_same) = ∫∫ P·R`.  So the note's square
identity — which needs a reflection of a four-fold integral — is replaced by
the pointwise weighted Cauchy--Schwarz `Q² ≤ P·R`, the same
`(∫Aη)² ≤ (∫A)(∫Aη²)` used throughout this project, at weight
`A(u) = W(x₀,u)W(u,x₂)` and `η(u) = S(x₀,u)`.

Both graphs are laid out on that frame: `0, 1` are the opposite corners,
`2, 3` the other two cycle vertices, and `4, 5` the pages — both on the edge
`0-2` for Atlas 145, one on `0-2` and one on `0-3` for Atlas 148.  The frame
copy of Atlas 148 is carried to `Methods/Atlas148.graph148` by
`homDensity_iso`.

The chromatic data is the same as Atlas 148's, `r(r-1)(r-2)²(r²-3r+3)`, with
the same surjective counts; it is proved again for this graph because the two
are not isomorphic.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.Atlas145

open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.PureChordal
  Taeyoung.Methods.Negative Taeyoung.Methods.Atlas148

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The two graphs on the `4`-cycle frame -/

/-- Opposite corners `0, 1`; the other cycle vertices `2, 3`; both pages on the
cycle edge `0-2`. -/
def frame145 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (2, 4), (2, 5)]

/-- The same frame with one page on `0-2` and one on `0-3`. -/
def frameAdj : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (2, 4), (3, 5)]

instance : DecidableRel frame145.Adj := graphFromEdges_decidableAdj _ _
instance : DecidableRel frameAdj.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_frame145 :
    frame145.edgeFinset =
      {s(0, 2), s(0, 3), s(0, 4), s(0, 5), s(1, 2), s(1, 3), s(2, 4), s(2, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma edgeFinset_frameAdj :
    frameAdj.edgeFinset =
      {s(0, 2), s(0, 3), s(0, 4), s(0, 5), s(1, 2), s(1, 3), s(2, 4), s(3, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_frame145 (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight frame145 W x =
      W (x 0) (x 2) * W (x 0) (x 3) * W (x 0) (x 4) * W (x 0) (x 5) *
        W (x 1) (x 2) * W (x 1) (x 3) * W (x 2) (x 4) * W (x 2) (x 5) := by
  rw [graphWeight, edgeFinset_frame145]
  simp
  ring

lemma graphWeight_frameAdj (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight frameAdj W x =
      W (x 0) (x 2) * W (x 0) (x 3) * W (x 0) (x 4) * W (x 0) (x 5) *
        W (x 1) (x 2) * W (x 1) (x 3) * W (x 2) (x 4) * W (x 3) (x 5) := by
  rw [graphWeight, edgeFinset_frameAdj]
  simp
  ring

lemma graphWeight_frame145_cons (W : Graphon Ω μ) (a0 a1 a2 a3 a4 a5 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight frame145 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
        (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y)))))) =
      W a0 a2 * W a0 a3 * W a0 a4 * W a0 a5 * W a1 a2 * W a1 a3 * W a2 a4 *
        W a2 a5 := by
  rw [graphWeight_frame145]
  rfl

lemma graphWeight_frameAdj_cons (W : Graphon Ω μ) (a0 a1 a2 a3 a4 a5 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight frameAdj W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
        (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y)))))) =
      W a0 a2 * W a0 a3 * W a0 a4 * W a0 a5 * W a1 a2 * W a1 a3 * W a2 a4 *
        W a3 a5 := by
  rw [graphWeight_frameAdj]
  rfl

/-! ### The three cycle-arm integrals -/

/-- `Q(x,y) = ∫ W(x,u)W(y,u)·S(x,u) du`. -/
noncomputable def armOne (W : Graphon Ω μ) (x y : Ω) : ℝ :=
  ∫ u, W x u * W y u * pageOp W 0 x u ∂μ

/-- `R(x,y) = ∫ W(x,u)W(y,u)·S(x,u)² du`. -/
noncomputable def armTwo (W : Graphon Ω μ) (x y : Ω) : ℝ :=
  ∫ u, W x u * W y u * pageOp W 0 x u ^ 2 ∂μ

section Arms

variable (W : Graphon Ω μ)

private lemma arm_weight_nonneg (x y u : Ω) : 0 ≤ W x u * W y u :=
  mul_nonneg (W.nonneg _ _) (W.nonneg _ _)

lemma integrable_arm_weight (x y : Ω) : Integrable (fun u ↦ W x u * W y u) μ :=
  integrable_of_bdd ((measurable_row W.measurable x).mul
    (measurable_row W.measurable y)) (C := 1) fun u ↦ by
      rw [abs_of_nonneg (arm_weight_nonneg W x y u)]
      exact mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _)

lemma integrable_armOne (x y : Ω) :
    Integrable (fun u ↦ W x u * W y u * pageOp W 0 x u) μ :=
  integrable_of_bdd (((measurable_row W.measurable x).mul
    (measurable_row W.measurable y)).mul
      (measurable_row (measurable_pageOp W le_rfl) x)) (C := 1) fun u ↦ by
        have h0 : 0 ≤ W x u * W y u * pageOp W 0 x u :=
          mul_nonneg (arm_weight_nonneg W x y u) (pageOp_nonneg W le_rfl _ _)
        rw [abs_of_nonneg h0]
        exact mul_le_one₀ (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
          (pageOp_nonneg W le_rfl _ _) (pageOp_le_one W le_rfl _ _)

lemma integrable_armTwo (x y : Ω) :
    Integrable (fun u ↦ W x u * W y u * pageOp W 0 x u ^ 2) μ :=
  integrable_of_bdd (((measurable_row W.measurable x).mul
    (measurable_row W.measurable y)).mul
      ((measurable_row (measurable_pageOp W le_rfl) x).pow_const 2)) (C := 1)
    fun u ↦ by
      have h0 : 0 ≤ W x u * W y u * pageOp W 0 x u ^ 2 :=
        mul_nonneg (arm_weight_nonneg W x y u) (sq_nonneg _)
      rw [abs_of_nonneg h0]
      exact mul_le_one₀ (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
        (sq_nonneg _)
        (pow_le_one₀ (pageOp_nonneg W le_rfl _ _) (pageOp_le_one W le_rfl _ _))

lemma armOne_nonneg (x y : Ω) : 0 ≤ armOne W x y :=
  integral_nonneg fun u ↦
    mul_nonneg (arm_weight_nonneg W x y u) (pageOp_nonneg W le_rfl _ _)

lemma armOne_le_one (x y : Ω) : armOne W x y ≤ 1 := by
  refine le_of_abs_le (abs_integral_le_of_bdd (((measurable_row W.measurable x).mul
    (measurable_row W.measurable y)).mul
      (measurable_row (measurable_pageOp W le_rfl) x)) fun u ↦ ?_)
  have h0 : 0 ≤ W x u * W y u * pageOp W 0 x u :=
    mul_nonneg (arm_weight_nonneg W x y u) (pageOp_nonneg W le_rfl _ _)
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
    (pageOp_nonneg W le_rfl _ _) (pageOp_le_one W le_rfl _ _)

lemma armTwo_nonneg (x y : Ω) : 0 ≤ armTwo W x y :=
  integral_nonneg fun u ↦ mul_nonneg (arm_weight_nonneg W x y u) (sq_nonneg _)

lemma armTwo_le_one (x y : Ω) : armTwo W x y ≤ 1 := by
  refine le_of_abs_le (abs_integral_le_of_bdd (((measurable_row W.measurable x).mul
    (measurable_row W.measurable y)).mul
      ((measurable_row (measurable_pageOp W le_rfl) x).pow_const 2)) fun u ↦ ?_)
  have h0 : 0 ≤ W x u * W y u * pageOp W 0 x u ^ 2 :=
    mul_nonneg (arm_weight_nonneg W x y u) (sq_nonneg _)
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
    (sq_nonneg _)
    (pow_le_one₀ (pageOp_nonneg W le_rfl _ _) (pageOp_le_one W le_rfl _ _))

lemma measurable_armOne : Measurable fun q : Ω × Ω ↦ armOne W q.1 q.2 := by
  have hg : StronglyMeasurable fun p : (Ω × Ω) × Ω ↦
      W p.1.1 p.2 * W p.1.2 p.2 * pageOp W 0 p.1.1 p.2 := by
    refine (?_ : Measurable _).stronglyMeasurable
    exact ((W.measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (W.measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).mul
      ((measurable_pageOp W le_rfl).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  exact (hg.integral_prod_right' (ν := μ)).measurable

lemma measurable_armTwo : Measurable fun q : Ω × Ω ↦ armTwo W q.1 q.2 := by
  have hg : StronglyMeasurable fun p : (Ω × Ω) × Ω ↦
      W p.1.1 p.2 * W p.1.2 p.2 * pageOp W 0 p.1.1 p.2 ^ 2 := by
    refine (?_ : Measurable _).stronglyMeasurable
    exact ((W.measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (W.measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).mul
      (((measurable_pageOp W le_rfl).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).pow_const 2)

  exact (hg.integral_prod_right' (ν := μ)).measurable

/-- **The page-concentration Cauchy--Schwarz.**  `Q² ≤ P·R`. -/
theorem sq_armOne_le (x y : Ω) :
    armOne W x y ^ 2 ≤ pageOp W 0 x y * armTwo W x y := by
  have hcs := integral_mul_sq_le_integral_mul_integral_mul_sq
    (A := fun u ↦ W x u * W y u) (η := fun u ↦ pageOp W 0 x u)
    (integrable_arm_weight W x y) (integrable_armOne W x y)
    (integrable_armTwo W x y) (fun u ↦ arm_weight_nonneg W x y u)
  rw [← pageOp_zero_eq] at hcs
  exact hcs

end Arms

/-! ### The two peeled densities -/

theorem homDensity_frame145 (W : Graphon Ω μ) :
    homDensity frame145 W =
      ∫ a0, ∫ a1, pageOp W 0 a0 a1 * armTwo W a0 a1 ∂μ ∂μ := by
  have hm : Measurable (graphWeight frame145 W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight frame145 W x| ≤ 1 := fun x ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 5 → Ω ↦ graphWeight frame145 W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω ↦ graphWeight frame145 W (Fin.cons a0 (Fin.cons a1 y)))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  have hstep2 : ∀ a2 : Ω,
      (∫ y : Fin 3 → Ω,
          graphWeight frame145 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)))
        ∂assignmentMeasure (Fin 3) μ) =
        pageOp W 0 a0 a1 * (W a0 a2 * W a1 a2 * pageOp W 0 a0 a2 ^ 2) := by
    intro a2
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 3 → Ω ↦
        graphWeight frame145 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
      (hm.comp ((measurable_fin_cons a0).comp
        ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
      fun y ↦ hb _]
    have hstep3 : ∀ a3 : Ω,
        (∫ y : Fin 2 → Ω, graphWeight frame145 W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
          ∂assignmentMeasure (Fin 2) μ) =
          (W a0 a2 * W a1 a2 * pageOp W 0 a0 a2 ^ 2) *
            (W a0 a3 * W a1 a3 * degree W a3 ^ (0 : ℝ)) := by
      intro a3
      rw [integral_assignmentMeasure_succ
        (fun y : Fin 2 → Ω ↦ graphWeight frame145 W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
        (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
          ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
        fun y ↦ hb _]
      have hstep4 : ∀ a4 : Ω,
          (∫ y : Fin 1 → Ω, graphWeight frame145 W (Fin.cons a0 (Fin.cons a1
              (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y)))))
            ∂assignmentMeasure (Fin 1) μ) =
            (W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * pageOp W 0 a0 a2) *
              (W a0 a4 * W a2 a4 * degree W a4 ^ (0 : ℝ)) := by
        intro a4
        rw [integral_assignmentMeasure_succ
          (fun y : Fin 1 → Ω ↦ graphWeight frame145 W (Fin.cons a0 (Fin.cons a1
            (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y))))))
          (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
            ((measurable_fin_cons a2).comp ((measurable_fin_cons a3).comp
              (measurable_fin_cons a4))))))
          fun y ↦ hb _]
        have hval : ∀ a5 : Ω,
            (∫ y : Fin 0 → Ω, graphWeight frame145 W (Fin.cons a0 (Fin.cons a1
                (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y))))))
              ∂assignmentMeasure (Fin 0) μ) =
              (W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * (W a0 a4 * W a2 a4)) *
                (W a0 a5 * W a2 a5 * degree W a5 ^ (0 : ℝ)) := by
          intro a5
          rw [show (∫ y : Fin 0 → Ω, graphWeight frame145 W (Fin.cons a0
              (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 (Fin.cons a4
                (Fin.cons a5 y)))))) ∂assignmentMeasure (Fin 0) μ) =
              W a0 a2 * W a0 a3 * W a0 a4 * W a0 a5 * W a1 a2 * W a1 a3 *
                W a2 a4 * W a2 a5 by simp [graphWeight_frame145_cons],
            Real.rpow_zero]
          ring
        rw [integral_congr_ae (ae_of_all _ hval), integral_const_mul, ← pageOp,
          Real.rpow_zero]
        ring
      rw [integral_congr_ae (ae_of_all _ hstep4), integral_const_mul, ← pageOp,
        Real.rpow_zero]
      ring
    rw [integral_congr_ae (ae_of_all _ hstep3), integral_const_mul, ← pageOp]
    ring
  rw [integral_congr_ae (ae_of_all _ hstep2), integral_const_mul, armTwo]

theorem homDensity_frameAdj (W : Graphon Ω μ) :
    homDensity frameAdj W = ∫ a0, ∫ a1, armOne W a0 a1 ^ 2 ∂μ ∂μ := by
  have hm : Measurable (graphWeight frameAdj W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight frameAdj W x| ≤ 1 := fun x ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 5 → Ω ↦ graphWeight frameAdj W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω ↦ graphWeight frameAdj W (Fin.cons a0 (Fin.cons a1 y)))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  have hstep2 : ∀ a2 : Ω,
      (∫ y : Fin 3 → Ω,
          graphWeight frameAdj W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)))
        ∂assignmentMeasure (Fin 3) μ) =
        armOne W a0 a1 * (W a0 a2 * W a1 a2 * pageOp W 0 a0 a2) := by
    intro a2
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 3 → Ω ↦
        graphWeight frameAdj W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
      (hm.comp ((measurable_fin_cons a0).comp
        ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
      fun y ↦ hb _]
    have hstep3 : ∀ a3 : Ω,
        (∫ y : Fin 2 → Ω, graphWeight frameAdj W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
          ∂assignmentMeasure (Fin 2) μ) =
          (W a0 a2 * W a1 a2 * pageOp W 0 a0 a2) *
            (W a0 a3 * W a1 a3 * pageOp W 0 a0 a3) := by
      intro a3
      rw [integral_assignmentMeasure_succ
        (fun y : Fin 2 → Ω ↦ graphWeight frameAdj W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
        (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
          ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
        fun y ↦ hb _]
      have hstep4 : ∀ a4 : Ω,
          (∫ y : Fin 1 → Ω, graphWeight frameAdj W (Fin.cons a0 (Fin.cons a1
              (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y)))))
            ∂assignmentMeasure (Fin 1) μ) =
            (W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * pageOp W 0 a0 a3) *
              (W a0 a4 * W a2 a4 * degree W a4 ^ (0 : ℝ)) := by
        intro a4
        rw [integral_assignmentMeasure_succ
          (fun y : Fin 1 → Ω ↦ graphWeight frameAdj W (Fin.cons a0 (Fin.cons a1
            (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y))))))
          (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
            ((measurable_fin_cons a2).comp ((measurable_fin_cons a3).comp
              (measurable_fin_cons a4))))))
          fun y ↦ hb _]
        have hval : ∀ a5 : Ω,
            (∫ y : Fin 0 → Ω, graphWeight frameAdj W (Fin.cons a0 (Fin.cons a1
                (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y))))))
              ∂assignmentMeasure (Fin 0) μ) =
              (W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * (W a0 a4 * W a2 a4)) *
                (W a0 a5 * W a3 a5 * degree W a5 ^ (0 : ℝ)) := by
          intro a5
          rw [show (∫ y : Fin 0 → Ω, graphWeight frameAdj W (Fin.cons a0
              (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 (Fin.cons a4
                (Fin.cons a5 y)))))) ∂assignmentMeasure (Fin 0) μ) =
              W a0 a2 * W a0 a3 * W a0 a4 * W a0 a5 * W a1 a2 * W a1 a3 *
                W a2 a4 * W a3 a5 by simp [graphWeight_frameAdj_cons],
            Real.rpow_zero]
          ring
        rw [integral_congr_ae (ae_of_all _ hval), integral_const_mul, ← pageOp,
          Real.rpow_zero]
        ring
      rw [integral_congr_ae (ae_of_all _ hstep4), integral_const_mul, ← pageOp]
      ring
    rw [integral_congr_ae (ae_of_all _ hstep3), integral_const_mul, ← armOne]
    ring
  rw [integral_congr_ae (ae_of_all _ hstep2), integral_const_mul, ← armOne, sq]

/-! ### The concentration inequality -/

set_option maxHeartbeats 800000 in
/-- **Concentrating the two pages on one cycle edge does not decrease the
density.** -/
theorem homDensity_frameAdj_le (W : Graphon Ω μ) :
    homDensity frameAdj W ≤ homDensity frame145 W := by
  rw [homDensity_frame145, homDensity_frameAdj]
  have hiL : Integrable (fun q : Ω × Ω ↦ armOne W q.1 q.2 ^ 2) (μ.prod μ) :=
    integrable_prod_of_bdd ((measurable_armOne W).pow_const 2) (C := 1) fun q ↦ by
      show |armOne W q.1 q.2 ^ 2| ≤ 1
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_one₀ (armOne_nonneg W _ _) (armOne_le_one W _ _)
  have hiR : Integrable (fun q : Ω × Ω ↦
      pageOp W 0 q.1 q.2 * armTwo W q.1 q.2) (μ.prod μ) :=
    integrable_prod_of_bdd ((measurable_pageOp W le_rfl).mul (measurable_armTwo W))
      (C := 1) fun q ↦ by
        show |pageOp W 0 q.1 q.2 * armTwo W q.1 q.2| ≤ 1
        rw [abs_of_nonneg (mul_nonneg (pageOp_nonneg W le_rfl _ _)
          (armTwo_nonneg W _ _))]
        exact mul_le_one₀ (pageOp_le_one W le_rfl _ _) (armTwo_nonneg W _ _)
          (armTwo_le_one W _ _)
  rw [integral_integral hiL, integral_integral hiR]
  exact integral_mono hiL hiR fun q ↦ sq_armOne_le W q.1 q.2

/-! ### Transporting the Atlas 148 bound to the frame -/

/-- The frame copy of Atlas 148 is `Methods/Atlas148.graph148` relabelled. -/
def isoAdj : Taeyoung.Methods.Atlas148.graph148 ≃g frameAdj where
  toEquiv :=
    { toFun := ![0, 2, 3, 4, 5, 1]
      invFun := ![0, 5, 1, 2, 3, 4]
      left_inv := by decide
      right_inv := by decide }
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem homDensity_frame145_bound (W : Graphon Ω μ)
    (hp : 1 / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W * (2 * cliqueDensity 2 W - 1) ^ 2 *
        (3 * cliqueDensity 2 W ^ 2 - 3 * cliqueDensity 2 W + 1)
      ≤ homDensity frame145 W := by
  refine le_trans ?_ (homDensity_frameAdj_le W)
  rw [← homDensity_iso W isoAdj]
  exact Taeyoung.Methods.Atlas148.homDensity_graph148_bound W hp

/-! ### Chromatic data and the catalogue proposition -/

theorem s145_0 : surjCount frame145 0 = 0 := by decide +kernel
theorem s145_1 : surjCount frame145 1 = 0 := by decide +kernel
theorem s145_2 : surjCount frame145 2 = 0 := by decide +kernel
theorem s145_3 : surjCount frame145 3 = 18 := by decide +kernel
theorem s145_4 : surjCount frame145 4 = 264 := by decide +kernel
theorem s145_5 : surjCount frame145 5 = 840 := by decide +kernel

theorem s145_6 : surjCount frame145 6 = 720 := by
  rw [surjCount_card frame145]
  decide

theorem count145 (k : ℕ) :
    properAssignmentCount frame145 k
      = 18 * k.choose 3 + 264 * k.choose 4 + 840 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum frame145 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s145_0, s145_1, s145_2, s145_3, s145_4, s145_5, s145_6]
  ring

theorem num145 : IsChromaticNumber frame145 3 where
  positive := by rw [count145]; decide
  zero_below k hk := by
    rw [count145]
    interval_cases k <;> decide

theorem chrom145 : IsChromaticPolynomial frame145
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount frame145 j : ℝ) / (j).factorial) * ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount frame145

set_option maxHeartbeats 1000000 in
/-- **Atlas 145 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_145 : Taeyoung.SatisfiesLowerBound frame145 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount frame145 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := frame145) hP chrom145
  have hreq : r = 3 := IsChromaticNumber.unique (H := frame145) hr num145
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := homDensity_frame145_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount frame145 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = cliqueDensity 2 W * (2 * cliqueDensity 2 W - 1) ^ 2 *
            (3 * cliqueDensity 2 W ^ 2 - 3 * cliqueDensity 2 W + 1) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s145_0, s145_1, s145_2, s145_3, s145_4, s145_5, s145_6,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

end Taeyoung.Methods.Atlas145
