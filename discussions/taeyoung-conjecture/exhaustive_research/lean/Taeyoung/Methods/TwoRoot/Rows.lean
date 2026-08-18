import Taeyoung.Methods.TwoRoot.Core
import Taeyoung.Methods.ForestCone.Rows
import Taeyoung.Methods.BaseCone.Rows

/-!
# Two-root triangle-leaf books: the rows

Atlas 35, 93 and 112 — the scoped members of `B_{m,a,b}` — and the cone 180.

Each row is a peeling and nothing else: `Methods/TwoRoot/Core.lean` already has

```
∫∫ W·Zⁿ·H₀^m ≥ p^{n+1}(2p-1)^m,        Z = √(d(x)d(y)),
```

so a row has only to show that its density *is* that integral.  In every case
the leaves integrate to a degree and the pages to `H₀`, leaving

```
t = ∫∫ W(x,y)·d(x)^a·d(y)^b·H₀(x,y)^m.
```

`a = b` for Atlas 35 and 112, where `d(x)^a d(y)^b = (Z²)^a` on the nose.  Atlas
93 has `a = 1, b = 2`, and there the symmetry of `W` and `H₀` in `(x,y)` turns
the integral into its own symmetrisation, at which point AM–GM gives `Z³`.

The labelling puts the spine at `0,1`, then the pages, then the leaves — so that
coordinate peeling, which always removes coordinate `0`, meets the leaves first
and the spine last.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.TwoRoot

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.GeometricMean Taeyoung.Methods.ForestCone
  Taeyoung.Methods.PawCone Taeyoung.Methods.BaseCone

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Atlas 35 — the triangle with one leaf on each of two vertices -/

/-- Spine `0,1`; page `2`; leaf `3` on `0` and leaf `4` on `1`. -/
def book35 : SimpleGraph (Fin 5) :=
  graphFromEdges 5 [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4)]

instance : DecidableRel book35.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_book35 :
    book35.edgeFinset = {s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(1, 4)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_book35 (W : Graphon Ω μ) (x : Fin 5 → Ω) :
    graphWeight book35 W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
        W (x 1) (x 4) := by
  rw [graphWeight, edgeFinset_book35]
  simp
  ring

lemma graphWeight_book35_cons (W : Graphon Ω μ) (a0 a1 a2 a3 a4 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight book35 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
        (Fin.cons a3 (Fin.cons a4 y))))) =
      W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a4 := by
  rw [graphWeight_book35]
  rfl

/-- **The density of Atlas 35 is the two-root integral at `n = 2`, `m = 1`.** -/
theorem homDensity_book35 (W : Graphon Ω μ) :
    homDensity book35 W =
      ∫ a0, ∫ a1, W a0 a1 *
        (degree W a0 * degree W a1 * pageOp W 0 a0 a1) ∂μ ∂μ := by
  have hm : Measurable (graphWeight book35 W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight book35 W x| ≤ 1 := fun x ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω ↦ graphWeight book35 W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 3 → Ω ↦ graphWeight book35 W (Fin.cons a0 (Fin.cons a1 y)))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  -- the page `a2` is what is left after the two leaves have become degrees
  have hstep2 : ∀ a2 : Ω,
      (∫ y : Fin 2 → Ω,
          graphWeight book35 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)))
        ∂assignmentMeasure (Fin 2) μ) =
        (W a0 a1 * W a0 a2 * W a1 a2) * (degree W a0 * degree W a1) := by
    intro a2
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 2 → Ω ↦
        graphWeight book35 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
      (hm.comp ((measurable_fin_cons a0).comp
        ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
      fun y ↦ hb _]
    have hstep3 : ∀ a3 : Ω,
        (∫ y : Fin 1 → Ω,
            graphWeight book35 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
          ∂assignmentMeasure (Fin 1) μ) =
          (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * degree W a1 := by
      intro a3
      rw [integral_assignmentMeasure_succ
        (fun y : Fin 1 → Ω ↦ graphWeight book35 W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
        (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
          ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
        fun y ↦ hb _]
      have hval : ∀ a4 : Ω,
          (∫ y : Fin 0 → Ω, graphWeight book35 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                (Fin.cons a4 y)))))
            ∂assignmentMeasure (Fin 0) μ) =
            (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * W a1 a4 := by
        intro a4
        rw [show (∫ y : Fin 0 → Ω, graphWeight book35 W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
              (Fin.cons a4 y)))))
              ∂assignmentMeasure (Fin 0) μ) =
            W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a4 by
          simp [graphWeight_book35_cons]]
      rw [integral_congr_ae (ae_of_all _ hval), integral_const_mul]
      rfl
    rw [integral_congr_ae (ae_of_all _ hstep3)]
    have hre : ∀ a3 : Ω,
        (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * degree W a1 =
          ((W a0 a1 * W a0 a2 * W a1 a2) * degree W a1) * W a0 a3 := by
      intro a3; ring
    rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
    show _ * degree W a0 = _
    ring
  rw [integral_congr_ae (ae_of_all _ hstep2)]
  have hre : ∀ a2 : Ω,
      (W a0 a1 * W a0 a2 * W a1 a2) * (degree W a0 * degree W a1) =
        (W a0 a1 * (degree W a0 * degree W a1)) *
          (W a0 a2 * W a1 a2 * degree W a2 ^ (0 : ℝ)) := by
    intro a2
    rw [Real.rpow_zero]
    ring
  rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul, ← pageOp]
  ring

/-- **Atlas 35 dominates its target.** -/
theorem book35_bound (W : Graphon Ω μ) (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 3 * (2 * cliqueDensity 2 W - 1) ≤ homDensity book35 W := by
  have hprod : homDensity book35 W = ∫ q, pageIntegrand W 2 1 q ∂(μ.prod μ) := by
    rw [homDensity_book35]
    refine Eq.trans ?_ (integral_integral (f := fun a0 a1 ↦
      pageIntegrand W 2 1 (a0, a1)) ?_)
    · refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
      refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
      simp only [pageIntegrand]
      rw [sq_geoMean, pow_one]
    · exact (integrable_pageIntegrand W 2 1).congr (ae_of_all _ fun q ↦ rfl)
  rw [hprod]
  have h := target_le_integral_pageIntegrand W 2 1 one_pos hp
  rw [pow_one] at h
  exact h

/-! ### Atlas 93 — the triangle with one leaf on one vertex and two on another -/

/-- Spine `0,1`; page `2`; leaf `3` on `0`; leaves `4,5` on `1`. -/
def book93 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (1, 5)]

instance : DecidableRel book93.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_book93 :
    book93.edgeFinset =
      {s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(1, 4), s(1, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_book93 (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight book93 W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
        W (x 1) (x 4) * W (x 1) (x 5) := by
  rw [graphWeight, edgeFinset_book93]
  simp
  ring

lemma graphWeight_book93_cons (W : Graphon Ω μ) (a0 a1 a2 a3 a4 a5 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight book93 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
        (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y)))))) =
      W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a4 * W a1 a5 := by
  rw [graphWeight_book93]
  rfl

/-- **The density of Atlas 93.** -/
theorem homDensity_book93 (W : Graphon Ω μ) :
    homDensity book93 W =
      ∫ a0, ∫ a1, W a0 a1 *
        (degree W a0 * (degree W a1 * degree W a1) * pageOp W 0 a0 a1) ∂μ ∂μ := by
  have hm : Measurable (graphWeight book93 W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight book93 W x| ≤ 1 := fun x ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 5 → Ω ↦ graphWeight book93 W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω ↦ graphWeight book93 W (Fin.cons a0 (Fin.cons a1 y)))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  have hstep2 : ∀ a2 : Ω,
      (∫ y : Fin 3 → Ω,
          graphWeight book93 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)))
        ∂assignmentMeasure (Fin 3) μ) =
        (W a0 a1 * W a0 a2 * W a1 a2) *
          (degree W a0 * (degree W a1 * degree W a1)) := by
    intro a2
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 3 → Ω ↦
        graphWeight book93 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
      (hm.comp ((measurable_fin_cons a0).comp
        ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
      fun y ↦ hb _]
    have hstep3 : ∀ a3 : Ω,
        (∫ y : Fin 2 → Ω,
            graphWeight book93 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
          ∂assignmentMeasure (Fin 2) μ) =
          (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) *
            (degree W a1 * degree W a1) := by
      intro a3
      rw [integral_assignmentMeasure_succ
        (fun y : Fin 2 → Ω ↦ graphWeight book93 W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
        (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
          ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
        fun y ↦ hb _]
      have hstep4 : ∀ a4 : Ω,
          (∫ y : Fin 1 → Ω, graphWeight book93 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                (Fin.cons a4 y)))))
            ∂assignmentMeasure (Fin 1) μ) =
            (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a4) * degree W a1 := by
        intro a4
        rw [integral_assignmentMeasure_succ
          (fun y : Fin 1 → Ω ↦ graphWeight book93 W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
              (Fin.cons a4 y))))))
          (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
            ((measurable_fin_cons a2).comp ((measurable_fin_cons a3).comp
              (measurable_fin_cons a4))))))
          fun y ↦ hb _]
        have hval : ∀ a5 : Ω,
            (∫ y : Fin 0 → Ω, graphWeight book93 W
                (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                  (Fin.cons a4 (Fin.cons a5 y))))))
              ∂assignmentMeasure (Fin 0) μ) =
              (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a4) * W a1 a5 := by
          intro a5
          rw [show (∫ y : Fin 0 → Ω, graphWeight book93 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                (Fin.cons a4 (Fin.cons a5 y))))))
                ∂assignmentMeasure (Fin 0) μ) =
              W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a4 * W a1 a5 by
            simp [graphWeight_book93_cons]]
        rw [integral_congr_ae (ae_of_all _ hval), integral_const_mul]
        rfl
      rw [integral_congr_ae (ae_of_all _ hstep4)]
      have hre : ∀ a4 : Ω,
          (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a4) * degree W a1 =
            ((W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * degree W a1) * W a1 a4 := by
        intro a4; ring
      rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
      show _ * degree W a1 = _
      ring
    rw [integral_congr_ae (ae_of_all _ hstep3)]
    have hre : ∀ a3 : Ω,
        (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) *
            (degree W a1 * degree W a1) =
          ((W a0 a1 * W a0 a2 * W a1 a2) * (degree W a1 * degree W a1)) *
            W a0 a3 := by
      intro a3; ring
    rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
    show _ * degree W a0 = _
    ring
  rw [integral_congr_ae (ae_of_all _ hstep2)]
  have hre : ∀ a2 : Ω,
      (W a0 a1 * W a0 a2 * W a1 a2) *
          (degree W a0 * (degree W a1 * degree W a1)) =
        (W a0 a1 * (degree W a0 * (degree W a1 * degree W a1))) *
          (W a0 a2 * W a1 a2 * degree W a2 ^ (0 : ℝ)) := by
    intro a2
    rw [Real.rpow_zero]
    ring
  rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul, ← pageOp]
  ring

/-! ### Atlas 112 — the two-page book with one leaf on each spine vertex -/

/-- Spine `0,1`; pages `2,3`; leaf `4` on `0` and leaf `5` on `1`. -/
def book112 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (1, 5)]

instance : DecidableRel book112.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_book112 :
    book112.edgeFinset =
      {s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(1, 3), s(0, 4), s(1, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_book112 (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight book112 W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
        W (x 1) (x 3) * W (x 0) (x 4) * W (x 1) (x 5) := by
  rw [graphWeight, edgeFinset_book112]
  simp
  ring

lemma graphWeight_book112_cons (W : Graphon Ω μ) (a0 a1 a2 a3 a4 a5 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight book112 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
        (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y)))))) =
      W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * W a0 a4 * W a1 a5 := by
  rw [graphWeight_book112]
  rfl

/-- **The density of Atlas 112 is the two-root integral at `n = 2`, `m = 2`.** -/
theorem homDensity_book112 (W : Graphon Ω μ) :
    homDensity book112 W =
      ∫ a0, ∫ a1, W a0 a1 *
        (degree W a0 * degree W a1 *
          (pageOp W 0 a0 a1 * pageOp W 0 a0 a1)) ∂μ ∂μ := by
  have hm : Measurable (graphWeight book112 W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight book112 W x| ≤ 1 := fun x ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 5 → Ω ↦ graphWeight book112 W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω ↦ graphWeight book112 W (Fin.cons a0 (Fin.cons a1 y)))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  have hstep2 : ∀ a2 : Ω,
      (∫ y : Fin 3 → Ω,
          graphWeight book112 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)))
        ∂assignmentMeasure (Fin 3) μ) =
        (W a0 a1 * W a0 a2 * W a1 a2) *
          (degree W a0 * degree W a1 * pageOp W 0 a0 a1) := by
    intro a2
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 3 → Ω ↦
        graphWeight book112 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
      (hm.comp ((measurable_fin_cons a0).comp
        ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
      fun y ↦ hb _]
    have hstep3 : ∀ a3 : Ω,
        (∫ y : Fin 2 → Ω,
            graphWeight book112 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
          ∂assignmentMeasure (Fin 2) μ) =
          (W a0 a1 * W a0 a2 * W a1 a2) *
            (degree W a0 * degree W a1) *
              (W a0 a3 * W a1 a3 * degree W a3 ^ (0 : ℝ)) := by
      intro a3
      rw [integral_assignmentMeasure_succ
        (fun y : Fin 2 → Ω ↦ graphWeight book112 W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
        (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
          ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
        fun y ↦ hb _]
      have hstep4 : ∀ a4 : Ω,
          (∫ y : Fin 1 → Ω, graphWeight book112 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                (Fin.cons a4 y)))))
            ∂assignmentMeasure (Fin 1) μ) =
            (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * W a0 a4) *
              degree W a1 := by
        intro a4
        rw [integral_assignmentMeasure_succ
          (fun y : Fin 1 → Ω ↦ graphWeight book112 W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
              (Fin.cons a4 y))))))
          (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
            ((measurable_fin_cons a2).comp ((measurable_fin_cons a3).comp
              (measurable_fin_cons a4))))))
          fun y ↦ hb _]
        have hval : ∀ a5 : Ω,
            (∫ y : Fin 0 → Ω, graphWeight book112 W
                (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                  (Fin.cons a4 (Fin.cons a5 y))))))
              ∂assignmentMeasure (Fin 0) μ) =
              (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * W a0 a4) *
                W a1 a5 := by
          intro a5
          rw [show (∫ y : Fin 0 → Ω, graphWeight book112 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                (Fin.cons a4 (Fin.cons a5 y))))))
                ∂assignmentMeasure (Fin 0) μ) =
              W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * W a0 a4 *
                W a1 a5 by simp [graphWeight_book112_cons]]
        rw [integral_congr_ae (ae_of_all _ hval), integral_const_mul]
        rfl
      rw [integral_congr_ae (ae_of_all _ hstep4)]
      have hre : ∀ a4 : Ω,
          (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * W a0 a4) *
              degree W a1 =
            ((W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3) *
              degree W a1) * W a0 a4 := by
        intro a4; ring
      rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul,
        Real.rpow_zero]
      show _ * degree W a0 = _
      ring
    rw [integral_congr_ae (ae_of_all _ hstep3)]
    have hre : ∀ a3 : Ω,
        (W a0 a1 * W a0 a2 * W a1 a2) * (degree W a0 * degree W a1) *
            (W a0 a3 * W a1 a3 * degree W a3 ^ (0 : ℝ)) =
          ((W a0 a1 * W a0 a2 * W a1 a2) * (degree W a0 * degree W a1)) *
            (W a0 a3 * W a1 a3 * degree W a3 ^ (0 : ℝ)) := by
      intro a3; ring
    rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul, ← pageOp]
    ring
  rw [integral_congr_ae (ae_of_all _ hstep2)]
  have hre : ∀ a2 : Ω,
      (W a0 a1 * W a0 a2 * W a1 a2) *
          (degree W a0 * degree W a1 * pageOp W 0 a0 a1) =
        (W a0 a1 * (degree W a0 * degree W a1 * pageOp W 0 a0 a1)) *
          (W a0 a2 * W a1 a2 * degree W a2 ^ (0 : ℝ)) := by
    intro a2
    rw [Real.rpow_zero]
    ring
  rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul, ← pageOp]
  ring

/-- **Atlas 112 dominates its target.** -/
theorem book112_bound (W : Graphon Ω μ)
    (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 3 * (2 * cliqueDensity 2 W - 1) ^ 2 ≤
      homDensity book112 W := by
  have hprod : homDensity book112 W = ∫ q, pageIntegrand W 2 2 q ∂(μ.prod μ) := by
    rw [homDensity_book112]
    refine Eq.trans ?_ (integral_integral (f := fun a0 a1 ↦
      pageIntegrand W 2 2 (a0, a1)) ?_)
    · refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
      refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
      simp only [pageIntegrand]
      rw [sq_geoMean]
      ring
    · exact (integrable_pageIntegrand W 2 2).congr (ae_of_all _ fun q ↦ rfl)
  rw [hprod]
  exact target_le_integral_pageIntegrand W 2 2 two_pos hp

/-! ### Atlas 93's symmetrisation

`a = 1, b = 2`, so the integrand is not yet a function of `Z` alone.  It becomes
one after averaging with its transpose, which changes nothing because `W` and
`H₀` are both symmetric. -/

lemma pageOp_symm (W : Graphon Ω μ) (s : ℝ) (x y : Ω) :
    pageOp W s x y = pageOp W s y x := by
  simp only [pageOp]
  exact integral_congr_ae (ae_of_all _ fun z ↦ by ring)

/-- `W(x,y)·d(x)d(y)²·H₀(x,y)`, the density of Atlas 93. -/
noncomputable def integrand93 (W : Graphon Ω μ) (q : Ω × Ω) : ℝ :=
  W q.1 q.2 * (degree W q.1 * (degree W q.2 * degree W q.2) * pageOp W 0 q.1 q.2)

lemma measurable_integrand93 (W : Graphon Ω μ) : Measurable (integrand93 W) :=
  W.measurable.mul ((((measurable_degree W).comp measurable_fst).mul
    (((measurable_degree W).comp measurable_snd).mul
      ((measurable_degree W).comp measurable_snd))).mul
    (measurable_pageOp W le_rfl))

lemma integrand93_nonneg (W : Graphon Ω μ) (q : Ω × Ω) : 0 ≤ integrand93 W q :=
  mul_nonneg (W.nonneg _ _)
    (mul_nonneg (mul_nonneg (degree_nonneg W _)
      (mul_nonneg (degree_nonneg W _) (degree_nonneg W _)))
      (pageOp_nonneg W le_rfl _ _))

lemma integrand93_le_one (W : Graphon Ω μ) (q : Ω × Ω) : integrand93 W q ≤ 1 := by
  have h1 : degree W q.2 * degree W q.2 ≤ 1 :=
    mul_le_one₀ (degree_le_one W _) (degree_nonneg W _) (degree_le_one W _)
  have h2 : degree W q.1 * (degree W q.2 * degree W q.2) ≤ 1 :=
    mul_le_one₀ (degree_le_one W _)
      (mul_nonneg (degree_nonneg W _) (degree_nonneg W _)) h1
  exact mul_le_one₀ (W.le_one _ _)
    (mul_nonneg (mul_nonneg (degree_nonneg W _)
      (mul_nonneg (degree_nonneg W _) (degree_nonneg W _)))
      (pageOp_nonneg W le_rfl _ _))
    (mul_le_one₀ h2 (pageOp_nonneg W le_rfl _ _) (pageOp_le_one W le_rfl _ _))

lemma integrable_integrand93 (W : Graphon Ω μ) :
    Integrable (integrand93 W) (μ.prod μ) :=
  integrable_prod_of_bdd (measurable_integrand93 W) (C := 1) fun q ↦ by
    rw [abs_of_nonneg (integrand93_nonneg W q)]
    exact integrand93_le_one W q

lemma integrable_integrand93_swap (W : Graphon Ω μ) :
    Integrable (fun q : Ω × Ω ↦ integrand93 W q.swap) (μ.prod μ) :=
  integrable_prod_of_bdd ((measurable_integrand93 W).comp measurable_swap)
    (C := 1) fun q ↦ by
      show |integrand93 W q.swap| ≤ 1
      rw [abs_of_nonneg (integrand93_nonneg W q.swap)]
      exact integrand93_le_one W q.swap

/-- **The symmetrised integrand dominates `2·W·Z³·H₀`.**  `d(x)d(y)² +
d(x)²d(y) = Z²(d(x)+d(y)) ≥ 2Z³`. -/
lemma two_pageIntegrand_le (W : Graphon Ω μ) (q : Ω × Ω) :
    2 * pageIntegrand W 3 1 q ≤ integrand93 W q + integrand93 W q.swap := by
  have hsw : integrand93 W q.swap =
      W q.1 q.2 * (degree W q.2 * (degree W q.1 * degree W q.1) *
        pageOp W 0 q.1 q.2) := by
    simp only [integrand93, Prod.fst_swap, Prod.snd_swap]
    rw [W.symm, pageOp_symm]
  have hZ2 : geoMean W q ^ 2 = degree W q.1 * degree W q.2 := sq_geoMean W q
  have hAM := two_mul_geoMean_le W q
  have hAH : 0 ≤ W q.1 q.2 * pageOp W 0 q.1 q.2 :=
    mul_nonneg (W.nonneg _ _) (pageOp_nonneg W le_rfl _ _)
  have hstep : 2 * geoMean W q ^ 3 ≤
      geoMean W q ^ 2 * (degree W q.1 + degree W q.2) := by
    have h := mul_le_mul_of_nonneg_left hAM (sq_nonneg (geoMean W q))
    have he : geoMean W q ^ 2 * (2 * geoMean W q) = 2 * geoMean W q ^ 3 := by ring
    linarith
  have key : degree W q.1 * (degree W q.2 * degree W q.2) +
      degree W q.2 * (degree W q.1 * degree W q.1) =
        geoMean W q ^ 2 * (degree W q.1 + degree W q.2) := by
    rw [hZ2]; ring
  simp only [pageIntegrand, hsw, pow_one]
  calc 2 * (W q.1 q.2 * (geoMean W q ^ 3 * pageOp W 0 q.1 q.2))
      = (W q.1 q.2 * pageOp W 0 q.1 q.2) * (2 * geoMean W q ^ 3) := by ring
    _ ≤ (W q.1 q.2 * pageOp W 0 q.1 q.2) *
          (geoMean W q ^ 2 * (degree W q.1 + degree W q.2)) :=
        mul_le_mul_of_nonneg_left hstep hAH
    _ = (W q.1 q.2 * pageOp W 0 q.1 q.2) *
          (degree W q.1 * (degree W q.2 * degree W q.2) +
            degree W q.2 * (degree W q.1 * degree W q.1)) := by rw [key]
    _ = W q.1 q.2 * (degree W q.1 * (degree W q.2 * degree W q.2) *
            pageOp W 0 q.1 q.2) +
          W q.1 q.2 * (degree W q.2 * (degree W q.1 * degree W q.1) *
            pageOp W 0 q.1 q.2) := by ring

/-- **Atlas 93 dominates its target.** -/
theorem book93_bound (W : Graphon Ω μ) (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 4 * (2 * cliqueDensity 2 W - 1) ≤ homDensity book93 W := by
  have hprod : homDensity book93 W = ∫ q, integrand93 W q ∂(μ.prod μ) := by
    rw [homDensity_book93]
    exact integral_integral (f := fun a0 a1 ↦ integrand93 W (a0, a1))
      ((integrable_integrand93 W).congr (ae_of_all _ fun q ↦ rfl))
  have hsym : (∫ q, integrand93 W q.swap ∂(μ.prod μ)) =
      ∫ q, integrand93 W q ∂(μ.prod μ) := integral_prod_swap _
  have hmono : (∫ q, 2 * pageIntegrand W 3 1 q ∂(μ.prod μ)) ≤
      ∫ q, (integrand93 W q + integrand93 W q.swap) ∂(μ.prod μ) :=
    integral_mono ((integrable_pageIntegrand W 3 1).const_mul 2)
      ((integrable_integrand93 W).add (integrable_integrand93_swap W))
      (two_pageIntegrand_le W)
  rw [integral_const_mul,
    integral_add (integrable_integrand93 W) (integrable_integrand93_swap W),
    hsym] at hmono
  have hkey : cliqueDensity 2 W ^ 4 * (2 * cliqueDensity 2 W - 1) ≤
      ∫ q, pageIntegrand W 3 1 q ∂(μ.prod μ) := by
    have h := target_le_integral_pageIntegrand W 3 1 one_pos hp
    rw [pow_one] at h
    exact h
  rw [hprod]
  linarith

/-! ### Chromatic data -/

lemma affineProd_35 (z : ℝ) :
    affineProd [0, 1, 1, 1, 2] z = z ^ 3 * (2 * z - 1) := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_nil]
  ring

lemma affineProd_93 (z : ℝ) :
    affineProd [0, 1, 1, 1, 1, 2] z = z ^ 4 * (2 * z - 1) := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_cons, affineProd_nil]
  ring

lemma affineProd_112 (z : ℝ) :
    affineProd [0, 1, 1, 1, 2, 2] z = z ^ 3 * (2 * z - 1) ^ 2 := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_cons, affineProd_nil]
  ring

/-- `K₃` on the spine and the page, then the leaf on `0`, then the leaf on `1`. -/
def iso35 :
    attachVertex (attachVertex (⊤ : SimpleGraph (Fin 3)) {0}) {some 1} ≃g
      book35 where
  toEquiv := equiv40
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom35 : IsChromaticPolynomial book35
    ((([0, 1, 1, 1, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := book35) iso35
    (isClique_singleton _ (some 1))
    (isChromaticPolynomial_attachVertex (isCliqueTop _)
      (isChromaticPolynomial_top 3))
  rw [show (({0} : Finset (Fin 3)).card) = 1 from by decide,
    Finset.card_singleton] at h
  have hpoly : ((([0, 1, 1, 1, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) *
        ((X - C ((1 : ℕ) : ℝ)) * ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count35 (k : ℕ) :
    properAssignmentCount book35 k = (k - 1) * ((k - 1) * k.descFactorial 3) := by
  rw [properAssignmentCount_of_attachIso (H' := book35) iso35
      (isClique_singleton _ (some 1)) k,
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0} : Finset (Fin 3)).card) = 1 from by decide, Finset.card_singleton]

theorem num35 : IsChromaticNumber book35 3 where
  positive := by rw [count35]; decide
  zero_below k hk := by
    rw [count35, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero]

/-- `K₃`, then the leaf on `0`, then the two leaves on `1`. -/
def iso93 :
    attachVertex (attachVertex
      (attachVertex (⊤ : SimpleGraph (Fin 3)) {0}) {some 1})
      {some (some 1)} ≃g book93 where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom93 : IsChromaticPolynomial book93
    ((([0, 1, 1, 1, 1, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := book93) iso93
    (isClique_singleton _ (some (some 1)))
    (isChromaticPolynomial_attachVertex (isClique_singleton _ (some 1))
      (isChromaticPolynomial_attachVertex (isCliqueTop _)
        (isChromaticPolynomial_top 3)))
  rw [show (({0} : Finset (Fin 3)).card) = 1 from by decide,
    Finset.card_singleton, Finset.card_singleton] at h
  have hpoly :
      ((([0, 1, 1, 1, 1, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) * ((X - C ((1 : ℕ) : ℝ)) *
        ((X - C ((1 : ℕ) : ℝ)) * ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ)))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count93 (k : ℕ) :
    properAssignmentCount book93 k =
      (k - 1) * ((k - 1) * ((k - 1) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := book93) iso93
      (isClique_singleton _ (some (some 1))) k,
    properAssignmentCount_attachVertex (isClique_singleton _ (some 1)),
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0} : Finset (Fin 3)).card) = 1 from by decide,
    Finset.card_singleton, Finset.card_singleton]

theorem num93 : IsChromaticNumber book93 3 where
  positive := by rw [count93]; decide
  zero_below k hk := by
    rw [count93, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero, Nat.mul_zero]

/-- `K₃` on the spine and one page, the second page on the spine edge, then one
leaf on each spine vertex. -/
def iso112 :
    attachVertex (attachVertex
      (attachVertex (⊤ : SimpleGraph (Fin 3)) {0, 1}) {some 0})
      {some (some 1)} ≃g book112 where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom112 : IsChromaticPolynomial book112
    ((([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := book112) iso112
    (isClique_singleton _ (some (some 1)))
    (isChromaticPolynomial_attachVertex (isClique_singleton _ (some 0))
      (isChromaticPolynomial_attachVertex (isCliqueTop _)
        (isChromaticPolynomial_top 3)))
  rw [show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide,
    Finset.card_singleton, Finset.card_singleton] at h
  have hpoly :
      ((([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) * ((X - C ((1 : ℕ) : ℝ)) *
        ((X - C ((2 : ℕ) : ℝ)) * ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ)))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count112 (k : ℕ) :
    properAssignmentCount book112 k =
      (k - 1) * ((k - 1) * ((k - 2) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := book112) iso112
      (isClique_singleton _ (some (some 1))) k,
    properAssignmentCount_attachVertex (isClique_singleton _ (some 0)),
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide,
    Finset.card_singleton, Finset.card_singleton]

theorem num112 : IsChromaticNumber book112 3 where
  positive := by rw [count112]; decide
  zero_below k hk := by
    rw [count112, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero, Nat.mul_zero]

/-! ### The catalogue propositions -/

private lemma half_le_of_admissible {W : Graphon Ω μ}
    (hadm : admissibleDensity 3 (edgeDensity W)) :
    (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
  have h := hadm
  norm_num [admissibleDensity, edgeDensity] at h
  linarith

/-- **Atlas 35 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_35 : Taeyoung.SatisfiesLowerBound book35 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = (([0, 1, 1, 1, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := book35) hP chrom35
  have hreq : r = 3 := IsChromaticNumber.unique (H := book35) hr num35
  subst hPeq
  subst hreq
  have hkey := book35_bound W (half_le_of_admissible hadm)
  change Taeyoung.chromaticTarget (V := Fin 5) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 1, 2] (by norm_num) hone,
      affineProd_35]
    exact hkey

/-- **Atlas 93 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_93 : Taeyoung.SatisfiesLowerBound book93 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P =
      (([0, 1, 1, 1, 1, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := book93) hP chrom93
  have hreq : r = 3 := IsChromaticNumber.unique (H := book93) hr num93
  subst hPeq
  subst hreq
  have hkey := book93_bound W (half_le_of_admissible hadm)
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 1, 1, 2] (by norm_num) hone,
      affineProd_93]
    exact hkey

/-- **Atlas 112 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_112 : Taeyoung.SatisfiesLowerBound book112 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P =
      (([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := book112) hP chrom112
  have hreq : r = 3 := IsChromaticNumber.unique (H := book112) hr num112
  subst hPeq
  subst hreq
  have hkey := book112_bound W (half_le_of_admissible hadm)
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 1, 2, 2] (by norm_num) hone,
      affineProd_112]
    exact hkey

/-! ### Atlas 180 — the cone over Atlas 35 -/

theorem base_35 {Ω' : Type} [MeasurableSpace Ω'] {ν : Measure Ω'}
    [IsProbabilityMeasure ν] (V : Graphon Ω' ν)
    (hz : 1 - 1 / (2 : ℝ) ≤ cliqueDensity 2 V) :
    affineProd [0, 1, 1, 1, 2] (cliqueDensity 2 V) ≤ homDensity book35 V := by
  have hhalf : (1 : ℝ) / 2 ≤ cliqueDensity 2 V := by norm_num at hz; linarith
  rw [affineProd_35]
  exact book35_bound V hhalf

/-- `K₄` on `{0,1,2,3}`, with `4` on the edge `{0,1}` and `5` on `{0,2}`. -/
def equiv180 : Option (Option (Fin 4)) ≃ Fin 6 where
  toFun a := match a with
    | none => 5
    | some none => 4
    | some (some i) => ![0, 1, 2, 3] i
  invFun j := ![some (some 0), some (some 1), some (some 2), some (some 3),
    some none, none] j
  left_inv := by decide
  right_inv := by decide

def iso180 :
    attachVertex (attachVertex (⊤ : SimpleGraph (Fin 4)) {0, 1})
      {some 0, some 2} ≃g coneGraph book35 where
  toEquiv := equiv180
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom180 : IsChromaticPolynomial (coneGraph book35)
    ((((0 : ℝ) :: ([0, 1, 1, 1, 2] : List ℝ).map (· + 1)).map fun k ↦
      (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := coneGraph book35) iso180
    (isClique_attach_pair {0, 1} (by decide))
    (isChromaticPolynomial_attachVertex (isCliqueTop _)
      (isChromaticPolynomial_top 4))
  rw [show (({0, 1} : Finset (Fin 4)).card) = 2 from by decide,
    show (({some 0, some 2} : Finset (Option (Fin 4))).card) = 2 from by decide] at h
  rw [show ((0 : ℝ) :: ([0, 1, 1, 1, 2] : List ℝ).map (· + 1)) =
    [0, 1, 2, 2, 2, 3] from by norm_num]
  have hpoly : ((([0, 1, 2, 2, 2, 3] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((2 : ℕ) : ℝ)) *
        ((X - C ((2 : ℕ) : ℝ)) * ∏ i ∈ range 4, ((X : ℝ[X]) - C (i : ℝ))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count180 (k : ℕ) :
    properAssignmentCount (coneGraph book35) k =
      (k - 2) * ((k - 2) * k.descFactorial 4) := by
  rw [properAssignmentCount_of_attachIso (H' := coneGraph book35) iso180
      (isClique_attach_pair {0, 1} (by decide)) k,
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0, 1} : Finset (Fin 4)).card) = 2 from by decide,
    show (({some 0, some 2} : Finset (Option (Fin 4))).card) = 2 from by decide]

theorem num180 : IsChromaticNumber (coneGraph book35) 4 where
  positive := by rw [count180]; decide
  zero_below k hk := by
    rw [count180, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero]

/-- **Atlas 180 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_180 :
    Taeyoung.SatisfiesLowerBound (coneGraph book35) :=
  satisfiesLowerBound_of_baseCone (h := 3) book35 [0, 1, 1, 1, 2]
    (kmax := 2) (r := 4) rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) chrom180 num180 (by norm_num) base_35

end Taeyoung.Methods.TwoRoot
