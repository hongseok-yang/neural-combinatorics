import Taeyoung.Foundation.ProductIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The degree function and the rooted triangle density

Six of the catalogue's methodologies condition on the image of one distinguished
vertex.  All of them are written in terms of the same two rooted quantities:

* `degree W x = ∫ W x y dμ(y)`, the degree function `d`;
* `rootedTriangle W x = ∫∫ W x y · W x z · W y z`, the triangle density `τ`
  rooted at `x`.

This file defines them and records the facts every use needs: measurability,
the pointwise bounds, and that the mean degree is the shared edge density
`cliqueDensity 2 W`.
-/

open MeasureTheory

namespace Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The degree function -/

/-- The degree function `d(x) = ∫ W(x,y) dμ(y)`. -/
noncomputable def degree (W : Graphon Ω μ) (x : Ω) : ℝ := ∫ y, W x y ∂μ

lemma measurable_degree (W : Graphon Ω μ) : Measurable (degree W) := by
  have h : StronglyMeasurable (Function.uncurry W.toFun) :=
    W.measurable.stronglyMeasurable
  exact (h.integral_prod_right' (ν := μ)).measurable

lemma degree_nonneg (W : Graphon Ω μ) (x : Ω) : 0 ≤ degree W x :=
  integral_nonneg fun y ↦ W.nonneg x y

lemma degree_le_one (W : Graphon Ω μ) (x : Ω) : degree W x ≤ 1 := by
  have hint : Integrable (fun y ↦ W x y) μ := by
    refine (integrable_const (μ := μ) (1 : ℝ)).mono'
      ((W.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (ae_of_all _ fun y ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (W.nonneg x y)]
    exact W.le_one x y
  calc degree W x ≤ ∫ _y : Ω, (1 : ℝ) ∂μ :=
        integral_mono hint (integrable_const _) fun y ↦ W.le_one x y
    _ = 1 := by simp

lemma integrable_degree (W : Graphon Ω μ) : Integrable (degree W) μ :=
  (integrable_const (μ := μ) (1 : ℝ)).mono'
    (measurable_degree W).aestronglyMeasurable
    (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (degree_nonneg W x)]
      exact degree_le_one W x)

/-! ### Mean degree is the edge density -/

/-- `K₂` has a single edge. -/
lemma edgeFinset_top_fin_two :
    (⊤ : SimpleGraph (Fin 2)).edgeFinset = {s(0, 1)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

/-- The graph weight of `K₂` reads off the two assigned coordinates. -/
lemma graphWeight_top_fin_two (W : Graphon Ω μ) (x : Fin 2 → Ω) :
    graphWeight (⊤ : SimpleGraph (Fin 2)) W x = W (x 0) (x 1) := by
  rw [graphWeight, edgeFinset_top_fin_two]
  simp

/-- **The mean degree is the shared edge density.** -/
theorem integral_degree (W : Graphon Ω μ) :
    ∫ x, degree W x ∂μ = cliqueDensity 2 W := by
  have hmeas : Measurable fun x : Fin 2 → Ω ↦
      graphWeight (⊤ : SimpleGraph (Fin 2)) W x := measurable_graphWeight _ W
  have hbdd : ∀ x : Fin 2 → Ω,
      |graphWeight (⊤ : SimpleGraph (Fin 2)) W x| ≤ 1 := fun x ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [cliqueDensity, homDensity, integral_assignmentMeasure_succ _ hmeas hbdd]
  refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
  have hmeas1 : Measurable fun y : Fin 1 → Ω ↦
      graphWeight (⊤ : SimpleGraph (Fin 2)) W (Fin.cons a y) :=
    hmeas.comp (measurable_fin_cons a)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 1 → Ω ↦ graphWeight (⊤ : SimpleGraph (Fin 2)) W (Fin.cons a y))
    hmeas1 (fun y ↦ hbdd _)]
  refine integral_congr_ae (ae_of_all _ fun b ↦ ?_)
  simp [graphWeight_top_fin_two, Fin.cons_one]

/-! ### The rooted triangle density -/

/-- The triangle density rooted at `x`,
`τ(x) = ∫∫ W(x,y) W(x,z) W(y,z) dμ(y) dμ(z)`. -/
noncomputable def rootedTriangle (W : Graphon Ω μ) (x : Ω) : ℝ :=
  ∫ y, ∫ z, W x y * W x z * W y z ∂μ ∂μ

lemma rootedTriangle_nonneg (W : Graphon Ω μ) (x : Ω) :
    0 ≤ rootedTriangle W x :=
  integral_nonneg fun y ↦ integral_nonneg fun z ↦
    mul_nonneg (mul_nonneg (W.nonneg _ _) (W.nonneg _ _)) (W.nonneg _ _)

end Taeyoung
