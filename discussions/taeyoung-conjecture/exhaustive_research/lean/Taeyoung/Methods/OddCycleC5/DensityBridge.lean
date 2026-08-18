import Taeyoung.Foundation
import Taeyoung.Foundation.ProductIntegral
import Taeyoung.Methods.OddCycleC5.Main

/-!
# Bridging the `C₅` development to the shared density layer

`Methods/OddCycleC5` states its inequality in an operator language:
`Internal.edgeDensity` is the mean degree, and `Internal.cycleDensity` is the
trace of an iterated kernel composition.  The shared foundation instead uses
`cliqueDensity 2 W` and `homDensity H W`, integrals over the finite product
measure `assignmentMeasure V μ`.

This file identifies the two, using the coordinate-peeling lemma
`integral_assignmentMeasure_succ`.
-/

open MeasureTheory

namespace Taeyoung.Methods.OddCycleC5

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Edge-density bridge.**  The mean degree of the `C₅` development is the
edge density of the shared foundation.  Both sides are `∫∫ W`, so this is the
foundation's `integral_degree` read through the method's vocabulary. -/
theorem edgeDensity_bridge (W : Taeyoung.Graphon Ω μ) :
    Internal.edgeDensity W.toFun μ = cliqueDensity 2 W :=
  integral_degree W

/-! ### The five-cycle -/

/-- The five-cycle, on the same edge list the Atlas module uses. -/
def c5 : SimpleGraph (Fin 5) :=
  graphFromEdges 5 [(0, 1), (0, 4), (1, 2), (2, 3), (3, 4)]

instance : DecidableRel c5.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_c5 :
    c5.edgeFinset = {s(0, 1), s(0, 4), s(1, 2), s(2, 3), s(3, 4)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

/-- The graph weight of the five-cycle, read off the five assigned coordinates. -/
lemma graphWeight_c5 (W : Taeyoung.Graphon Ω μ) (x : Fin 5 → Ω) :
    graphWeight c5 W x =
      W (x 0) (x 1) * W (x 0) (x 4) * W (x 1) (x 2) * W (x 2) (x 3) *
        W (x 3) (x 4) := by
  rw [graphWeight, edgeFinset_c5]
  simp
  ring

/-- The five-cycle weight on an explicitly built assignment. -/
lemma graphWeight_c5_cons (W : Taeyoung.Graphon Ω μ) (a0 a1 a2 a3 a4 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight c5 W
        (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y))))) =
      W a0 a1 * W a0 a4 * W a1 a2 * W a2 a3 * W a3 a4 := by
  rw [graphWeight_c5]
  rfl

/-- The five-cycle hom density as an iterated integral. -/
theorem homDensity_c5_iterated (W : Taeyoung.Graphon Ω μ) :
    homDensity c5 W =
      ∫ a0, ∫ a1, ∫ a2, ∫ a3, ∫ a4,
        W a0 a1 * W a0 a4 * W a1 a2 * W a2 a3 * W a3 a4 ∂μ ∂μ ∂μ ∂μ ∂μ := by
  have hm : Measurable (graphWeight c5 W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight c5 W x| ≤ 1 := fun x ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω ↦ graphWeight c5 W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) (fun y ↦ hb _)]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 3 → Ω ↦ graphWeight c5 W (Fin.cons a0 (Fin.cons a1 y)))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1))) (fun y ↦ hb _)]
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 2 → Ω ↦ graphWeight c5 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
    (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp (measurable_fin_cons a2)))) (fun y ↦ hb _)]
  refine integral_congr_ae (ae_of_all _ fun a3 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 1 → Ω ↦ graphWeight c5 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
    (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp ((measurable_fin_cons a2).comp (measurable_fin_cons a3))))) (fun y ↦ hb _)]
  refine integral_congr_ae (ae_of_all _ fun a4 ↦ ?_)
  simp [graphWeight_c5_cons]

/-- The trace of the four-fold kernel composition as an iterated integral. -/
theorem cycleDensity_five_iterated (W : Taeyoung.Graphon Ω μ) :
    Internal.cycleDensity μ W.toFun 5 =
      ∫ a0, ∫ a1, ∫ a2, ∫ a3, ∫ a4,
        W a0 a1 * W a1 a2 * W a2 a3 * W a3 a4 * W a4 a0 ∂μ ∂μ ∂μ ∂μ ∂μ := by
  simp only [Internal.cycleDensity, Internal.trace, Internal.compPow,
    Internal.comp]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  rw [← mul_assoc, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun a3 ↦ ?_)
  simp only []
  rw [← mul_assoc, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun a4 ↦ ?_)
  simp only []
  ring

/-- **Cycle-density bridge.**  The operator-language five-cycle density of the
`C₅` development is the shared foundation's homomorphism density. -/
theorem cycleDensity_bridge (W : Taeyoung.Graphon Ω μ) :
    Internal.cycleDensity μ W.toFun 5 = homDensity c5 W := by
  rw [cycleDensity_five_iterated, homDensity_c5_iterated]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a3 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a4 ↦ ?_)
  simp only []
  rw [W.symm a4 a0]
  ring

/-- **The checked `C₅` bound, in the shared density language.**

This is `c5_shortCycle_bound` with both of its density symbols replaced by the
foundation's: `homDensity` of the five-cycle, and `cliqueDensity 2` for the edge
density.  Nothing analytic is added here — only the two bridges. -/
theorem c5_homDensity_bound (W : Taeyoung.Graphon Ω μ) :
    cliqueDensity 2 W ^ 5 -
        cliqueDensity 2 W * (1 - cliqueDensity 2 W) ^ 4 ≤
      homDensity c5 W := by
  have h := c5_shortCycle_bound W
  rw [ge_iff_le, cycleDensity_bridge, edgeDensity_bridge] at h
  exact h

end Taeyoung.Methods.OddCycleC5
