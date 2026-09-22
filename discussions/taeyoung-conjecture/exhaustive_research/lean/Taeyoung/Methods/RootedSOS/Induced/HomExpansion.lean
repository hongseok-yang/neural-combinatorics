import Taeyoung.Methods.RootedSOS.Induced.Relabeling

/-! Expand an ordinary graph into induced completions of its unspecified edges. -/

open Finset MeasureTheory
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS.Induced

variable {E F U V : Type*} [Fintype E] [Fintype F] [Fintype U] [Fintype V]
  [DecidableEq E] [DecidableEq F] [DecidableEq U] [DecidableEq V]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem graphWeight_pairEnumeration (H : SimpleGraph V) [DecidableRel H.Adj]
    (pairs : F → V × V)
    (hinj : Function.Injective fun i => s((pairs i).1,(pairs i).2))
    (hedges : H.edgeFinset = univ.image (fun i => s((pairs i).1,(pairs i).2)))
    (W : Taeyoung.Graphon Ω μ) (z : V → Ω) :
    Taeyoung.graphWeight H W z = ∏ i, W (z (pairs i).1) (z (pairs i).2) := by
  rw [Taeyoung.graphWeight, hedges, Finset.prod_image (fun i _ j _ h => hinj h)]
  apply Finset.prod_congr rfl
  intro i _
  exact Taeyoung.edgeValue_mk W z _ _

theorem homDensity_completions (H : SimpleGraph V) [DecidableRel H.Adj]
    (pairs : E → V × V) (e : F ⊕ U ≃ E)
    (hinj : Function.Injective fun i : F => s((pairs (e (.inl i))).1,(pairs (e (.inl i))).2))
    (hedges : H.edgeFinset = univ.image
      (fun i : F => s((pairs (e (.inl i))).1,(pairs (e (.inl i))).2)))
    (W : Taeyoung.Graphon Ω μ) :
    Taeyoung.homDensity H W =
      ∑ q : U → Fin 2, inducedDensity pairs (fun i => Sum.elim (fun _ => 1) q (e.symm i)) W := by
  simp only [inducedDensity]
  rw [← integral_finsetSum _ (fun q _ => integrable_inducedWeight _ _ W)]
  unfold Taeyoung.homDensity
  apply integral_congr_ae
  filter_upwards [] with z
  rw [graphWeight_pairEnumeration H (fun i : F => pairs (e (.inl i))) hinj hedges W z]
  simp only [inducedWeight]
  rw [patternWeight_completions]
  simp [patternWeight, bitWeight]

end Taeyoung.Methods.RootedSOS.Induced
