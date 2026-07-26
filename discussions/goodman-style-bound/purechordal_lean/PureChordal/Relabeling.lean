import PureChordal.HomDensity
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Coordinate relabeling

Finite product measure is invariant under a permutation of the coordinates.
Consequently homomorphism density is invariant under graph isomorphism.
-/

open MeasureTheory
open scoped BigOperators

namespace PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V V' : Type*} [Fintype V] [DecidableEq V]
  [Fintype V'] [DecidableEq V']
variable {H : SimpleGraph V} {H' : SimpleGraph V'}
  [DecidableRel H.Adj] [DecidableRel H'.Adj]

lemma edgeValue_iso (W : Graphon Ω μ) (φ : H ≃g H')
    (x : V' → Ω) (e : Sym2 V) :
    edgeValue W (fun v ↦ x (φ v)) e =
      edgeValue W x (e.map φ) := by
  induction e using Sym2.inductionOn with
  | _ u v => simp

lemma graphWeight_eq_prod_edgeSet
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Graphon Ω μ) (x : V → Ω) :
    graphWeight G W x = ∏ e : G.edgeSet, edgeValue W x e.1 := by
  unfold graphWeight
  exact Finset.prod_subtype G.edgeFinset
    (fun e ↦ G.mem_edgeFinset) (fun e ↦ edgeValue W x e)

lemma graphWeight_iso (W : Graphon Ω μ) (φ : H ≃g H') (x : V' → Ω) :
    graphWeight H W (fun v ↦ x (φ v)) = graphWeight H' W x := by
  rw [graphWeight_eq_prod_edgeSet, graphWeight_eq_prod_edgeSet]
  rw [← φ.mapEdgeSet.prod_comp]
  apply Fintype.prod_congr
  intro e
  exact edgeValue_iso W φ x e.1

/-- Homomorphism density is invariant under graph isomorphism. -/
theorem homDensity_iso (W : Graphon Ω μ) (φ : H ≃g H') :
    homDensity H W = homDensity H' W := by
  let q : (V' → Ω) ≃ᵐ (V → Ω) :=
    MeasurableEquiv.piCongrLeft (fun _ : V ↦ Ω) φ.toEquiv.symm
  have hq : MeasurePreserving q (assignmentMeasure V' μ) (assignmentMeasure V μ) := by
    simpa [q, assignmentMeasure] using
      (measurePreserving_piCongrLeft
        (α := fun _ : V ↦ Ω) (fun _ : V ↦ μ) φ.toEquiv.symm)
  rw [homDensity, homDensity, ← hq.integral_comp']
  apply integral_congr_ae
  filter_upwards [] with x
  change graphWeight H W (q x) = graphWeight H' W x
  have hqx : q x = fun v ↦ x (φ v) := by
    funext v
    simp [q, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [hqx]
  exact graphWeight_iso W φ x

end PureChordal
