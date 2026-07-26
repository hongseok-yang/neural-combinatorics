import PureChordal.CubeInequality
import PureChordal.HomDensity
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# The integrated graph cube inequality

This file lifts the pointwise cube inequality to homomorphism densities.  The
result remains completely general: no clique symmetry is used here.
-/

open MeasureTheory
open scoped BigOperators

namespace PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

abbrev deleteOneEdge {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (e : Sym2 V) : SimpleGraph V :=
  G.deleteEdges (({e} : Finset (Sym2 V)) : Set (Sym2 V))

lemma graphWeight_deleteOneEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Graphon Ω μ) (e : Sym2 V) (x : V → Ω) :
    graphWeight (deleteOneEdge G e) W x =
      ∏ f ∈ G.edgeFinset.erase e, edgeValue W x f := by
  unfold graphWeight
  rw [SimpleGraph.edgeFinset_deleteEdges, Finset.sdiff_singleton_eq_erase]

lemma graphWeight_deleteIncidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Graphon Ω μ) (v : V) (x : V → Ω) :
    graphWeight (G.deleteIncidenceSet v) W x =
      ∏ f ∈ G.edgeFinset \ G.incidenceFinset v, edgeValue W x f := by
  unfold graphWeight
  rw [SimpleGraph.edgeFinset_deleteIncidenceSet_eq_sdiff]

theorem integrated_graph_edge_cube_inequality
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Graphon Ω μ) :
    2 * (∑ e ∈ G.edgeFinset, homDensity (deleteOneEdge G e) W) ≤
      (∑ v : V, homDensity (G.deleteIncidenceSet v) W) +
        (2 * (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)) *
          homDensity G W := by
  classical
  let L : (V → Ω) → ℝ := fun x =>
    2 * ∑ e ∈ G.edgeFinset, graphWeight (deleteOneEdge G e) W x
  let R : (V → Ω) → ℝ := fun x =>
    (∑ v : V, graphWeight (G.deleteIncidenceSet v) W x) +
      (2 * (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)) *
        graphWeight G W x
  have hL : Integrable L (assignmentMeasure V μ) := by
    dsimp [L]
    exact (integrable_finsetSum G.edgeFinset fun e _ =>
      integrable_graphWeight (deleteOneEdge G e) W).const_mul 2
  have hR : Integrable R (assignmentMeasure V μ) := by
    dsimp [R]
    exact (integrable_finsetSum Finset.univ fun v _ =>
      integrable_graphWeight (G.deleteIncidenceSet v) W).add
        ((integrable_graphWeight G W).const_mul
          (2 * (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)))
  have hpoint : ∀ x, L x ≤ R x := by
    intro x
    dsimp [L, R]
    simp_rw [graphWeight_deleteOneEdge, graphWeight_deleteIncidence]
    simpa only [graphWeight] using
      (graph_edge_cube_inequality G (fun e => edgeValue W x e)
        (fun e he => edgeValue_nonneg W x e)
        (fun e he => edgeValue_le_one W x e))
  have h := integral_mono hL hR hpoint
  dsimp [L, R] at h
  rw [integral_const_mul,
    integral_finsetSum G.edgeFinset
      (fun e _ => integrable_graphWeight (deleteOneEdge G e) W),
    integral_add
      (integrable_finsetSum Finset.univ fun v _ =>
        integrable_graphWeight (G.deleteIncidenceSet v) W)
      ((integrable_graphWeight G W).const_mul
        (2 * (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ))),
    integral_finsetSum Finset.univ
      (fun v _ => integrable_graphWeight (G.deleteIncidenceSet v) W),
    integral_const_mul] at h
  simpa [homDensity] using h

end PureChordal
