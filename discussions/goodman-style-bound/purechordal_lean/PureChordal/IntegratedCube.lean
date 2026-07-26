import PureChordal.ProductInequalities
import PureChordal.HomDensity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# The graph cube inequality

This file proves the pointwise clique cube inequality on a graph's incidence
sets and lifts it to homomorphism densities.  The result remains completely
general: no clique symmetry is used here.
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

/-- Every edge is counted at its two endpoints, so summing an edge weight over
all vertex incidence sets doubles the total. -/
lemma sum_incidenceFinset_eq_two_mul_sum_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : Sym2 V → ℝ) :
    (∑ v, ∑ e ∈ G.incidenceFinset v, f e)
      = 2 * ∑ e ∈ G.edgeFinset, f e := by
  classical
  calc
    (∑ v, ∑ e ∈ G.incidenceFinset v, f e)
        =
      ∑ v, ∑ e ∈ G.edgeFinset,
        if v ∈ e then f e else 0 := by
          apply Finset.sum_congr rfl
          intro v _
          rw [G.incidenceFinset_eq_filter, Finset.sum_filter]
    _ = ∑ e ∈ G.edgeFinset, ∑ v, if v ∈ e then f e else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ e ∈ G.edgeFinset, 2 * f e := by
          apply Finset.sum_congr rfl
          intro e he
          have hcard : e.toFinset.card = 2 :=
            G.card_toFinset_mem_edgeFinset ⟨e, he⟩
          have hfilter :
              (Finset.univ.filter fun v : V ↦ v ∈ e) = e.toFinset := by
            ext v
            simp
          rw [← Finset.sum_filter, hfilter]
          simp [hcard]
    _ = 2 * ∑ e ∈ G.edgeFinset, f e := by
          rw [Finset.mul_sum]

/-- The pointwise clique cube inequality: the finite-product deficit inequality
instantiated on the incidence sets of a simple graph. -/
theorem graph_edge_cube_inequality
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : Sym2 V → ℝ)
    (ha0 : ∀ e ∈ G.edgeFinset, 0 ≤ a e)
    (ha1 : ∀ e ∈ G.edgeFinset, a e ≤ 1) :
    2 * (∑ e ∈ G.edgeFinset, ∏ f ∈ G.edgeFinset.erase e, a f)
      ≤
    (∑ v, ∏ f ∈ G.edgeFinset \ G.incidenceFinset v, a f) +
      (2 * (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)) *
        ∏ f ∈ G.edgeFinset, a f := by
  classical
  exact two_mul_sum_prod_erase_le_vertex_deleted_sum
    G.edgeFinset (fun v ↦ G.incidenceFinset v)
    (fun v ↦ G.incidenceFinset_subset v)
    (sum_incidenceFinset_eq_two_mul_sum_edges G)
    a ha0 ha1

/-- The integrated cube inequality: the pointwise graph cube inequality averaged
over the assignment measure, stated with homomorphism densities of the
edge-deleted and vertex-deleted graphs.  No clique symmetry is used. -/
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
