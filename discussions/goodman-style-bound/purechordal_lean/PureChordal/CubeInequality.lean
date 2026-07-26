import PureChordal.ProductInequalities
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# The pointwise clique cube inequality

This file instantiates the finite-product deficit inequality on the incidence
sets of a simple graph.  Every edge is counted at its two endpoints.
-/

open scoped BigOperators

namespace PureChordal

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

end PureChordal
