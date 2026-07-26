import PureChordal.ChromaticFactorization

/-!
# Pure chordal graphs on 4 vertices

Auto-generated certificates and `k`-partite optimality
theorems for the non-clique pure chordal graphs on 4 vertices.
-/

namespace PureChordal.Examples.G4_1

/-- Bags (maximal `K3` cliques) of a pure chordal graph on 4 vertices. -/
def bags : Fin 2 → Finset (Fin 4)
  | i => match i.1 with
    | 0 => {0, 1, 2}
    | _ => {0, 1, 3}

/-- The graph, presented as the union of its 2 maximal cliques. -/
def graph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun u v =>
    ∃ i : Fin 2, u ∈ bags i ∧ v ∈ bags i

noncomputable instance : DecidableRel graph.Adj :=
  Classical.decRel _

/-- Parent indices of a rooted clique tree. -/
def parent : Fin 2 → Fin 2
  | i => match i.1 with
    | 0 => 0
    | _ => 0

/-- The pure clique-tree certificate. -/
def decomp : PureCliqueTreeDecomp graph 3 2 where
  root := 0
  root_val := by decide
  parent := parent
  parent_lt := by decide
  parent_root := by decide
  bag := bags
  bag_card := by decide
  bag_clique := by
    intro i
    rw [SimpleGraph.isClique_iff]
    intro u hu v hv huv
    rw [graph, SimpleGraph.fromRel_adj]
    exact ⟨huv, Or.inl ⟨i, hu, hv⟩⟩
  bag_injective := by decide
  vertex_cover := by decide
  edge_cover := by
    intro u v huv
    rw [graph, SimpleGraph.fromRel_adj] at huv
    rcases huv with ⟨hne, h | h⟩
    · exact h
    · rcases h with ⟨i, hv, hu⟩
      exact ⟨i, hu, hv⟩
  old_eq_parentSeparator := by decide

/-- `k`-partite optimality: at edge density `1 - 1/k` with `3 ≤ k`, the balanced
complete `k`-partite graphon minimizes this graph's homomorphism density. -/
theorem optimality
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (k : ℕ) [NeZero k] (hrk : 3 ≤ k)
    (hp : cliqueDensity 2 W = 1 - 1 / (k : ℝ)) :
    homDensity graph (balancedMultipartiteGraphon k) ≤ homDensity graph W :=
  decomp.balancedMultipartite_minimal k W (by norm_num) hrk hp

end PureChordal.Examples.G4_1
