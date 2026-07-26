import PureChordal.CertificatePolynomialBound

/-!
# The Goldner--Harary graph

We use the standard `11`-vertex, `27`-edge presentation.  Its eight maximal
cliques are tetrahedra.  The order below is a rooted topological order for a
clique tree: bag `1` is attached to bag `0`, bags `2`, `3`, and `4` to bag `1`,
and bags `5`, `6`, and `7` to bag `2`.
-/

namespace PureChordal

/-- The eight maximal `K₄` bags of the Goldner--Harary graph. -/
def goldnerHararyBags (i : Fin 8) : Finset (Fin 11) :=
  match i.1 with
  | 0 => {0, 1, 3, 4}
  | 1 => {1, 3, 4, 10}
  | 2 => {1, 3, 7, 10}
  | 3 => {1, 4, 5, 10}
  | 4 => {3, 4, 9, 10}
  | 5 => {1, 2, 3, 7}
  | 6 => {1, 6, 7, 10}
  | _ => {3, 7, 8, 10}

/-- The Goldner--Harary graph, presented as the union of its eight maximal
tetrahedra. -/
def goldnerHararyGraph : SimpleGraph (Fin 11) :=
  SimpleGraph.fromRel fun u v =>
    ∃ i : Fin 8, u ∈ goldnerHararyBags i ∧ v ∈ goldnerHararyBags i

noncomputable instance goldnerHararyGraph_decidableAdj :
    DecidableRel goldnerHararyGraph.Adj :=
  Classical.decRel _

/-- Parent indices for the displayed rooted clique tree. -/
def goldnerHararyParent (i : Fin 8) : Fin 8 :=
  match i.1 with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 2
  | 6 => 2
  | _ => 2

/-- The explicit pure `K₄` clique-tree certificate for Goldner--Harary. -/
def goldnerHararyDecomp :
    PureCliqueTreeDecomp goldnerHararyGraph 4 8 where
  root := 0
  root_val := by decide
  parent := goldnerHararyParent
  parent_lt := by decide
  parent_root := by decide
  bag := goldnerHararyBags
  bag_card := by decide
  bag_clique := by
    intro i
    rw [SimpleGraph.isClique_iff]
    intro u hu v hv huv
    rw [goldnerHararyGraph, SimpleGraph.fromRel_adj]
    exact ⟨huv, Or.inl ⟨i, hu, hv⟩⟩
  bag_injective := by decide
  vertex_cover := by decide
  edge_cover := by
    intro u v huv
    rw [goldnerHararyGraph, SimpleGraph.fromRel_adj] at huv
    rcases huv with ⟨hne, h | h⟩
    · exact h
    · rcases h with ⟨i, hv, hu⟩
      exact ⟨i, hu, hv⟩
  old_eq_parentSeparator := by decide

@[simp] lemma goldnerHarary_root :
    goldnerHararyDecomp.root = 0 := rfl

@[simp] lemma goldnerHarary_separator_card (i : Fin 8) :
    (goldnerHararyDecomp.separator i).card =
      if i = 0 then 0 else 3 := by
  fin_cases i <;> decide

/-- A computable degree function for the bag-union presentation. -/
def goldnerHararyDegree (v : Fin 11) : ℕ :=
  (Finset.univ.filter fun u : Fin 11 ↦
    u ≠ v ∧ ∃ i : Fin 8,
      u ∈ goldnerHararyBags i ∧ v ∈ goldnerHararyBags i).card

/-- This presentation has the characteristic Goldner--Harary degree list. -/
lemma goldnerHarary_degrees :
    List.ofFn goldnerHararyDegree =
      [3, 8, 3, 8, 6, 3, 3, 6, 3, 3, 8] := by
  decide

lemma goldnerHarary_certificateBound (p : ℝ) :
    goldnerHararyDecomp.certificateBound p =
      p * (2 * p - 1) * (3 * p - 2) ^ 8 := by
  norm_num [PureCliqueTreeDecomp.certificateBound,
    PureCliqueTreeDecomp.cliquePolyTail, cliquePoly,
    Fin.prod_univ_succ, Finset.prod_range_succ, Finset.prod_Ico_succ_top,
    goldnerHarary_separator_card]
  ring

end PureChordal
