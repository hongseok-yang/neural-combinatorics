import PureChordal.CertificatePolynomialBound

/-!
# The diamond graph

The diamond is `K₄` with one edge removed.  It is the union of the triangles
`{0,1,2}` and `{0,1,3}`, glued along the edge `{0,1}`.
-/

namespace PureChordal

def diamondBags (i : Fin 2) : Finset (Fin 4) :=
  if i = 0 then {0, 1, 2} else {0, 1, 3}

def diamondGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun u v =>
    ∃ i : Fin 2, u ∈ diamondBags i ∧ v ∈ diamondBags i

noncomputable instance diamondGraph_decidableAdj : DecidableRel diamondGraph.Adj :=
  Classical.decRel _

lemma diamondGraph_adj_iff (u v : Fin 4) :
    diamondGraph.Adj u v ↔
      u ≠ v ∧ ¬ ((u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2)) := by
  rw [diamondGraph, SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> decide

/-- The two-triangle pure clique-tree certificate for the diamond. -/
def diamondDecomp : PureCliqueTreeDecomp diamondGraph 3 2 where
  root := 0
  root_val := by decide
  parent := fun _ => 0
  parent_lt := by decide
  parent_root := by decide
  bag := diamondBags
  bag_card := by decide
  bag_clique := by
    intro i
    rw [SimpleGraph.isClique_iff]
    intro u hu v hv huv
    rw [diamondGraph, SimpleGraph.fromRel_adj]
    exact ⟨huv, Or.inl ⟨i, hu, hv⟩⟩
  bag_injective := by decide
  vertex_cover := by decide
  edge_cover := by
    intro u v huv
    rw [diamondGraph, SimpleGraph.fromRel_adj] at huv
    rcases huv with ⟨hne, h | h⟩
    · exact h
    · rcases h with ⟨i, hv, hu⟩
      exact ⟨i, hu, hv⟩
  old_eq_parentSeparator := by decide

@[simp] lemma diamond_root :
    diamondDecomp.root = 0 := rfl

@[simp] lemma diamond_separator_zero_card :
    (diamondDecomp.separator 0).card = 0 := by
  decide

@[simp] lemma diamond_separator_one_card :
    (diamondDecomp.separator 1).card = 2 := by
  decide

lemma diamond_certificateBound (p : ℝ) :
    diamondDecomp.certificateBound p = p * (2 * p - 1) ^ 2 := by
  norm_num [PureCliqueTreeDecomp.certificateBound,
    PureCliqueTreeDecomp.cliquePolyTail,
    cliquePoly, Finset.prod_range_succ, Finset.prod_Ico_succ_top,
    diamond_separator_one_card]
  ring

end PureChordal
