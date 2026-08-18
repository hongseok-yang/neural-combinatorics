import Taeyoung.Methods.PureChordal.ChromaticFactorization

/-!
# Single-bag clique certificates

A complete graph is its own unique maximal clique, so its rooted clique tree
has exactly one bag and no separator.  This file supplies that degenerate
certificate uniformly in `n`; the Atlas clique rows instantiate it at
`n = 3, 4, 5, 6`.

The generated certificates in `N4`/`N5`/`N6` cover only the *non-clique* pure
chordal graphs, so this file is what completes the pure-chordal layer.
-/

namespace Taeyoung.Methods.PureChordal.Certificates

/-- The one-bag rooted clique-tree certificate of the complete graph `K n`.

Every hypothesis is degenerate: the single bag is all of `Fin n`, it is a clique
because the graph is `⊤`, and both `parent_lt` and `old_eq_parentSeparator` are
vacuous because `Fin 1` has no index other than the root. -/
def cliqueDecomp (n : ℕ) :
    PureCliqueTreeDecomp (⊤ : SimpleGraph (Fin n)) n 1 where
  root := 0
  root_val := rfl
  parent := id
  parent_lt := by
    intro i hi
    exact absurd (Subsingleton.elim i 0) hi
  parent_root := rfl
  bag := fun _ => Finset.univ
  bag_card := by simp
  bag_clique := by
    intro _
    rw [SimpleGraph.isClique_iff]
    intro u _ v _ huv
    simpa using huv
  bag_injective := fun a b _ => Subsingleton.elim a b
  vertex_cover := fun v => ⟨0, Finset.mem_univ v⟩
  edge_cover := by
    intro u v _
    exact ⟨0, Finset.mem_univ u, Finset.mem_univ v⟩
  old_eq_parentSeparator := by
    intro i hi
    exact absurd (Subsingleton.elim i 0) hi

end Taeyoung.Methods.PureChordal.Certificates
