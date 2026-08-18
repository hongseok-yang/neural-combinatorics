import Taeyoung.Methods.PureChordal.Certificate
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Chordal graphs via the clique-tree characterization

Mathlib currently has no chordal-graph API.  For finite graphs we use the
standard equivalent clique-tree characterization as the formal definition:
the maximal cliques admit a rooted topological order in which the vertices of
each new clique already seen are exactly its intersection with its parent.

Keeping this structure separate from `PureCliqueTreeDecomp` makes the logical
wrapper explicit.  Chordality supplies maximal-clique bags; the purity
hypothesis supplies their common cardinality.
-/

namespace Taeyoung.Methods.PureChordal

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A rooted clique-tree presentation of all maximal cliques of a finite graph.
This is the clique-tree characterization of chordality. -/
structure MaximalCliqueTreeDecomp (H : SimpleGraph V) (m : ℕ) where
  root : Fin m
  root_val : root.val = 0
  parent : Fin m → Fin m
  parent_lt : ∀ i, i ≠ root → (parent i).val < i.val
  parent_root : parent root = root
  bag : Fin m → Finset V
  bag_maximal : ∀ i, Maximal H.IsClique (bag i : Set V)
  bag_injective : Function.Injective bag
  maximal_cover :
    ∀ C : Finset V, Maximal H.IsClique (C : Set V) → ∃ i, bag i = C
  vertex_cover : ∀ v, ∃ i, v ∈ bag i
  edge_cover : ∀ ⦃u v⦄, H.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i
  old_eq_parentSeparator :
    ∀ i, i ≠ root →
      bag i ∩ ((Finset.univ.filter fun j : Fin m ↦ j.val < i.val).biUnion bag)
        = bag i ∩ bag (parent i)

/-- Chordality, formalized by the standard maximal-clique-tree
characterization. -/
def IsChordal (H : SimpleGraph V) : Prop :=
  ∃ m : ℕ, Nonempty (MaximalCliqueTreeDecomp H m)

/-- All maximal cliques have the common size `r`. -/
def HasPureMaximalCliques (H : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ C : Finset V, Maximal H.IsClique (C : Set V) → C.card = r

namespace MaximalCliqueTreeDecomp

variable {H : SimpleGraph V} {m r : ℕ}

/-- Forget maximality and use the common maximal-clique size to obtain the
certificate required by the analytic proof. -/
def toPureCliqueTreeDecomp
    (D : MaximalCliqueTreeDecomp H m)
    (hpure : HasPureMaximalCliques H r) :
    PureCliqueTreeDecomp H r m where
  root := D.root
  root_val := D.root_val
  parent := D.parent
  parent_lt := D.parent_lt
  parent_root := D.parent_root
  bag := D.bag
  bag_card i := hpure (D.bag i) (D.bag_maximal i)
  bag_clique i := (D.bag_maximal i).1
  bag_injective := D.bag_injective
  vertex_cover := D.vertex_cover
  edge_cover := D.edge_cover
  old_eq_parentSeparator := D.old_eq_parentSeparator

end MaximalCliqueTreeDecomp

namespace IsChordal

variable {H : SimpleGraph V}

/-- Number of bags in a chosen clique-tree witness. -/
noncomputable def numBags (hH : IsChordal H) : ℕ :=
  Classical.choose hH

/-- A chosen maximal-clique-tree witness. -/
noncomputable def decomp (hH : IsChordal H) :
    MaximalCliqueTreeDecomp H hH.numBags :=
  Classical.choice (Classical.choose_spec hH)

/-- The pure certificate canonically chosen from chordality and uniform
maximal-clique size. -/
noncomputable def pureDecomp
    (hH : IsChordal H) (hpure : HasPureMaximalCliques H r) :
    PureCliqueTreeDecomp H r hH.numBags :=
  hH.decomp.toPureCliqueTreeDecomp hpure

end IsChordal

end Taeyoung.Methods.PureChordal
