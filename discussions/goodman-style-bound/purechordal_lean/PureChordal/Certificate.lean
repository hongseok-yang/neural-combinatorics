import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold

/-!
# A rooted pure clique-tree certificate

The analytic theorem is first stated for an explicit certificate.  We use a
rooted topological ordering of the bags (`Fin m`) rather than Mathlib's path API.
The field `old_eq_parentSeparator` is the rooted form of running intersection:
the vertices of a non-root bag that occurred in an earlier bag are exactly its
intersection with its parent.
-/

open scoped BigOperators

namespace PureChordal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A rooted, topologically ordered clique-tree decomposition into `r`-cliques. -/
structure PureCliqueTreeDecomp (H : SimpleGraph V) (r m : ℕ) where
  root : Fin m
  root_val : root.val = 0
  parent : Fin m → Fin m
  parent_lt : ∀ i, i ≠ root → (parent i).val < i.val
  parent_root : parent root = root
  bag : Fin m → Finset V
  bag_card : ∀ i, (bag i).card = r
  bag_clique : ∀ i, H.IsClique (bag i : Set V)
  bag_injective : Function.Injective bag
  vertex_cover : ∀ v, ∃ i, v ∈ bag i
  edge_cover : ∀ ⦃u v⦄, H.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i
  old_eq_parentSeparator :
    ∀ i, i ≠ root →
      bag i ∩ ((Finset.univ.filter fun j : Fin m ↦ j.val < i.val).biUnion bag)
        = bag i ∩ bag (parent i)

namespace PureCliqueTreeDecomp

variable {H : SimpleGraph V} {r m : ℕ} (D : PureCliqueTreeDecomp H r m)

/-- All vertices appearing in a strictly earlier bag. -/
def previousVertices (i : Fin m) : Finset V :=
  (Finset.univ.filter fun j : Fin m ↦ j.val < i.val).biUnion D.bag

/-- Bag indices whose numerical value is strictly below `n`. -/
def bagIndicesLT (_D : PureCliqueTreeDecomp H r m)
    (n : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i : Fin m ↦ i.val < n

/-- Vertices exposed by all bags with index strictly below `n`. -/
def accumulatedVerticesLT (n : ℕ) : Finset V :=
  (D.bagIndicesLT n).biUnion D.bag

/-- The separator from a bag to its parent; the root separator is empty. -/
def separator (i : Fin m) : Finset V :=
  if i = D.root then ∅ else D.bag i ∩ D.bag (D.parent i)

/-- The size of the parent separator. -/
def sepCard (i : Fin m) : ℕ :=
  (D.separator i).card

/-- Vertices introduced at bag `i`. -/
def newVertices (i : Fin m) : Finset V :=
  D.bag i \ D.separator i

@[simp] lemma separator_root : D.separator D.root = ∅ := by
  simp [separator]

@[simp] lemma sepCard_root : D.sepCard D.root = 0 := by
  simp [sepCard]

lemma separator_of_ne_root {i : Fin m} (hi : i ≠ D.root) :
    D.separator i = D.bag i ∩ D.bag (D.parent i) := by
  simp [separator, hi]

lemma old_eq_separator {i : Fin m} (hi : i ≠ D.root) :
    D.bag i ∩ D.previousVertices i = D.separator i := by
  rw [previousVertices, D.old_eq_parentSeparator i hi, D.separator_of_ne_root hi]

lemma separator_subset_bag (i : Fin m) :
    D.separator i ⊆ D.bag i := by
  by_cases hi : i = D.root
  · simp [hi]
  · rw [D.separator_of_ne_root hi]
    exact Finset.inter_subset_left

lemma sepCard_le (i : Fin m) :
    D.sepCard i ≤ r := by
  calc
    D.sepCard i = (D.separator i).card := rfl
    _ ≤ (D.bag i).card := Finset.card_le_card (D.separator_subset_bag i)
    _ = r := D.bag_card i

lemma sepCard_lt {i : Fin m} (hi : i ≠ D.root) :
    D.sepCard i < r := by
  by_contra hnot
  have hle : D.sepCard i ≤ r := D.sepCard_le i
  have heqcard : D.sepCard i = r :=
    Nat.le_antisymm hle (Nat.le_of_not_gt hnot)
  have hsub : D.separator i ⊆ D.bag i := D.separator_subset_bag i
  have hbag_le_sep : (D.bag i).card ≤ (D.separator i).card := by
    rw [D.bag_card i, ← sepCard, heqcard]
  have hsepbag : D.separator i = D.bag i :=
    Finset.eq_of_subset_of_card_le hsub hbag_le_sep
  have hbag_sub_parent : D.bag i ⊆ D.bag (D.parent i) := by
    intro v hv
    have hvsep : v ∈ D.separator i := by simpa [hsepbag] using hv
    rw [D.separator_of_ne_root hi] at hvsep
    exact (Finset.mem_inter.mp hvsep).2
  have hbags : D.bag i = D.bag (D.parent i) := by
    apply Finset.eq_of_subset_of_card_le hbag_sub_parent
    rw [D.bag_card i, D.bag_card (D.parent i)]
  have hip : i = D.parent i := D.bag_injective hbags
  have hlt := D.parent_lt i hi
  rw [← hip] at hlt
  exact (Nat.lt_irrefl _ hlt)

@[simp] lemma previousVertices_root :
    D.previousVertices D.root = ∅ := by
  ext v
  simp [previousVertices, D.root_val]

lemma previousVertices_eq_accumulatedVerticesLT (i : Fin m) :
    D.previousVertices i = D.accumulatedVerticesLT i.val := by
  rfl

lemma bagIndicesLT_succ {n : ℕ} (hn : n < m) :
    D.bagIndicesLT (n + 1) =
      insert (⟨n, hn⟩ : Fin m) (D.bagIndicesLT n) := by
  ext j
  simp only [bagIndicesLT, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · intro hj
    by_cases heq : j.val = n
    · exact Or.inl (Fin.ext heq)
    · exact Or.inr (by omega)
  · rintro (hji | hj)
    · subst j
      simp
    · omega

lemma index_not_mem_bagIndicesLT {n : ℕ} (hn : n < m) :
    (⟨n, hn⟩ : Fin m) ∉ D.bagIndicesLT n := by
  simp [bagIndicesLT]

lemma bagIndicesLT_card :
    D.bagIndicesLT m = Finset.univ := by
  ext i
  simp [bagIndicesLT]

lemma accumulatedVerticesLT_succ {n : ℕ} (hn : n < m) :
    D.accumulatedVerticesLT (n + 1) =
      D.bag ⟨n, hn⟩ ∪ D.accumulatedVerticesLT n := by
  unfold accumulatedVerticesLT
  rw [D.bagIndicesLT_succ hn]
  simp

lemma accumulatedVerticesLT_zero :
    D.accumulatedVerticesLT 0 = ∅ := by
  simp [accumulatedVerticesLT, bagIndicesLT]

lemma accumulatedVerticesLT_card :
    D.accumulatedVerticesLT m = Finset.univ := by
  unfold accumulatedVerticesLT bagIndicesLT
  have hfilter :
      (Finset.univ.filter fun i : Fin m => i.val < m) =
        Finset.univ := by
    ext i
    simp
  rw [hfilter]
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
  rcases D.vertex_cover v with ⟨i, hvi⟩
  exact ⟨i, trivial, hvi⟩

lemma bag_subset_accumulatedVerticesLT {i : Fin m} {n : ℕ}
    (hin : i.val < n) :
    D.bag i ⊆ D.accumulatedVerticesLT n := by
  intro v hv
  rw [accumulatedVerticesLT, Finset.mem_biUnion]
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin⟩, hv⟩

lemma bag_inter_previous_eq_separator (i : Fin m) :
    D.bag i ∩ D.previousVertices i = D.separator i := by
  by_cases hi : i = D.root
  · subst i
    simp
  · exact D.old_eq_separator hi

lemma newVertices_eq_bag_sdiff_previous (i : Fin m) :
    D.newVertices i = D.bag i \ D.previousVertices i := by
  ext v
  rw [newVertices, ← D.bag_inter_previous_eq_separator i]
  simp

lemma newVertices_disjoint_accumulatedVerticesLT (i : Fin m) :
    Disjoint (D.newVertices i) (D.accumulatedVerticesLT i.val) := by
  rw [← D.previousVertices_eq_accumulatedVerticesLT,
    D.newVertices_eq_bag_sdiff_previous]
  exact (Finset.disjoint_sdiff
    (s := D.previousVertices i) (t := D.bag i)).symm

lemma accumulatedVerticesLT_inter_bag (i : Fin m) :
    D.accumulatedVerticesLT i.val ∩ D.bag i = D.separator i := by
  rw [← D.previousVertices_eq_accumulatedVerticesLT,
    Finset.inter_comm, D.bag_inter_previous_eq_separator]

lemma newVertices_disjoint_of_lt {i j : Fin m} (hij : i.val < j.val) :
    Disjoint (D.newVertices i) (D.newVertices j) := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  have hvibag : v ∈ D.bag i := by
    exact (Finset.mem_sdiff.mp hvi).1
  have hvjbag : v ∈ D.bag j := by
    exact (Finset.mem_sdiff.mp hvj).1
  have hvprev : v ∈ D.previousVertices j := by
    rw [previousVertices, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, hvibag⟩
  have hvsep : v ∈ D.separator j := by
    rw [← D.bag_inter_previous_eq_separator j]
    exact Finset.mem_inter.mpr ⟨hvjbag, hvprev⟩
  exact (Finset.mem_sdiff.mp hvj).2 hvsep

/-- The sets of vertices introduced by distinct bags are pairwise disjoint. -/
theorem newVertices_pairwiseDisjoint :
    Set.PairwiseDisjoint (Finset.univ : Finset (Fin m)) D.newVertices := by
  intro i hi j hj hij
  have hval : i.val ≠ j.val := by
    intro h
    exact hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · exact D.newVertices_disjoint_of_lt hlt
  · exact (D.newVertices_disjoint_of_lt hgt).symm

lemma mem_biUnion_newVertices (v : V) :
    v ∈ (Finset.univ : Finset (Fin m)).biUnion D.newVertices := by
  rcases D.vertex_cover v with ⟨i, hvi⟩
  have aux :
      ∀ n : ℕ, ∀ i : Fin m, i.val = n → v ∈ D.bag i →
        v ∈ (Finset.univ : Finset (Fin m)).biUnion D.newVertices := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro i hin hvbag
        by_cases hvnew : v ∈ D.newVertices i
        · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hvnew⟩
        · have hvsep : v ∈ D.separator i := by
            by_contra hvnot
            apply hvnew
            exact Finset.mem_sdiff.mpr ⟨hvbag, hvnot⟩
          have hvprev : v ∈ D.previousVertices i := by
            have hvinter : v ∈ D.bag i ∩ D.previousVertices i := by
              rw [D.bag_inter_previous_eq_separator]
              exact hvsep
            exact (Finset.mem_inter.mp hvinter).2
          rw [previousVertices, Finset.mem_biUnion] at hvprev
          rcases hvprev with ⟨j, hj, hvj⟩
          have hjlt : j.val < i.val := (Finset.mem_filter.mp hj).2
          exact ih j.val (by omega) j rfl hvj
  exact aux i.val i rfl hvi

/-- The introduced-vertex sets cover the entire vertex type. -/
theorem biUnion_newVertices :
    (Finset.univ : Finset (Fin m)).biUnion D.newVertices =
      (Finset.univ : Finset V) := by
  ext v
  simp only [Finset.mem_univ, iff_true]
  exact D.mem_biUnion_newVertices v

lemma card_newVertices (i : Fin m) :
    (D.newVertices i).card = r - D.sepCard i := by
  rw [newVertices, Finset.card_sdiff,
    Finset.inter_eq_left.mpr (D.separator_subset_bag i), D.bag_card]
  rfl

end PureCliqueTreeDecomp

end PureChordal
