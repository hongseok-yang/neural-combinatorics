import ApicesCommonness.Trees.Graph.Apex
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Recursive trees, and every tree is one

Plan T-D6.  The Markov construction of `lem:tree-extension` adds the vertices of a tree one at a
time, each attached to an earlier one.  Internally a tree on `m + 1` vertices is a *recursive tree*:
a function `par : ℕ → ℕ`, vertex `i + 1` (`i < m`) being attached to vertex `min (par i) i`
(`parV par i`).  Clamping by `min · i` makes every `par` a recursive tree with no side condition,
and the tree on the first `m` vertices is given by the *same* function (the last vertex is a leaf).

* `treeGraph par m : SimpleGraph (Fin (m + 1))`, its sorted edges `(parV par i, i + 1)`
  (`edgePairs_treeGraph`) and the product over them (`prod_edgePairs_treeGraph`).
* `exists_recTree_iso`: every tree on `Fin (m + 1)` (Mathlib's `IsTree`) is a relabelled recursive
  tree.  Route A of the plan: root the tree at `0`, list the vertices by distance from `0`
  (`Tuple.sort`), and let the parent of a vertex be the penultimate vertex of a shortest path from
  the root, which is the unique neighbour closer to the root (`eq_treeParent_of_adj`).
* `homDensity_apexGraph_of_iso`: densities of `T^{+k}` are those of the recursive tree.
-/

open Finset SimpleGraph MeasureTheory

namespace ApicesCommonness

/-! ### Recursive trees -/

/-- The parent of vertex `i + 1`: vertex `min (par i) i`. -/
def parV (par : ℕ → ℕ) {m : ℕ} (i : Fin m) : Fin (m + 1) := ⟨min (par i) i, by omega⟩

lemma parV_lt_succ (par : ℕ → ℕ) {m : ℕ} (i : Fin m) : parV par i < i.succ := by
  rw [Fin.lt_def]; simp only [parV, Fin.val_succ]; omega

/-- The recursive tree on `Fin (m + 1)` with edges `{parV par i, i + 1}`, `i < m`. -/
def treeGraph (par : ℕ → ℕ) (m : ℕ) : SimpleGraph (Fin (m + 1)) where
  Adj u v := ∃ i : Fin m, (u = parV par i ∧ v = i.succ) ∨ (v = parV par i ∧ u = i.succ)
  symm := ⟨fun u v ⟨i, h⟩ => ⟨i, h.symm⟩⟩
  loopless := ⟨fun u ⟨i, h⟩ => by
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    · have := parV_lt_succ par i
      rw [← h₁, ← h₂] at this
      exact lt_irrefl _ this⟩

instance (par : ℕ → ℕ) (m : ℕ) : DecidableRel (treeGraph par m).Adj := fun u v =>
  inferInstanceAs (Decidable (∃ i : Fin m, (u = parV par i ∧ v = i.succ) ∨
    (v = parV par i ∧ u = i.succ)))

lemma treeGraph_adj (par : ℕ → ℕ) (m : ℕ) (u v : Fin (m + 1)) :
    (treeGraph par m).Adj u v ↔
      ∃ i : Fin m, (u = parV par i ∧ v = i.succ) ∨ (v = parV par i ∧ u = i.succ) := Iff.rfl

/-- **The sorted edges of a recursive tree** are the pairs `(parV par i, i + 1)`. -/
theorem edgePairs_treeGraph (par : ℕ → ℕ) (m : ℕ) :
    edgePairs (treeGraph par m) = univ.image fun i : Fin m => (parV par i, i.succ) := by
  ext ⟨a, b⟩
  rw [mem_edgePairs, mem_image]
  constructor
  · rintro ⟨hlt, i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨i, mem_univ _, rfl⟩
    · exact absurd hlt (not_lt.mpr (parV_lt_succ par i).le)
  · rintro ⟨i, -, he⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨parV_lt_succ par i, i, Or.inl ⟨rfl, rfl⟩⟩

/-- **Products over the edges of a recursive tree.** -/
theorem prod_edgePairs_treeGraph {β : Type*} [CommMonoid β] (par : ℕ → ℕ) (m : ℕ)
    (g : Fin (m + 1) → Fin (m + 1) → β) :
    ∏ p ∈ edgePairs (treeGraph par m), g p.1 p.2 = ∏ i : Fin m, g (parV par i) i.succ := by
  rw [edgePairs_treeGraph, prod_image]
  intro i _ j _ h
  exact Fin.succ_injective _ (Prod.mk.inj h).2

/-! ### Parents in a rooted tree -/

section Parent

variable {V : Type*} {T : SimpleGraph V} (hT : T.IsTree) (r : V)

/-- A shortest path from the root `r` to `v`. -/
noncomputable def rootPath (v : V) : T.Walk r v := (hT.connected.exists_path_of_dist r v).choose

lemma rootPath_isPath (v : V) : (rootPath hT r v).IsPath :=
  (hT.connected.exists_path_of_dist r v).choose_spec.1

lemma rootPath_length (v : V) : (rootPath hT r v).length = T.dist r v :=
  (hT.connected.exists_path_of_dist r v).choose_spec.2

/-- The parent of `v`: the penultimate vertex of the shortest path from the root. -/
noncomputable def treeParent (v : V) : V := (rootPath hT r v).penultimate

lemma treeParent_adj {v : V} (hv : v ≠ r) : T.Adj (treeParent hT r v) v :=
  Walk.adj_penultimate (Walk.not_nil_of_ne hv.symm)

/-- The parent is one step closer to the root. -/
lemma dist_treeParent {v : V} (hv : v ≠ r) :
    T.dist r v = T.dist r (treeParent hT r v) + 1 := by
  have hadj := treeParent_adj hT r hv
  have hmem : treeParent hT r v ∈ (rootPath hT r v).support := Walk.getVert_mem_support _ _
  have h := hT.isAcyclic.path_concat (rootPath_isPath hT r (treeParent hT r v))
    (rootPath_isPath hT r v) hadj hmem
  have hl := congrArg Walk.length h
  rw [Walk.length_concat, rootPath_length, rootPath_length] at hl
  exact hl

/-- **The parent is the unique neighbour closer to the root.** -/
lemma eq_treeParent_of_adj {a b : V} (hab : T.Adj a b) (h : T.dist r a < T.dist r b) :
    a = treeParent hT r b := by
  have hp := rootPath_isPath hT r a
  have hq := rootPath_isPath hT r b
  by_cases ha : a ∈ (rootPath hT r b).support
  · have he := hT.isAcyclic.path_concat hp hq hab ha
    rw [treeParent, he, Walk.penultimate_concat]
  · have hb := hT.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hp hq hab ha
    have he := hT.isAcyclic.path_concat hq hp hab.symm hb
    have hl := congrArg Walk.length he
    rw [Walk.length_concat, rootPath_length, rootPath_length] at hl
    omega

end Parent

/-! ### Every tree on `Fin (m + 1)` is a relabelled recursive tree -/

section Bridge

variable {m : ℕ} {T : SimpleGraph (Fin (m + 1))} (hT : T.IsTree)
include hT

/-- Vertices listed by distance from the root `0`: `bfsOrder hT i` is the `i`-th vertex. -/
noncomputable def bfsOrder : Equiv.Perm (Fin (m + 1)) := Tuple.sort fun v => T.dist 0 v

omit hT in
lemma bfsOrder_lt {u v : Fin (m + 1)} (h : T.dist 0 u < T.dist 0 v) :
    (bfsOrder (T := T)).symm u < (bfsOrder (T := T)).symm v := by
  by_contra hle
  have hm := Tuple.monotone_sort (fun v => T.dist 0 v) (not_lt.mp hle)
  simp only [Function.comp_apply, bfsOrder, Equiv.apply_symm_apply] at hm
  exact absurd h (not_lt.mpr hm)

lemma bfsOrder_zero : (bfsOrder (T := T)) 0 = 0 := by
  have hm := Tuple.monotone_sort (fun v => T.dist 0 v)
    (Fin.zero_le ((bfsOrder (T := T)).symm 0))
  simp only [Function.comp_apply, bfsOrder, Equiv.apply_symm_apply, dist_self,
    Nat.le_zero] at hm
  exact ((hT.connected.dist_eq_zero_iff).mp hm).symm

lemma bfsOrder_symm_zero : (bfsOrder (T := T)).symm 0 = 0 := by
  rw [Equiv.symm_apply_eq, bfsOrder_zero hT]

/-- The parent function of the recursive tree: vertex `j + 1` (in BFS order) is attached to the
position of the parent of the `(j + 1)`-st vertex. -/
noncomputable def bfsPar : ℕ → ℕ := fun j =>
  if h : j + 1 < m + 1 then
    ((bfsOrder (T := T)).symm (treeParent hT 0 (bfsOrder (T := T) ⟨j + 1, h⟩)) : ℕ)
  else 0

lemma bfsOrder_succ_ne_zero (i : Fin m) : bfsOrder (T := T) i.succ ≠ 0 := by
  intro h
  have := congrArg (bfsOrder (T := T)).symm h
  rw [Equiv.symm_apply_apply, bfsOrder_symm_zero hT] at this
  exact Fin.succ_ne_zero i this

lemma parV_bfsPar (i : Fin m) :
    parV (bfsPar hT) i = (bfsOrder (T := T)).symm (treeParent hT 0 (bfsOrder (T := T) i.succ)) := by
  have hne := bfsOrder_succ_ne_zero hT i
  have hlt := bfsOrder_lt (T := T) (by
    rw [dist_treeParent hT 0 hne]; exact Nat.lt_succ_self _ :
      T.dist 0 (treeParent hT 0 (bfsOrder (T := T) i.succ)) < T.dist 0 (bfsOrder (T := T) i.succ))
  rw [Equiv.symm_apply_apply, Fin.lt_def, Fin.val_succ] at hlt
  have hpar : bfsPar hT i = ((bfsOrder (T := T)).symm
      (treeParent hT 0 (bfsOrder (T := T) i.succ)) : ℕ) := by
    simp only [bfsPar, dif_pos (show (i : ℕ) + 1 < m + 1 by omega)]
    rfl
  ext
  simp only [parV, hpar]
  omega

/-- An edge whose first end is closer to the root is a recursive-tree edge. -/
lemma treeGraph_adj_of_lt {u v : Fin (m + 1)} (huv : T.Adj u v) (h : T.dist 0 u < T.dist 0 v) :
    (treeGraph (bfsPar hT) m).Adj ((bfsOrder (T := T)).symm u) ((bfsOrder (T := T)).symm v) := by
  have hu := eq_treeParent_of_adj hT 0 huv h
  have hv0 : (bfsOrder (T := T)).symm v ≠ 0 := by
    intro h0
    rw [Equiv.symm_apply_eq, bfsOrder_zero hT] at h0
    subst h0
    simp at h
  obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr hv0
  refine ⟨i, Or.inl ⟨?_, hi.symm⟩⟩
  rw [parV_bfsPar, hi, Equiv.apply_symm_apply, ← hu]

/-- **Every tree is a relabelled recursive tree** (plan T-D6, route A). -/
theorem exists_recTree_iso :
    ∃ (par : ℕ → ℕ) (e : Fin (m + 1) ≃ Fin (m + 1)), T = (treeGraph par m).comap e := by
  refine ⟨bfsPar hT, (bfsOrder (T := T)).symm, ?_⟩
  ext u v
  rw [comap_adj]
  constructor
  · intro huv
    rcases lt_or_gt_of_ne (hT.dist_ne_of_adj 0 huv) with h | h
    · exact treeGraph_adj_of_lt hT huv h
    · exact (treeGraph_adj_of_lt hT huv.symm h).symm
  · rintro ⟨i, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩
    · rw [parV_bfsPar] at hu
      rw [(bfsOrder (T := T)).symm.injective hu, (Equiv.symm_apply_eq _).mp hv]
      exact treeParent_adj hT 0 (bfsOrder_succ_ne_zero hT i)
    · rw [parV_bfsPar] at hv
      rw [(bfsOrder (T := T)).symm.injective hv, (Equiv.symm_apply_eq _).mp hu]
      exact (treeParent_adj hT 0 (bfsOrder_succ_ne_zero hT i)).symm

end Bridge

/-! ### Densities of `T^{+k}` are those of the recursive tree -/

section Density

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `homDensity` does not depend on the decidability instance, and respects graph equality. -/
lemma homDensity_congr {v : ℕ} {F G : SimpleGraph (Fin v)} [DecidableRel F.Adj]
    [DecidableRel G.Adj] (h : F = G) (L : Ω → Ω → ℝ) (μ : Measure Ω) :
    homDensity F L μ = homDensity G L μ := by
  subst h
  congr

/-- **Relabelling invariance for `T^{+k}`.** -/
theorem homDensity_apexGraph_of_iso {m k : ℕ} {T : SimpleGraph (Fin (m + 1))} [DecidableRel T.Adj]
    {par : ℕ → ℕ} {e : Fin (m + 1) ≃ Fin (m + 1)} (h : T = (treeGraph par m).comap e)
    {L : Ω → Ω → ℝ} (hL : ∀ x y, L x y = L y x) :
    homDensity (apexGraph T k) L μ = homDensity (apexGraph (treeGraph par m) k) L μ := by
  rw [homDensity_congr (congrArg (fun G => apexGraph G k) h), homDensity_congr
    (apexGraph_comap (treeGraph par m) e), homDensity_comap_equiv _ _ hL]

/-- **Relabelling invariance for `T`.** -/
theorem homDensity_tree_of_iso {m : ℕ} {T : SimpleGraph (Fin (m + 1))} [DecidableRel T.Adj]
    {par : ℕ → ℕ} {e : Fin (m + 1) ≃ Fin (m + 1)} (h : T = (treeGraph par m).comap e)
    {L : Ω → Ω → ℝ} (hL : ∀ x y, L x y = L y x) :
    homDensity T L μ = homDensity (treeGraph par m) L μ := by
  rw [homDensity_congr h, homDensity_comap_equiv _ _ hL]

end Density

end ApicesCommonness
