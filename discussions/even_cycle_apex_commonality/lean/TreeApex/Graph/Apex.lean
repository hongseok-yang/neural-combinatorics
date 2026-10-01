import EvenCycleApex.Graph.ApexEdges
import EvenCycleApex.Graph.DensityAlgebra
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Graphs with independent apices

Paper `sec:statements` and `eq:sizes`.

* `apexGraph G k` is `G^{+k}` on `Fin (n + k)`: the graph `G` on the first `n` vertices
  (`Fin.castAdd k i`) and `k` apices (`Fin.natAdd n j`), each joined to every vertex of `G` and to no
  other apex.  It is the even-cycle library's `apexCycle` with `cycleGraph n` replaced by `G`
  (`apexCycle_eq_apexGraph`).
* `edgePairs_apexGraph`, `prod_edgePairs_apexGraph`: the sorted edges split into the edges of `G` and
  the `n · k` apex edges (verbatim `Graph/ApexEdges.lean` of the even-cycle library).
* `apexGraph_edgeCount`: `|E(T^{+k})| = (k + 1) n − 1` for a tree `T` on `n` vertices.
* `apexGraph_connected`, `apexGraph_comap` (relabelling `G` relabels `G^{+k}`), and the three small
  graphs `K₂ = ⊤`, `P₃ = pathGraph 3`, `K₃ = ⊤` with their sorted edge sets.
-/

open Finset SimpleGraph

namespace TreeApex

open EvenCycleApex

/-- `G^{+k}`: the graph `G` on `Fin.castAdd k '' Fin n`, and `k` independent apices
`Fin.natAdd n '' Fin k`, each adjacent to all vertices of `G`. -/
def apexGraph {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : SimpleGraph (Fin (n + k)) where
  Adj u v :=
    Fin.addCases (motive := fun _ => Prop)
      (fun i => Fin.addCases (motive := fun _ => Prop) (fun j => G.Adj i j) (fun _ => True) v)
      (fun _ => Fin.addCases (motive := fun _ => Prop) (fun _ => True) (fun _ => False) v) u
  symm := ⟨fun u v h => by
    induction u using Fin.addCases with
    | left i =>
      induction v using Fin.addCases with
      | left j => simp only [Fin.addCases_left] at h ⊢; exact h.symm
      | right j => simp
    | right i =>
      induction v using Fin.addCases with
      | left j => simp
      | right j => simp at h⟩
  loopless := ⟨fun u h => by
    induction u using Fin.addCases with
    | left i => simp only [Fin.addCases_left] at h; exact G.loopless.irrefl i h
    | right i => simp at h⟩

variable {n k : ℕ} (G : SimpleGraph (Fin n))

@[simp] lemma apexGraph_adj_castAdd_castAdd (i j : Fin n) :
    (apexGraph G k).Adj (Fin.castAdd k i) (Fin.castAdd k j) ↔ G.Adj i j := by
  simp [apexGraph]

@[simp] lemma apexGraph_adj_castAdd_natAdd (i : Fin n) (j : Fin k) :
    (apexGraph G k).Adj (Fin.castAdd k i) (Fin.natAdd n j) := by
  simp [apexGraph]

@[simp] lemma apexGraph_adj_natAdd_castAdd (i : Fin k) (j : Fin n) :
    (apexGraph G k).Adj (Fin.natAdd n i) (Fin.castAdd k j) := by
  simp [apexGraph]

@[simp] lemma apexGraph_not_adj_natAdd_natAdd (i j : Fin k) :
    ¬ (apexGraph G k).Adj (Fin.natAdd n i) (Fin.natAdd n j) := by
  simp [apexGraph]

instance [DecidableRel G.Adj] (k : ℕ) : DecidableRel (apexGraph G k).Adj := fun u v => by
  induction u using Fin.addCases with
  | left i =>
    induction v using Fin.addCases with
    | left j => exact decidable_of_iff _ (apexGraph_adj_castAdd_castAdd G i j).symm
    | right j => exact isTrue (apexGraph_adj_castAdd_natAdd G i j)
  | right i =>
    induction v using Fin.addCases with
    | left j => exact isTrue (apexGraph_adj_natAdd_castAdd G i j)
    | right j => exact isFalse (apexGraph_not_adj_natAdd_natAdd G i j)

/-- **Cross-check with the even-cycle library.**  `C_n^{+k}` is `apexGraph (cycleGraph n) k`. -/
theorem apexCycle_eq_apexGraph (n k : ℕ) : apexCycle n k = apexGraph (cycleGraph n) k := rfl

/-! ### The edges of `G^{+k}` -/

/-- The edges of `G` on the first `n` vertices. -/
def baseEdgesIn [DecidableRel G.Adj] (k : ℕ) : Finset (Fin (n + k) × Fin (n + k)) :=
  (edgePairs G).map ((Fin.castAddEmb k).prodMap (Fin.castAddEmb k))

lemma disjoint_baseEdgesIn_crossEdges [DecidableRel G.Adj] :
    Disjoint (baseEdgesIn G k) (crossEdges n k) := by
  rw [Finset.disjoint_left]
  intro p h₁ h₂
  simp only [baseEdgesIn, crossEdges, mem_map] at h₁ h₂
  obtain ⟨q, _, rfl⟩ := h₁
  obtain ⟨r, _, hr⟩ := h₂
  have h := congrArg (fun p : Fin (n + k) × Fin (n + k) => (p.2 : ℕ)) hr
  simp at h
  have := q.2.isLt
  omega

/-- **The edges of `G^{+k}`.** -/
theorem edgePairs_apexGraph [DecidableRel G.Adj] :
    edgePairs (apexGraph G k) = baseEdgesIn G k ∪ crossEdges n k := by
  ext ⟨a, b⟩
  rw [mem_union, mem_edgePairs]
  constructor
  · rintro ⟨hlt, hadj⟩
    induction a using Fin.addCases with
    | left i =>
      induction b using Fin.addCases with
      | left j =>
        left
        refine mem_map.mpr ⟨(i, j), mem_edgePairs.mpr ⟨?_, ?_⟩, rfl⟩
        · rw [Fin.lt_def] at hlt ⊢; simpa using hlt
        · simpa using hadj
      | right j =>
        right
        exact mem_map.mpr ⟨(i, j), mem_univ _, rfl⟩
    | right i =>
      induction b using Fin.addCases with
      | left j =>
        exfalso
        rw [Fin.lt_def] at hlt
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hlt
        have := j.isLt
        omega
      | right j => exact absurd hadj (apexGraph_not_adj_natAdd_natAdd G i j)
  · rintro (h | h)
    · obtain ⟨q, hq, hqe⟩ := mem_map.mp h
      rw [mem_edgePairs] at hq
      rw [← hqe]
      refine ⟨?_, ?_⟩
      · show Fin.castAdd k q.1 < Fin.castAdd k q.2
        rw [Fin.lt_def] at hq ⊢
        simpa using hq.1
      · show (apexGraph G k).Adj (Fin.castAdd k q.1) (Fin.castAdd k q.2)
        simpa using hq.2
    · obtain ⟨q, _, hqe⟩ := mem_map.mp h
      rw [← hqe]
      refine ⟨?_, ?_⟩
      · show Fin.castAdd k q.1 < Fin.natAdd n q.2
        rw [Fin.lt_def]
        simp only [Fin.val_castAdd, Fin.val_natAdd]
        have := q.1.isLt
        omega
      · show (apexGraph G k).Adj (Fin.castAdd k q.1) (Fin.natAdd n q.2)
        exact apexGraph_adj_castAdd_natAdd G q.1 q.2

/-- **Products over the edges of `G^{+k}` split** into the part of `G` and the `n · k` apex edges. -/
theorem prod_edgePairs_apexGraph [DecidableRel G.Adj] {β : Type*} [CommMonoid β]
    (g : Fin (n + k) → Fin (n + k) → β) :
    ∏ p ∈ edgePairs (apexGraph G k), g p.1 p.2
      = (∏ p ∈ edgePairs G, g (Fin.castAdd k p.1) (Fin.castAdd k p.2)) *
          ∏ i : Fin n, ∏ j : Fin k, g (Fin.castAdd k i) (Fin.natAdd n j) := by
  rw [edgePairs_apexGraph, prod_union (disjoint_baseEdgesIn_crossEdges G), baseEdgesIn,
    crossEdges, prod_map, prod_map, ← univ_product_univ, prod_product]
  rfl

/-- `|E(G^{+k})| = |E(G)| + n k`. -/
lemma card_edgePairs_apexGraph [DecidableRel G.Adj] :
    (edgePairs (apexGraph G k)).card = (edgePairs G).card + n * k := by
  rw [edgePairs_apexGraph, card_union_of_disjoint (disjoint_baseEdgesIn_crossEdges G), baseEdgesIn,
    crossEdges, card_map, card_map, card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin]

/-- A tree on `n` vertices has `n − 1` edges. -/
lemma IsTree.card_edgePairs [DecidableRel G.Adj] (hT : G.IsTree) :
    (edgePairs G).card + 1 = n := by
  rw [EvenCycleApex.card_edgePairs, hT.card_edgeFinset, Fintype.card_fin]

/-- **`eq:sizes`.**  `|E(T^{+k})| = (k + 1) n − 1` for a tree `T` on `n` vertices. -/
theorem apexGraph_edgeCount [DecidableRel G.Adj] (hT : G.IsTree) :
    (edgePairs (apexGraph G k)).card = (k + 1) * n - 1 := by
  rw [card_edgePairs_apexGraph]
  have h := IsTree.card_edgePairs G hT
  have : (k + 1) * n = n * k + n := by ring
  omega

/-! ### Connectivity -/

/-- `G^{+k}` is connected as soon as `G` has a vertex and `k ≥ 1`: every vertex of `G` is adjacent
to the first apex, and every apex to the first vertex of `G`. -/
theorem apexGraph_connected (hn : 0 < n) (hk : 0 < k) : (apexGraph G k).Connected := by
  set a : Fin (n + k) := Fin.natAdd n ⟨0, hk⟩
  have hreach : ∀ u, (apexGraph G k).Reachable u a := by
    intro u
    induction u using Fin.addCases with
    | left i => exact (apexGraph_adj_castAdd_natAdd G i _).reachable
    | right j =>
      exact (apexGraph_adj_natAdd_castAdd G j ⟨0, hn⟩).reachable.trans
        (apexGraph_adj_castAdd_natAdd G _ _).reachable
  haveI : Nonempty (Fin (n + k)) := ⟨a⟩
  exact Connected.mk fun u v => (hreach u).trans (hreach v).symm

/-! ### Relabelling -/

/-- The extension of a permutation of `Fin n` by the identity on the apices. -/
def apexEquiv (e : Fin n ≃ Fin n) (k : ℕ) : Fin (n + k) ≃ Fin (n + k) :=
  finSumFinEquiv.symm.trans ((e.sumCongr (Equiv.refl (Fin k))).trans finSumFinEquiv)

@[simp] lemma apexEquiv_castAdd (e : Fin n ≃ Fin n) (i : Fin n) :
    apexEquiv e k (Fin.castAdd k i) = Fin.castAdd k (e i) := by
  simp [apexEquiv]

@[simp] lemma apexEquiv_natAdd (e : Fin n ≃ Fin n) (j : Fin k) :
    apexEquiv e k (Fin.natAdd n j) = Fin.natAdd n j := by
  simp [apexEquiv]

/-- **Relabelling `G` relabels `G^{+k}`.** -/
theorem apexGraph_comap (e : Fin n ≃ Fin n) :
    apexGraph (G.comap e) k = (apexGraph G k).comap (apexEquiv e k) := by
  ext u v
  induction u using Fin.addCases with
  | left i =>
    induction v using Fin.addCases with
    | left j => simp
    | right j => simp
  | right i =>
    induction v using Fin.addCases with
    | left j => simp
    | right j => simp

/-! ### The small graphs `K₂`, `P₃`, `K₃` -/

instance (m : ℕ) : DecidableRel (pathGraph m).Adj := fun _ _ =>
  decidable_of_iff _ pathGraph_adj.symm

lemma edgePairs_K₂ : edgePairs (⊤ : SimpleGraph (Fin 2)) = {(0, 1)} := by decide

lemma edgePairs_P₃ : edgePairs (pathGraph 3) = {(0, 1), (1, 2)} := by decide

lemma edgePairs_K₃ : edgePairs (⊤ : SimpleGraph (Fin 3)) = {(0, 1), (0, 2), (1, 2)} := by decide

lemma connected_K₂ : (⊤ : SimpleGraph (Fin 2)).Connected := connected_top_iff.mpr ⟨0⟩

lemma connected_K₃ : (⊤ : SimpleGraph (Fin 3)).Connected := connected_top_iff.mpr ⟨0⟩

lemma connected_P₃ : (pathGraph 3).Connected := pathGraph_connected 2

end TreeApex
