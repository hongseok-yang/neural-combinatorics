import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Cycles with independent apices

Blueprint `def:densities` and `lem:counts`.

* `cycleGraph n` is Mathlib's cycle on `Fin n` (`Mathlib/Combinatorics/SimpleGraph/Circulant.lean`):
  `a ~ b ↔ a - b = 1 ∨ b - a = 1`.
* `apexCycle n k` is `C_n^{+k}` on `Fin (n + k)`: the cycle on the first `n` vertices
  (`Fin.castAdd k i`), and `k` apices (`Fin.natAdd n j`), each joined to every cycle vertex and to
  no other apex.
* `edgePairs F` lists each edge of `F` once, as the ordered pair `(i, j)` with `i < j`.  It is the
  index set of the edge product in `homDensity`, and `card_edgePairs` identifies its size with
  Mathlib's edge count.

Main results: `cycleGraph_card_edgePairs` (`|E(C_n)| = n` for `n ≥ 3`) and
`apexCycle_edgeCount` (`|E(C_n^{+k})| = n (k + 1)` for `n ≥ 3`).
-/

namespace EvenCycleApex

open SimpleGraph Finset

/-- `C_n^{+k}`: the cycle `cycleGraph n` on `Fin.castAdd k '' Fin n`, and `k` independent apices
`Fin.natAdd n '' Fin k`, each adjacent to all cycle vertices. -/
def apexCycle (n k : ℕ) : SimpleGraph (Fin (n + k)) where
  Adj u v :=
    Fin.addCases (motive := fun _ => Prop)
      (fun i => Fin.addCases (motive := fun _ => Prop) (fun j => (cycleGraph n).Adj i j)
        (fun _ => True) v)
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
    | left i => simp only [Fin.addCases_left] at h; exact (cycleGraph n).loopless.irrefl i h
    | right i => simp at h⟩

variable {n k : ℕ}

@[simp] lemma apexCycle_adj_castAdd_castAdd (i j : Fin n) :
    (apexCycle n k).Adj (Fin.castAdd k i) (Fin.castAdd k j) ↔ (cycleGraph n).Adj i j := by
  simp [apexCycle]

@[simp] lemma apexCycle_adj_castAdd_natAdd (i : Fin n) (j : Fin k) :
    (apexCycle n k).Adj (Fin.castAdd k i) (Fin.natAdd n j) := by
  simp [apexCycle]

@[simp] lemma apexCycle_adj_natAdd_castAdd (i : Fin k) (j : Fin n) :
    (apexCycle n k).Adj (Fin.natAdd n i) (Fin.castAdd k j) := by
  simp [apexCycle]

@[simp] lemma apexCycle_not_adj_natAdd_natAdd (i j : Fin k) :
    ¬ (apexCycle n k).Adj (Fin.natAdd n i) (Fin.natAdd n j) := by
  simp [apexCycle]

instance (n k : ℕ) : DecidableRel (apexCycle n k).Adj := fun u v => by
  induction u using Fin.addCases with
  | left i =>
    induction v using Fin.addCases with
    | left j => exact decidable_of_iff _ (apexCycle_adj_castAdd_castAdd i j).symm
    | right j => exact isTrue (apexCycle_adj_castAdd_natAdd i j)
  | right i =>
    induction v using Fin.addCases with
    | left j => exact isTrue (apexCycle_adj_natAdd_castAdd i j)
    | right j => exact isFalse (apexCycle_not_adj_natAdd_natAdd i j)

/-! ### Edge counts -/

/-- The edges of `F`, each once, as ordered pairs `(i, j)` with `i < j`. -/
def edgePairs {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj] : Finset (Fin v × Fin v) :=
  univ.filter fun p => p.1 < p.2 ∧ F.Adj p.1 p.2

lemma mem_edgePairs {v : ℕ} {F : SimpleGraph (Fin v)} [DecidableRel F.Adj] {p : Fin v × Fin v} :
    p ∈ edgePairs F ↔ p.1 < p.2 ∧ F.Adj p.1 p.2 := by
  simp [edgePairs]

/-- `edgePairs F` is in bijection with Mathlib's `F.edgeFinset`, via `p ↦ s(p.1, p.2)`. -/
lemma card_edgePairs {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj] :
    (edgePairs F).card = F.edgeFinset.card := by
  refine Finset.card_bij (fun p _ => s(p.1, p.2)) (fun p hp => ?_) (fun p hp q hq hpq => ?_)
    (fun e he => ?_)
  · rw [mem_edgePairs] at hp
    simpa using hp.2
  · rw [mem_edgePairs] at hp hq
    rcases Sym2.eq_iff.mp hpq with h | h
    · exact Prod.ext h.1 h.2
    · exact absurd (h.1 ▸ h.2 ▸ hq.1) (not_lt.mpr hp.1.le)
  · induction e using Sym2.ind with
    | h a b =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      rcases lt_or_gt_of_ne (F.ne_of_adj he) with hab | hab
      · exact ⟨(a, b), mem_edgePairs.mpr ⟨hab, he⟩, rfl⟩
      · exact ⟨(b, a), mem_edgePairs.mpr ⟨hab, he.symm⟩, Sym2.eq_swap⟩

/-- Twice the number of edges is the degree sum. -/
lemma two_mul_card_edgePairs {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj] :
    2 * (edgePairs F).card = ∑ u, F.degree u := by
  rw [card_edgePairs, sum_degrees_eq_twice_card_edges]

/-- `|E(C_n)| = n` for `n ≥ 3`. -/
lemma cycleGraph_card_edgePairs (hn : 3 ≤ n) : (edgePairs (cycleGraph n)).card = n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := two_mul_card_edgePairs (cycleGraph (m + 3))
  simp only [cycleGraph_degree_three_le, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega

/-- Degree of a vertex as a sum of indicator values. -/
lemma degree_eq_sum {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj] (u : Fin v) :
    F.degree u = ∑ w, if F.Adj u w then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter]

/-- A cycle vertex of `C_n^{+k}` has degree `2 + k` (for `n ≥ 3`). -/
lemma apexCycle_degree_castAdd (hn : 3 ≤ n) (i : Fin n) :
    (apexCycle n k).degree (Fin.castAdd k i) = 2 + k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [degree_eq_sum, Fin.sum_univ_add]
  simp only [apexCycle_adj_castAdd_castAdd, apexCycle_adj_castAdd_natAdd, if_true, sum_const,
    card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  rw [← degree_eq_sum, cycleGraph_degree_three_le]

/-- An apex of `C_n^{+k}` has degree `n`. -/
lemma apexCycle_degree_natAdd (j : Fin k) :
    (apexCycle n k).degree (Fin.natAdd n j) = n := by
  rw [degree_eq_sum, Fin.sum_univ_add]
  simp

/-- **`lem:counts`.**  `|E(C_n^{+k})| = n (k + 1)` for `n ≥ 3`. -/
theorem apexCycle_edgeCount (hn : 3 ≤ n) : (edgePairs (apexCycle n k)).card = n * (k + 1) := by
  have h := two_mul_card_edgePairs (apexCycle n k)
  rw [Fin.sum_univ_add] at h
  simp only [apexCycle_degree_castAdd hn, apexCycle_degree_natAdd, sum_const, card_univ,
    Fintype.card_fin, smul_eq_mul] at h
  have : 2 * (edgePairs (apexCycle n k)).card = 2 * (n * (k + 1)) := by rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) this

end EvenCycleApex
