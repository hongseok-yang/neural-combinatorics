import ApicesCommonness.Common.Graph.Apex
import Mathlib.Data.Fin.Embedding

/-!
# The edges of `C_n^{+s}`

The sorted edges of `apexCycle n s` are the sorted edges of the cycle, moved into the first `n`
vertices, together with the `n · s` pairs `(castAdd i, natAdd j)` joining a cycle vertex to an apex
(`edgePairs_apexCycle`).  Consequently every product over the edges splits
(`prod_edgePairs_apexCycle`).  No symmetry is needed: `castAdd` is monotone and every cycle vertex
precedes every apex.
-/

open Finset SimpleGraph

namespace ApicesCommonness

variable {n s : ℕ}

/-- The cycle–apex pairs `(castAdd i, natAdd j)`. -/
def crossEdges (n s : ℕ) : Finset (Fin (n + s) × Fin (n + s)) :=
  (univ : Finset (Fin n × Fin s)).map ((Fin.castAddEmb s).prodMap (Fin.natAddEmb n))

/-- The cycle edges on the first `n` vertices. -/
def cycleEdgesIn (n s : ℕ) : Finset (Fin (n + s) × Fin (n + s)) :=
  (edgePairs (cycleGraph n)).map ((Fin.castAddEmb s).prodMap (Fin.castAddEmb s))

lemma disjoint_cycleEdgesIn_crossEdges : Disjoint (cycleEdgesIn n s) (crossEdges n s) := by
  rw [Finset.disjoint_left]
  intro p h₁ h₂
  simp only [cycleEdgesIn, crossEdges, mem_map] at h₁ h₂
  obtain ⟨q, _, rfl⟩ := h₁
  obtain ⟨r, _, hr⟩ := h₂
  have h := congrArg (fun p : Fin (n + s) × Fin (n + s) => (p.2 : ℕ)) hr
  simp at h
  have := q.2.isLt
  omega

/-- **The edges of `C_n^{+s}`.** -/
theorem edgePairs_apexCycle :
    edgePairs (apexCycle n s) = cycleEdgesIn n s ∪ crossEdges n s := by
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
      | right j => exact absurd hadj (apexCycle_not_adj_natAdd_natAdd i j)
  · rintro (h | h)
    · obtain ⟨q, hq, hqe⟩ := mem_map.mp h
      rw [mem_edgePairs] at hq
      rw [← hqe]
      refine ⟨?_, ?_⟩
      · show Fin.castAdd s q.1 < Fin.castAdd s q.2
        rw [Fin.lt_def] at hq ⊢
        simpa using hq.1
      · show (apexCycle n s).Adj (Fin.castAdd s q.1) (Fin.castAdd s q.2)
        simpa using hq.2
    · obtain ⟨q, _, hqe⟩ := mem_map.mp h
      rw [← hqe]
      refine ⟨?_, ?_⟩
      · show Fin.castAdd s q.1 < Fin.natAdd n q.2
        rw [Fin.lt_def]
        simp only [Fin.val_castAdd, Fin.val_natAdd]
        have := q.1.isLt
        omega
      · show (apexCycle n s).Adj (Fin.castAdd s q.1) (Fin.natAdd n q.2)
        exact apexCycle_adj_castAdd_natAdd q.1 q.2

/-- **Products over the edges of `C_n^{+s}` split** into the cycle part and the `n · s` apex edges. -/
theorem prod_edgePairs_apexCycle {β : Type*} [CommMonoid β]
    (g : Fin (n + s) → Fin (n + s) → β) :
    ∏ p ∈ edgePairs (apexCycle n s), g p.1 p.2
      = (∏ p ∈ edgePairs (cycleGraph n), g (Fin.castAdd s p.1) (Fin.castAdd s p.2)) *
          ∏ i : Fin n, ∏ j : Fin s, g (Fin.castAdd s i) (Fin.natAdd n j) := by
  rw [edgePairs_apexCycle, prod_union disjoint_cycleEdgesIn_crossEdges, cycleEdgesIn, crossEdges,
    prod_map, prod_map, ← univ_product_univ, prod_product]
  rfl

end ApicesCommonness
