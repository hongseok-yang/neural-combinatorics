import Taeyoung.Methods.Link.Cone
import Taeyoung.Foundation.ChromaticExtension

/-!
# The chromatic data of a cone

Every cone row so far has obtained its chromatic polynomial from an attachment
tower, which works only when the cone happens to be chordal enough to have a
simplicial vertex.  `K₁ ∨ C₅` is not, so the general identity is proved here:

```
properAssignmentCount (K₁ ∨ F) k = k · properAssignmentCount F (k-1),
```

because a proper colouring of the cone is a colour for the apex together with a
proper colouring of `F` avoiding it, and the colours other than a fixed one are
`Fin.succAbove`-indexed by `Fin (k-1)`.

Consequently `χ_{K₁∨F}(x) = x·χ_F(x-1)` and `χ(K₁∨F) = χ(F) + 1`, both stated
below in the form the catalogue uses.
-/

open Finset Polynomial

namespace Taeyoung.Methods.Link

open Taeyoung

variable {n : ℕ}

/-! ### Adjacency in a cone -/

lemma coneGraph_adj_succ (F : SimpleGraph (Fin n)) (i j : Fin n) :
    (coneGraph F).Adj i.succ j.succ ↔ F.Adj i j := by
  simp only [coneGraph, SimpleGraph.sup_adj, starGraph, SimpleGraph.fromRel_adj,
    SimpleGraph.map_adj', Fin.coe_succEmb]
  constructor
  · rintro (⟨-, h | h⟩ | ⟨-, a, b, hab, ha, hb⟩)
    · exact absurd h (Fin.succ_ne_zero i)
    · exact absurd h (Fin.succ_ne_zero j)
    · rw [Fin.succ_inj] at ha hb
      exact ha ▸ hb ▸ hab
  · intro h
    exact Or.inr ⟨fun hc ↦ h.ne (Fin.succ_injective _ hc), i, j, h, rfl, rfl⟩

lemma coneGraph_adj_zero (F : SimpleGraph (Fin n)) (j : Fin n) :
    (coneGraph F).Adj 0 j.succ := by
  refine Or.inl ?_
  rw [starGraph, SimpleGraph.fromRel_adj]
  exact ⟨(Fin.succ_ne_zero j).symm, Or.inl rfl⟩

/-- A cone colouring is an apex colour together with a colouring of the base
that avoids it. -/
lemma isProperAssignment_coneGraph {k : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (c : Fin k) (y : Fin n → Fin k) :
    IsProperAssignment (coneGraph F) (Fin.cons c y) ↔
      (∀ i, y i ≠ c) ∧ IsProperAssignment F y := by
  constructor
  · intro h
    refine ⟨fun i ↦ ?_, fun u v huv ↦ ?_⟩
    · have := h (coneGraph_adj_zero F i)
      simpa using this.symm
    · have := h ((coneGraph_adj_succ F u v).mpr huv)
      simpa using this
  · rintro ⟨havoid, hprop⟩ u v huv
    obtain rfl | ⟨i, rfl⟩ := u.eq_zero_or_eq_succ
    · obtain rfl | ⟨j, rfl⟩ := v.eq_zero_or_eq_succ
      · exact absurd huv (SimpleGraph.irrefl _)
      · simpa using (havoid j).symm
    · obtain rfl | ⟨j, rfl⟩ := v.eq_zero_or_eq_succ
      · simpa using havoid i
      · simpa using hprop ((coneGraph_adj_succ F i j).mp huv)

/-! ### The count -/

/-- Proper colourings of `F` avoiding one fixed colour are the proper colourings
with one colour fewer. -/
lemma card_avoiding (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] {m : ℕ}
    (c : Fin (m + 1))
    [DecidablePred fun y : Fin n → Fin m ↦ IsProperAssignment F y]
    [DecidablePred fun y : Fin n → Fin (m + 1) ↦
      (∀ i, y i ≠ c) ∧ IsProperAssignment F y] :
    ((univ : Finset (Fin n → Fin m)).filter fun y ↦ IsProperAssignment F y).card =
      ((univ : Finset (Fin n → Fin (m + 1))).filter
        fun y ↦ (∀ i, y i ≠ c) ∧ IsProperAssignment F y).card := by
  refine Finset.card_bij (fun y _ ↦ fun j ↦ c.succAbove (y j)) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact ⟨fun i ↦ Fin.succAbove_ne c (y i),
      fun u v huv ↦ fun hc ↦ hy huv (Fin.succAbove_right_injective hc)⟩
  · intro y₁ _ y₂ _ hy
    funext j
    exact Fin.succAbove_right_injective (congrFun hy j)
  · intro y' hy'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy'
    obtain ⟨havoid, hprop⟩ := hy'
    refine ⟨fun j ↦ Classical.choose (Fin.exists_succAbove_eq (havoid j)), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro u v huv hc
      have hu := Classical.choose_spec (Fin.exists_succAbove_eq (havoid u))
      have hv := Classical.choose_spec (Fin.exists_succAbove_eq (havoid v))
      exact hprop huv (by rw [← hu, ← hv]; exact congrArg c.succAbove hc)
    · funext j
      exact Classical.choose_spec (Fin.exists_succAbove_eq (havoid j))

/-- **The cone counting identity.** -/
theorem properAssignmentCount_coneGraph (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (k : ℕ) :
    properAssignmentCount (coneGraph F) k = k * properAssignmentCount F (k - 1) := by
  classical
  cases k with
  | zero =>
      have hempty : IsEmpty (Fin (n + 1) → Fin 0) := ⟨fun x ↦ (x 0).elim0⟩
      simp [properAssignmentCount, Finset.univ_eq_empty]
  | succ m =>
      have hsplit : properAssignmentCount (coneGraph F) (m + 1) =
          ∑ c : Fin (m + 1), ∑ y : Fin n → Fin (m + 1),
            if (∀ i, y i ≠ c) ∧ IsProperAssignment F y then 1 else 0 := by
        rw [properAssignmentCount, Finset.card_filter,
          ← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 1) ↦ Fin (m + 1))]
        simp only [Fintype.sum_prod_type, Fin.consEquiv_apply]
        refine Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
        exact if_congr (isProperAssignment_coneGraph F c y) rfl rfl
      rw [hsplit]
      have hinner : ∀ c : Fin (m + 1),
          (∑ y : Fin n → Fin (m + 1),
            if (∀ i, y i ≠ c) ∧ IsProperAssignment F y then 1 else 0) =
              properAssignmentCount F m := by
        intro c
        rw [← Finset.card_filter, properAssignmentCount]
        exact (card_avoiding F c).symm
      rw [Finset.sum_congr rfl fun c _ ↦ hinner c, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.add_sub_cancel]

/-! ### The chromatic polynomial and the chromatic number -/

/-- **`χ_{K₁∨F}(x) = x·χ_F(x-1)`.** -/
theorem isChromaticPolynomial_coneGraph {P : Polynomial ℝ}
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (hP : IsChromaticPolynomial F P) :
    IsChromaticPolynomial (coneGraph F) (X * P.comp (X - 1)) := by
  intro k
  rw [properAssignmentCount_coneGraph, eval_mul, eval_X, eval_comp, eval_sub,
    eval_X, eval_one]
  cases k with
  | zero => simp
  | succ j =>
      have hcast : ((j + 1 : ℕ) : ℝ) - 1 = ((j : ℕ) : ℝ) := by push_cast; ring
      rw [hcast, hP j, Nat.add_sub_cancel]
      push_cast
      ring

/-- **The chromatic number of a cone is one more than the base's.** -/
theorem isChromaticNumber_coneGraph {r : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (hr : IsChromaticNumber F r) :
    IsChromaticNumber (coneGraph F) (r + 1) where
  positive := by
    rw [properAssignmentCount_coneGraph, Nat.add_sub_cancel]
    exact Nat.mul_pos (Nat.succ_pos r) hr.positive
  zero_below k hk := by
    rw [properAssignmentCount_coneGraph]
    cases k with
    | zero => simp
    | succ j =>
        rw [Nat.add_sub_cancel, hr.zero_below j (by omega), Nat.mul_zero]

end Taeyoung.Methods.Link
