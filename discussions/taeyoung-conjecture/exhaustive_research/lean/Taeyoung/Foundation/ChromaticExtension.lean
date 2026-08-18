import Taeyoung.Foundation.Isomorphism

/-!
# Adjoining a vertex whose neighbourhood is a clique

Every remaining catalogue row needs a chromatic polynomial: both
`SatisfiesLowerBound` and `ViolatesLowerBound` quantify over polynomials
satisfying `IsChromaticPolynomial`, and `properAssignmentCount` is noncomputable
with a condition ranging over all `k : ℕ`, so `decide` never applies.

This file supplies the single most useful construction.  If `S` is a clique of
`H` and we adjoin one new vertex adjacent to exactly `S`, then

```
properAssignmentCount (attachVertex H S) k = (k - |S|) * properAssignmentCount H k
```

because a proper colouring of `H` is injective on `S`, so the new vertex has
exactly `k - |S|` admissible colours whatever the colouring below it.

Iterating this from a clique builds leaves (`|S| = 1`), trees, and every pure
chordal graph; taking `S = univ` is a cone.
-/

namespace Taeyoung

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The construction -/

/-- The oriented relation defining the attachment; `fromRel` symmetrises it. -/
def attachRel (H : SimpleGraph V) (S : Finset V) : Option V → Option V → Prop
  | some u, some v => H.Adj u v
  | some u, none => u ∈ S
  | none, _ => False

/-- `H` with one new vertex `none` adjacent to exactly the vertices of `S`. -/
def attachVertex (H : SimpleGraph V) (S : Finset V) : SimpleGraph (Option V) :=
  SimpleGraph.fromRel (attachRel H S)

variable {H : SimpleGraph V} {S : Finset V}

@[simp] lemma attachVertex_adj_some_some (u v : V) :
    (attachVertex H S).Adj (some u) (some v) ↔ H.Adj u v := by
  simp only [attachVertex, SimpleGraph.fromRel_adj, attachRel]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    exact ⟨by simpa using h.ne, Or.inl h⟩

@[simp] lemma attachVertex_adj_some_none (u : V) :
    (attachVertex H S).Adj (some u) none ↔ u ∈ S := by
  simp [attachVertex, SimpleGraph.fromRel_adj, attachRel]

@[simp] lemma attachVertex_adj_none_some (v : V) :
    (attachVertex H S).Adj none (some v) ↔ v ∈ S := by
  simp [attachVertex, SimpleGraph.fromRel_adj, attachRel]

@[simp] lemma attachVertex_adj_none_none :
    ¬ (attachVertex H S).Adj none none := by
  simp [attachVertex, SimpleGraph.fromRel_adj, attachRel]

/-! ### Proper colourings are injective on a clique -/

/-- A proper assignment is injective on any clique. -/
lemma injOn_of_isClique (hS : H.IsClique (S : Set V)) {k : ℕ} {x : V → Fin k}
    (hx : IsProperAssignment H x) : Set.InjOn x (S : Set V) := by
  intro u hu v hv huv
  by_contra hne
  exact hx (hS hu hv hne) huv

/-- Hence a clique carries exactly `|S|` distinct colours. -/
lemma card_image_of_isClique (hS : H.IsClique (S : Set V)) {k : ℕ}
    {x : V → Fin k} (hx : IsProperAssignment H x) :
    (S.image x).card = S.card :=
  Finset.card_image_of_injOn (injOn_of_isClique hS hx)

/-- The colours available to the new vertex: everything off `S`'s palette. -/
lemma card_filter_avoiding {k : ℕ} {x : V → Fin k}
    (hcard : (S.image x).card = S.card) :
    (univ.filter fun c : Fin k => ∀ u ∈ S, c ≠ x u).card = k - S.card := by
  classical
  have hset : (univ.filter fun c : Fin k => ∀ u ∈ S, c ≠ x u) =
      univ \ S.image x := by
    ext c
    constructor
    · intro hc
      rw [mem_filter] at hc
      rw [mem_sdiff]
      refine ⟨mem_univ c, fun hmem => ?_⟩
      obtain ⟨u, hu, hxu⟩ := mem_image.mp hmem
      exact hc.2 u hu hxu.symm
    · intro hc
      rw [mem_sdiff] at hc
      rw [mem_filter]
      exact ⟨mem_univ c, fun u hu hcu =>
        hc.2 (mem_image.mpr ⟨u, hu, hcu.symm⟩)⟩
  rw [hset, Finset.card_sdiff, Finset.inter_univ, hcard]
  simp

/-! ### The count identity -/

/-- Assignments to `Option V` split into the new colour and the rest. -/
def optionArrowEquiv (V : Type*) (k : ℕ) :
    (Option V → Fin k) ≃ Fin k × (V → Fin k) where
  toFun y := (y none, fun v => y (some v))
  invFun p := fun a => Option.elim a p.1 p.2
  left_inv y := by
    funext a
    cases a <;> rfl
  right_inv p := rfl

/-- Under that splitting, properness becomes properness below plus avoidance. -/
lemma isProperAssignment_attachVertex_iff {k : ℕ} (y : Option V → Fin k) :
    IsProperAssignment (attachVertex H S) y ↔
      IsProperAssignment H (fun v => y (some v)) ∧
        ∀ u ∈ S, y none ≠ y (some u) := by
  constructor
  · intro h
    exact ⟨fun u v huv => h (by simpa using huv),
      fun u hu => h (by simpa using hu)⟩
  · rintro ⟨hx, hc⟩ a b hab
    match a, b with
    | some u, some v => exact hx (by simpa using hab)
    | some u, none => exact fun hh => hc u (by simpa using hab) hh.symm
    | none, some v => exact hc v (by simpa using hab)
    | none, none => exact absurd hab attachVertex_adj_none_none

/-- **Adjoining a vertex on a clique multiplies the count by `k - |S|`.** -/
theorem properAssignmentCount_attachVertex (hS : H.IsClique (S : Set V))
    (k : ℕ) :
    properAssignmentCount (attachVertex H S) k =
      (k - S.card) * properAssignmentCount H k := by
  classical
  have hsplit : properAssignmentCount (attachVertex H S) k =
      ∑ x : V → Fin k, ∑ c : Fin k,
        if IsProperAssignment H x ∧ ∀ u ∈ S, c ≠ x u then 1 else 0 := by
    rw [properAssignmentCount, Finset.card_filter,
      ← Equiv.sum_comp (optionArrowEquiv V k).symm]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun c _ => ?_
    congr 1
    exact propext (isProperAssignment_attachVertex_iff _)
  rw [hsplit, properAssignmentCount, Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : IsProperAssignment H x
  · have hinner : (∑ c : Fin k,
        if IsProperAssignment H x ∧ ∀ u ∈ S, c ≠ x u then (1 : ℕ) else 0) =
        (univ.filter fun c : Fin k => ∀ u ∈ S, c ≠ x u).card := by
      rw [Finset.card_filter]
      exact Finset.sum_congr rfl fun c _ => by simp [hx]
    rw [hinner, card_filter_avoiding (card_image_of_isClique hS hx), if_pos hx,
      mul_one]
  · rw [if_neg hx, mul_zero]
    exact Finset.sum_eq_zero fun c _ => if_neg fun h => hx h.1

/-- Proper assignments of `K s` are exactly the injections, so their number is
the falling factorial.  (Moved up from the pure-chordal development: it is a
statement about `properAssignmentCount` alone.) -/
lemma properAssignmentCount_top (s k : ℕ) :
    properAssignmentCount (⊤ : SimpleGraph (Fin s)) k =
      k.descFactorial s := by
  classical
  let P : (Fin s → Fin k) → Prop := fun x ↦ Function.Injective x
  have hpred :
      IsProperAssignment (⊤ : SimpleGraph (Fin s)) = P := by
    funext x
    apply propext
    constructor
    · intro hx u v hxy
      by_contra huv
      exact (hx (by simpa [SimpleGraph.top_adj] using huv)) hxy
    · intro hx u v huv hxy
      have huv' : u ≠ v := by
        simpa [SimpleGraph.top_adj] using huv
      exact huv' (hx hxy)
  unfold properAssignmentCount
  simp only [hpred]
  rw [← Fintype.card_subtype]
  calc
    Fintype.card {x : Fin s → Fin k // P x} =
        Fintype.card (Fin s ↪ Fin k) :=
      Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _)
    _ = k.descFactorial s := by
      simp

/-! ### The polynomial form -/

/-- With fewer colours than a clique has vertices, nothing is properly
colourable. -/
lemma properAssignmentCount_eq_zero_of_lt (hS : H.IsClique (S : Set V)) {k : ℕ}
    (hk : k < S.card) : properAssignmentCount H k = 0 := by
  classical
  rw [properAssignmentCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ hx
  have hcard := card_image_of_isClique hS hx
  have hle : (S.image x).card ≤ k := by
    calc (S.image x).card ≤ (univ : Finset (Fin k)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = k := by simp
  omega

open Polynomial in
/-- **The chromatic polynomial gains a factor `X - |S|`.**

This is the polynomial form of `properAssignmentCount_attachVertex`.  The
`k < |S|` case is not an exception: the clique `S` already forces the count
below to vanish there, so both sides are zero. -/
theorem isChromaticPolynomial_attachVertex {P : Polynomial ℝ}
    (hS : H.IsClique (S : Set V)) (hP : IsChromaticPolynomial H P) :
    IsChromaticPolynomial (attachVertex H S) ((X - C (S.card : ℝ)) * P) := by
  intro k
  rw [properAssignmentCount_attachVertex hS, eval_mul, eval_sub, eval_X, eval_C,
    hP k]
  rcases lt_or_ge k S.card with hk | hk
  · rw [properAssignmentCount_eq_zero_of_lt hS hk]
    have : (k - S.card : ℕ) = 0 := by omega
    rw [this]
    simp
  · have hcast : ((k - S.card : ℕ) : ℝ) = (k : ℝ) - (S.card : ℝ) :=
      Nat.cast_sub hk
    push_cast [hcast]
    ring


/-! ### Decidability, and transport onto a concrete labelling

An attachment lives on `Option V`, while an Atlas module states its graph by an
edge list on `Fin n`.  These two facts bridge the gap: adjacency of an
attachment is decidable, so the isomorphism can be discharged by `decide`, and
both chromatic specifications then transport along it.
-/

instance attachRel_decidable (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) : DecidableRel (attachRel H S)
  | some u, some v => inferInstanceAs (Decidable (H.Adj u v))
  | some u, none => inferInstanceAs (Decidable (u ∈ S))
  | none, some _ => inferInstanceAs (Decidable False)
  | none, none => inferInstanceAs (Decidable False)

instance attachVertex_decidableAdj (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) : DecidableRel (attachVertex H S).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

variable {V' : Type*} [Fintype V'] [DecidableEq V'] {H' : SimpleGraph V'}

/-- The attachment count, read on a graph presented some other way. -/
theorem properAssignmentCount_of_attachIso (φ : attachVertex H S ≃g H')
    (hS : H.IsClique (S : Set V)) (k : ℕ) :
    properAssignmentCount H' k = (k - S.card) * properAssignmentCount H k := by
  rw [← properAssignmentCount_iso φ k, properAssignmentCount_attachVertex hS]

open Polynomial in
/-- The attachment chromatic polynomial, read on a graph presented some other
way.  This is the form an Atlas module uses. -/
theorem isChromaticPolynomial_of_attachIso {P : Polynomial ℝ}
    (φ : attachVertex H S ≃g H') (hS : H.IsClique (S : Set V))
    (hP : IsChromaticPolynomial H P) :
    IsChromaticPolynomial H' ((X - C (S.card : ℝ)) * P) :=
  IsChromaticPolynomial.of_iso φ.symm (isChromaticPolynomial_attachVertex hS hP)

/-- A complete graph is a clique on all of its vertices. -/
lemma isClique_top_univ (n : ℕ) :
    (⊤ : SimpleGraph (Fin n)).IsClique ((univ : Finset (Fin n)) : Set (Fin n)) := by
  intro u _ v _ huv
  simpa using huv

open Polynomial in
/-- The chromatic polynomial of `K n` is the falling factorial. -/
theorem isChromaticPolynomial_top (n : ℕ) :
    IsChromaticPolynomial (⊤ : SimpleGraph (Fin n))
      (∏ i ∈ range n, (X - C (i : ℝ))) := by
  intro k
  rw [properAssignmentCount_top, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ]
      rcases lt_or_ge k m with hk | hk
      · have h1 : k.descFactorial m = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hk
        have h2 : k.descFactorial (m + 1) = 0 :=
          Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
        rw [Nat.descFactorial_succ] at h2
        rw [h1]
        simp
      · rw [Nat.cast_mul, Nat.cast_sub hk]
        push_cast
        ring


end Taeyoung
