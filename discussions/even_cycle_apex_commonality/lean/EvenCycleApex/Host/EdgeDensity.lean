import EvenCycleApex.Host.Defs
import EvenCycleApex.Graph.DensityAlgebra
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

/-!
# Densities of edge sets on a finite host, and their algebra

On the host `(Fin d, w)`, an edge set `E : Finset (Fin v × Fin v)` (pairs of formal vertices, in any
orientation) has density

```
  edgeDensity w E L = ∑_{x : Fin v → Fin d} (∏ᵢ w(xᵢ)) ∏_{(i, j) ∈ E} L(xᵢ, xⱼ).
```

`hostDensity w F L` is `edgeDensity w (edgePairs F) L` by definition.  Working with raw edge sets
makes the finite part of blueprint `lem:density-algebra` a matter of reindexing sums:

* `edgeDensity_map_equiv` — relabelling the vertices by a bijection;
* `edgeDensity_append` — the density of a disjoint union of edge sets on `Fin a` and `Fin b`
  (placed on `Fin (a + b)` by `Fin.castAdd` and `Fin.natAdd`) is the product; with the second edge
  set empty this adds isolated vertices (`edgeDensity_castAdd`);
* `colour_parity_expansion`, `edgeDensity_colour_even`, `edgeDensity_colour_odd` — blueprint
  `lem:parity`: averaging `∏ (1 + σ U_e)` over `σ = ±1`, with and without the factor `σ`, keeps the
  even, respectively odd, edge subsets.
-/

open Finset

namespace EvenCycleApex

variable {d : ℕ}

/-- The density of an edge set on the host `(Fin d, w)`. -/
def edgeDensity (w : Fin d → ℝ) {v : ℕ} (E : Finset (Fin v × Fin v)) (L : Fin d → Fin d → ℝ) : ℝ :=
  ∑ x : Fin v → Fin d, (∏ i, w (x i)) * ∏ p ∈ E, L (x p.1) (x p.2)

lemma hostDensity_eq_edgeDensity (w : Fin d → ℝ) {v : ℕ} (F : SimpleGraph (Fin v))
    [DecidableRel F.Adj] (L : Fin d → Fin d → ℝ) :
    hostDensity w F L = edgeDensity w (edgePairs F) L := rfl

/-- Summing out all vertices: `∑_x ∏ᵢ w(xᵢ) = (∑ w)^v`. -/
lemma sum_prod_weights (w : Fin d → ℝ) (v : ℕ) :
    ∑ x : Fin v → Fin d, ∏ i, w (x i) = (∑ j, w j) ^ v := by
  rw [← Fintype.prod_sum (fun (_ : Fin v) (j : Fin d) => w j)]
  simp

lemma edgeDensity_empty (w : Fin d → ℝ) (hw : ∑ j, w j = 1) (v : ℕ) (L : Fin d → Fin d → ℝ) :
    edgeDensity w (∅ : Finset (Fin v × Fin v)) L = 1 := by
  simp [edgeDensity, sum_prod_weights, hw]

/-! ### Relabelling -/

/-- **Relabelling.**  Moving the formal vertices along a bijection does not change the density. -/
lemma edgeDensity_map_equiv (w : Fin d → ℝ) {v v' : ℕ} (e : Fin v ≃ Fin v')
    (E : Finset (Fin v × Fin v)) (L : Fin d → Fin d → ℝ) :
    edgeDensity w (E.map (e.toEmbedding.prodMap e.toEmbedding)) L = edgeDensity w E L := by
  unfold edgeDensity
  refine (Fintype.sum_equiv (e.arrowCongr (Equiv.refl (Fin d))) _ _ fun x => ?_).symm
  have hx : ∀ i, (e.arrowCongr (Equiv.refl (Fin d)) x) (e i) = x i := fun i => by
    simp [Equiv.arrowCongr_apply]
  rw [prod_map, ← e.prod_comp (fun i' => w ((e.arrowCongr (Equiv.refl (Fin d)) x) i'))]
  simp only [Function.Embedding.coe_prodMap, Prod.map_fst, Prod.map_snd, Equiv.coe_toEmbedding,
    hx]

/-- Two sorted pairs with the same unordered pair are equal. -/
lemma eq_of_sym2_eq_of_lt {v : ℕ} {p q : Fin v × Fin v} (hp : p.1 < p.2) (hq : q.1 < q.2)
    (h : s(p.1, p.2) = s(q.1, q.2)) : p = q := by
  rcases Sym2.eq_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Prod.ext h₁ h₂
  · exact absurd (h₁ ▸ h₂ ▸ hq) (not_lt.mpr hp.le)

/-- **Relabelling a sorted edge set** (pairs `i < j`) by a permutation, for a symmetric kernel:
the image edge `{π i, π j}` is again written with its smaller end first. -/
lemma edgeDensity_image_sortPair (w : Fin d → ℝ) {v : ℕ} {L : Fin d → Fin d → ℝ}
    (hL : ∀ i j, L i j = L j i) (π : Fin v ≃ Fin v) {E : Finset (Fin v × Fin v)}
    (hE : ∀ p ∈ E, p.1 < p.2) :
    edgeDensity w (E.image fun p => sortPair (π p.1) (π p.2)) L = edgeDensity w E L := by
  rw [← edgeDensity_map_equiv w π E L]
  unfold edgeDensity
  refine sum_congr rfl fun x _ => ?_
  congr 1
  rw [prod_image, prod_map]
  · refine prod_congr rfl fun p _ => ?_
    simp only [Function.Embedding.coe_prodMap, Prod.map_fst, Prod.map_snd, Equiv.coe_toEmbedding]
    exact apply_sortPair (fun a b => L (x a) (x b)) (fun a b => hL _ _) _ _
  · intro p hp q hq hpq
    have hs := congrArg (fun r : Fin v × Fin v => s(r.1, r.2)) hpq
    simp only [sym2_sortPair_eq] at hs
    have hs' : s(p.1, p.2) = s(q.1, q.2) := by
      have := congrArg (Sym2.map π.symm) hs
      simpa [Sym2.map_mk] using this
    exact eq_of_sym2_eq_of_lt (hE p hp) (hE q hq) hs'

/-- **Isomorphic edge sets have equal densities** (symmetric kernel, sorted pairs).  The permutation
is only asserted to exist, so for concrete small graphs it can be found by `decide`. -/
lemma edgeDensity_eq_of_iso (w : Fin d → ℝ) {v : ℕ} {L : Fin d → Fin d → ℝ}
    (hL : ∀ i j, L i j = L j i) {F G : Finset (Fin v × Fin v)} (hF : ∀ p ∈ F, p.1 < p.2)
    (h : ∃ π : Equiv.Perm (Fin v), F.image (fun p => sortPair (π p.1) (π p.2)) = G) :
    edgeDensity w F L = edgeDensity w G L := by
  obtain ⟨π, rfl⟩ := h
  exact (edgeDensity_image_sortPair w hL π hF).symm

/-! ### Disjoint unions and isolated vertices -/

section Append

variable {a b : ℕ}

/-- `Fin (a + b) → α` as a pair of functions on `Fin a` and `Fin b`. -/
def appendEquiv (a b : ℕ) (α : Type*) : (Fin a → α) × (Fin b → α) ≃ (Fin (a + b) → α) where
  toFun p := Fin.append p.1 p.2
  invFun x := (fun i => x (Fin.castAdd b i), fun j => x (Fin.natAdd a j))
  left_inv p := by ext i <;> simp
  right_inv x := Fin.append_castAdd_natAdd

/-- The edges of `E` on the first `a` vertices of `Fin (a + b)`. -/
def castAddEdges (b : ℕ) (E : Finset (Fin a × Fin a)) : Finset (Fin (a + b) × Fin (a + b)) :=
  E.map ((Fin.castAddEmb b).prodMap (Fin.castAddEmb b))

/-- The edges of `E` on the last `b` vertices of `Fin (a + b)`. -/
def natAddEdges (a : ℕ) (E : Finset (Fin b × Fin b)) : Finset (Fin (a + b) × Fin (a + b)) :=
  E.map ((Fin.natAddEmb a).prodMap (Fin.natAddEmb a))

lemma disjoint_castAddEdges_natAddEdges (E₁ : Finset (Fin a × Fin a))
    (E₂ : Finset (Fin b × Fin b)) : Disjoint (castAddEdges b E₁) (natAddEdges a E₂) := by
  rw [Finset.disjoint_left]
  intro p h₁ h₂
  simp only [castAddEdges, natAddEdges, mem_map] at h₁ h₂
  obtain ⟨q, _, rfl⟩ := h₁
  obtain ⟨r, _, hr⟩ := h₂
  have h := congrArg (fun p : Fin (a + b) × Fin (a + b) => (p.1 : ℕ)) hr
  simp at h
  have := q.1.isLt
  omega

/-- **Disjoint union.**  The density of two edge sets on disjoint vertex blocks is the product of
their densities. -/
lemma edgeDensity_append (w : Fin d → ℝ) (E₁ : Finset (Fin a × Fin a))
    (E₂ : Finset (Fin b × Fin b)) (L : Fin d → Fin d → ℝ) :
    edgeDensity w (castAddEdges b E₁ ∪ natAddEdges a E₂) L
      = edgeDensity w E₁ L * edgeDensity w E₂ L := by
  unfold edgeDensity
  rw [sum_mul_sum, ← Fintype.sum_prod_type', ← (appendEquiv a b (Fin d)).sum_comp]
  refine sum_congr rfl fun p _ => ?_
  obtain ⟨y, z⟩ := p
  simp only [appendEquiv, Equiv.coe_fn_mk]
  rw [prod_union (disjoint_castAddEdges_natAddEdges E₁ E₂), Fin.prod_univ_add]
  simp only [castAddEdges, natAddEdges, prod_map, Function.Embedding.coe_prodMap, Prod.map_fst,
    Prod.map_snd, Fin.castAddEmb_apply, Fin.natAddEmb_apply, Fin.append_left, Fin.append_right]
  ring

/-- **Isolated vertices.**  Adding `b` isolated vertices does not change the density. -/
lemma edgeDensity_castAdd (w : Fin d → ℝ) (hw : ∑ j, w j = 1) (E : Finset (Fin a × Fin a))
    (L : Fin d → Fin d → ℝ) :
    edgeDensity w (castAddEdges b E) L = edgeDensity w E L := by
  have h := edgeDensity_append w E (∅ : Finset (Fin b × Fin b)) L
  rw [edgeDensity_empty w hw, mul_one] at h
  rw [← h]
  congr 1
  simp [natAddEdges]

end Append

/-! ### Colour parity (`lem:parity`) -/

/-- **`lem:parity`.**  Averaging `∏_{e ∈ E} (1 + σ u_e)` over `σ = ±1` keeps the even edge
subsets. -/
theorem colour_parity_expansion {ι : Type*} [DecidableEq ι] (E : Finset ι) (u : ι → ℝ) :
    (∏ e ∈ E, (1 + 1 * u e) + ∏ e ∈ E, (1 + -1 * u e)) / 2
      = ∑ F ∈ E.powerset.filter (fun F => Even F.card), ∏ e ∈ F, u e := by
  simp only [prod_one_add, one_mul, neg_one_mul, prod_neg, ← sum_add_distrib, sum_div,
    sum_filter]
  refine sum_congr rfl fun F _ => ?_
  rcases Nat.even_or_odd F.card with h | h
  · rw [if_pos h, h.neg_one_pow]; ring
  · rw [if_neg (Nat.not_even_iff_odd.mpr h), h.neg_one_pow]; ring

/-- **`lem:parity`, signed.**  With the extra factor `σ`, the odd edge subsets remain. -/
theorem colour_parity_expansion_odd {ι : Type*} [DecidableEq ι] (E : Finset ι) (u : ι → ℝ) :
    (∏ e ∈ E, (1 + 1 * u e) - ∏ e ∈ E, (1 + -1 * u e)) / 2
      = ∑ F ∈ E.powerset.filter (fun F => Odd F.card), ∏ e ∈ F, u e := by
  simp only [prod_one_add, one_mul, neg_one_mul, prod_neg, ← sum_sub_distrib, sum_div,
    sum_filter]
  refine sum_congr rfl fun F _ => ?_
  rcases Nat.even_or_odd F.card with h | h
  · rw [if_neg (Nat.not_odd_iff_even.mpr h), h.neg_one_pow]; ring
  · rw [if_pos h, h.neg_one_pow]; ring

variable (w : Fin d → ℝ) {v : ℕ} (E : Finset (Fin v × Fin v)) (U : Fin d → Fin d → ℝ)

/-- The colour average of the density of `E` is the sum of the densities of its even subsets. -/
theorem edgeDensity_colour_even :
    (edgeDensity w E (colourKernel 1 U) + edgeDensity w E (colourKernel (-1) U)) / 2
      = ∑ F ∈ E.powerset.filter (fun F => Even F.card), edgeDensity w F U := by
  unfold edgeDensity colourKernel
  rw [← sum_add_distrib, sum_div]
  simp_rw [← mul_add, mul_div_assoc]
  rw [sum_comm' (t' := univ) (s' := fun _ => E.powerset.filter (fun F => Even F.card))
    (by simp)]
  refine sum_congr rfl fun x _ => ?_
  rw [colour_parity_expansion E (fun p => U (x p.1) (x p.2)), mul_sum]

/-- The signed colour average keeps the odd subsets. -/
theorem edgeDensity_colour_odd :
    (edgeDensity w E (colourKernel 1 U) - edgeDensity w E (colourKernel (-1) U)) / 2
      = ∑ F ∈ E.powerset.filter (fun F => Odd F.card), edgeDensity w F U := by
  unfold edgeDensity colourKernel
  rw [← sum_sub_distrib, sum_div]
  simp_rw [← mul_sub, mul_div_assoc]
  rw [sum_comm' (t' := univ) (s' := fun _ => E.powerset.filter (fun F => Odd F.card))
    (by simp)]
  refine sum_congr rfl fun x _ => ?_
  rw [colour_parity_expansion_odd E (fun p => U (x p.1) (x p.2)), mul_sum]

end EvenCycleApex
