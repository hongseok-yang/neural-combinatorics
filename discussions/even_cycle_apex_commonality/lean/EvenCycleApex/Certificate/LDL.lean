import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.BigOperators

/-!
# Rational `LDLᵀ` factorizations

Blueprint `lem:ldl-soundness`.  A certificate matrix `A` (integer entries, a list of rows) comes with
rational data `L` (the strictly lower part of each row) and `δ`.  The checker `factorOK` (written for
kernel reduction: structural recursion, core `Rat` via `mkRat`) verifies `δₕ > 0` and
`A_ij = ∑ₕ L_ih δₕ L_jh` for all `i, j`, where row `i` of `L` is its strict part followed by `1`.

Only the identity and `δ ≥ 0` are used for positivity (`factorOK_sound`):
`xᵀ A x = ∑ₕ δₕ (∑ᵢ xᵢ L_ih)² ≥ 0` (plan D6: Sylvester's criterion is not needed).
-/

open Finset

namespace EvenCycleApex

/-- A rational from a numerator/denominator pair. -/
def ratOf (x : ℤ × ℕ) : ℚ := mkRat x.1 x.2

/-- `∑ₕ aₕ dₕ bₕ`, truncated at the shortest list. -/
def dot3 : List ℚ → List ℚ → List ℚ → ℚ
  | a :: as, d :: ds, b :: bs => a * d * b + dot3 as ds bs
  | _, _, _ => 0

/-- Lockstep test of two lists of equal length. -/
def all2 {α β : Type*} (f : α → β → Bool) : List α → List β → Bool
  | a :: as, b :: bs => f a b && all2 f as bs
  | [], [] => true
  | _, _ => false

/-- The `LDLᵀ` check of one matrix. -/
def factorOK (A : List (List ℤ)) (strict : List (List (ℤ × ℕ))) (diag : List (ℤ × ℕ)) : Bool :=
  let Lq := strict.map fun r => r.map ratOf ++ [1]
  let δ := diag.map ratOf
  δ.all (fun d => decide (0 < d)) &&
    all2 (fun (Ai : List ℤ) (Li : List ℚ) =>
      all2 (fun (a : ℤ) (Lj : List ℚ) => dot3 Li δ Lj == (a : ℚ)) Ai Lq) A Lq

lemma all2_sound {α β : Type*} {f : α → β → Bool} (da : α) (db : β) :
    ∀ {l₁ : List α} {l₂ : List β}, all2 f l₁ l₂ = true →
      l₁.length = l₂.length ∧ ∀ i < l₁.length, f (l₁.getD i da) (l₂.getD i db) = true
  | [], [], _ => by simp
  | [], _ :: _, h => by simp [all2] at h
  | _ :: _, [], h => by simp [all2] at h
  | a :: as, b :: bs, h => by
    simp only [all2, Bool.and_eq_true] at h
    obtain ⟨hlen, hall⟩ := all2_sound da db h.2
    refine ⟨by simp [hlen], fun i hi => ?_⟩
    cases i with
    | zero => simpa using h.1
    | succ i => simpa using hall i (by simpa using hi)

lemma dot3_eq_sum : ∀ (l₁ l₂ l₃ : List ℚ) (N : ℕ), l₂.length ≤ N →
    dot3 l₁ l₂ l₃ = ∑ h ∈ range N, l₁.getD h 0 * l₂.getD h 0 * l₃.getD h 0
  | l₁, [], l₃, N, _ => by
    rw [show dot3 l₁ [] l₃ = 0 by cases l₁ <;> cases l₃ <;> rfl]
    simp
  | [], d :: ds, l₃, N, _ => by simp [dot3]
  | a :: as, d :: ds, [], N, _ => by simp [dot3]
  | a :: as, d :: ds, b :: bs, N, hN => by
    obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at hN; omega⟩
    rw [dot3, sum_range_succ', dot3_eq_sum as ds bs N (by simp at hN; omega)]
    simp [add_comm]

/-- `xᵀ A x = ∑ₕ δₕ (∑ᵢ xᵢ L_ih)²`. -/
lemma quad_nonneg_of_factor {n D : ℕ} {A L : ℕ → ℕ → ℝ} {δ : ℕ → ℝ} (hδ : ∀ h < D, 0 ≤ δ h)
    (hA : ∀ i < n, ∀ j < n, A i j = ∑ h ∈ range D, L i h * δ h * L j h) (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ range n, ∑ j ∈ range n, x i * A i j * x j := by
  have : ∑ i ∈ range n, ∑ j ∈ range n, x i * A i j * x j
      = ∑ h ∈ range D, δ h * (∑ i ∈ range n, x i * L i h) ^ 2 := by
    calc ∑ i ∈ range n, ∑ j ∈ range n, x i * A i j * x j
        = ∑ i ∈ range n, ∑ j ∈ range n, ∑ h ∈ range D, δ h * (x i * L i h) * (x j * L j h) := by
          refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
          rw [hA i (mem_range.mp hi) j (mem_range.mp hj), mul_sum, sum_mul]
          exact sum_congr rfl fun h _ => by ring
      _ = ∑ i ∈ range n, ∑ h ∈ range D, ∑ j ∈ range n, δ h * (x i * L i h) * (x j * L j h) :=
          sum_congr rfl fun i _ => sum_comm
      _ = ∑ h ∈ range D, ∑ i ∈ range n, ∑ j ∈ range n, δ h * (x i * L i h) * (x j * L j h) :=
          sum_comm
      _ = _ := sum_congr rfl fun h _ => by
          rw [sq, sum_mul_sum, mul_sum]
          refine sum_congr rfl fun i _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun j _ => by ring
  rw [this]
  exact sum_nonneg fun h hh => mul_nonneg (hδ h (mem_range.mp hh)) (sq_nonneg _)

/-- **`lem:ldl-soundness`.**  A checked factorization makes the matrix positive semidefinite. -/
theorem factorOK_sound {A : List (List ℤ)} {strict : List (List (ℤ × ℕ))} {diag : List (ℤ × ℕ)}
    (h : factorOK A strict diag = true) (x : ℕ → ℝ) :
    0 ≤ ∑ a ∈ range A.length, ∑ b ∈ range A.length,
      x a * (((A.getD a []).getD b 0 : ℤ) : ℝ) * x b := by
  simp only [factorOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hpos, hrows⟩ := h
  set Lq := strict.map fun r => r.map ratOf ++ [1] with hLq
  set δ := diag.map ratOf with hδ
  obtain ⟨hlen, hrow⟩ := all2_sound [] [] hrows
  refine quad_nonneg_of_factor (D := δ.length)
    (L := fun i h => (((Lq.getD i []).getD h 0 : ℚ) : ℝ)) (δ := fun h => ((δ.getD h 0 : ℚ) : ℝ))
    (fun i hi => ?_) (fun i hi j hj => ?_) x
  · have hmem : δ.getD i 0 ∈ δ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.getElem_mem hi
    exact_mod_cast (hpos _ hmem).le
  · obtain ⟨hlen', hent⟩ := all2_sound 0 [] (hrow i hi)
    have hj' : j < (A.getD i []).length := by rw [hlen', ← hlen]; exact hj
    have he := hent j hj'
    simp only [beq_iff_eq] at he
    rw [dot3_eq_sum _ _ _ δ.length le_rfl] at he
    rw [show (((A.getD i []).getD j 0 : ℤ) : ℝ) = ((((A.getD i []).getD j 0 : ℤ) : ℚ) : ℝ) by
      push_cast; rfl, ← he, Rat.cast_sum]
    simp only [Rat.cast_mul]

end EvenCycleApex
