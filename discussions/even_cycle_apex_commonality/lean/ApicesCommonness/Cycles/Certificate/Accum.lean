import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

/-!
# Packed orbit accumulators

DEVIATIONS X3 (ii).  Identity (C) of `prop:checked-data` is checked on orbit-indexed coefficient
vectors.  A vector is accumulated in two naturals `pos, neg` holding one 128-bit slot per orbit
(`accStep`, forced at every step so that the kernel keeps no chain of unevaluated additions), and a
third natural `mass = ∑ |c|`.

Soundness (`list_sum_eq_of_packed`): if two lists of `(orbit, coefficient)` items have the same
packed value `∑ c · 2^{128 o}` and total mass `< 2^128`, then their orbit-wise coefficient sums
agree (uniqueness of base-`2^128` digits, `digits_zero`), hence `∑ c · f(o)` agrees for every `f`.
-/

open Finset

namespace ApicesCommonness

/-- One forced update of the packed accumulator `(pos, neg, mass)` by `c` in slot `o`. -/
def accStep (p q m o : ℕ) (c : ℤ) (k : ℕ → ℕ → ℕ → Bool) : Bool :=
  match c with
  | .ofNat x =>
      let p' := Nat.add p (Nat.shiftLeft x (Nat.mul 128 o))
      let m' := Nat.add m x
      match Nat.beq p' m' with
      | true => k p' q m'
      | false => k p' q m'
  | .negSucc x =>
      let q' := Nat.add q (Nat.shiftLeft (Nat.succ x) (Nat.mul 128 o))
      let m' := Nat.add m (Nat.succ x)
      match Nat.beq q' m' with
      | true => k p q' m'
      | false => k p q' m'

/-- Accumulate a list of `(orbit, coefficient)` items. -/
def accList : List (ℕ × ℤ) → ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → Bool) → Bool
  | [], p, q, m, k => k p q m
  | x :: l, p, q, m, k => accStep p q m x.1 x.2 fun p q m => accList l p q m k

/-- The positive part of the packed value. -/
def posOf (l : List (ℕ × ℤ)) : ℕ := (l.map fun x => x.2.toNat * 2 ^ (128 * x.1)).sum

/-- The negative part of the packed value. -/
def negOf (l : List (ℕ × ℤ)) : ℕ := (l.map fun x => (-x.2).toNat * 2 ^ (128 * x.1)).sum

/-- The total mass `∑ |c|`. -/
def massOf (l : List (ℕ × ℤ)) : ℕ := (l.map fun x => x.2.natAbs).sum

lemma accStep_eq (p q m o : ℕ) (c : ℤ) (k : ℕ → ℕ → ℕ → Bool) :
    accStep p q m o c k
      = k (p + c.toNat * 2 ^ (128 * o)) (q + (-c).toNat * 2 ^ (128 * o)) (m + c.natAbs) := by
  cases c with
  | ofNat x =>
    simp only [accStep]
    split <;> simp [Nat.shiftLeft_eq]
  | negSucc x =>
    simp only [accStep]
    split <;> simp [Int.neg_negSucc, Nat.shiftLeft_eq]

lemma accList_eq (l : List (ℕ × ℤ)) (p q m : ℕ) (k : ℕ → ℕ → ℕ → Bool) :
    accList l p q m k = k (p + posOf l) (q + negOf l) (m + massOf l) := by
  induction l generalizing p q m with
  | nil => simp [accList, posOf, negOf, massOf]
  | cons x l ih =>
    rw [accList, accStep_eq, ih]
    simp only [posOf, negOf, massOf, List.map_cons, List.sum_cons]
    congr 1 <;> ring

lemma accList_append (l₁ l₂ : List (ℕ × ℤ)) (p q m : ℕ) (k : ℕ → ℕ → ℕ → Bool) :
    accList (l₁ ++ l₂) p q m k = accList l₁ p q m fun p q m => accList l₂ p q m k := by
  rw [accList_eq, accList_eq, accList_eq]
  simp only [posOf, negOf, massOf, List.map_append, List.sum_append]
  congr 1 <;> ring

/-- The packed value `∑ c · 2^{128 o}` is `pos − neg`. -/
lemma posOf_sub_negOf (l : List (ℕ × ℤ)) :
    (posOf l : ℤ) - negOf l = (l.map fun x => x.2 * (2 : ℤ) ^ (128 * x.1)).sum := by
  induction l with
  | nil => simp [posOf, negOf]
  | cons x l ih =>
    simp only [posOf, negOf, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat] at ih ⊢
    rw [← ih]
    have := Int.toNat_sub_toNat_neg x.2
    linear_combination (2 : ℤ) ^ (128 * x.1) * this

/-! ### Uniqueness of digits -/

lemma abs_digits_le (B : ℤ) (hB : 0 < B) : ∀ (N : ℕ) (D : ℕ → ℤ), (∀ o < N, |D o| < B) →
    |∑ o ∈ range N, D o * B ^ o| ≤ B ^ N - 1
  | 0, D, _ => by simp
  | N + 1, D, hD => by
    rw [sum_range_succ]
    have ih := abs_digits_le B hB N D fun o ho => hD o (by omega)
    have hN : |D N| + 1 ≤ B := Int.add_one_le_iff.mpr (hD N (by omega))
    have hpow : 0 < B ^ N := pow_pos hB N
    calc |∑ o ∈ range N, D o * B ^ o + D N * B ^ N|
        ≤ |∑ o ∈ range N, D o * B ^ o| + |D N * B ^ N| := abs_add_le _ _
      _ ≤ (B ^ N - 1) + (B - 1) * B ^ N := by
          rw [abs_mul, abs_of_pos hpow]
          nlinarith
      _ = B ^ (N + 1) - 1 := by ring

/-- **Uniqueness of base-`B` digits.**  If `∑_{o < N} D_o B^o = 0` and every `|D_o| < B`, then
every `D_o = 0`. -/
lemma digits_zero (B : ℤ) (hB : 0 < B) : ∀ (N : ℕ) (D : ℕ → ℤ), (∀ o < N, |D o| < B) →
    ∑ o ∈ range N, D o * B ^ o = 0 → ∀ o < N, D o = 0
  | 0, _, _, _ => fun o ho => absurd ho (Nat.not_lt_zero _)
  | N + 1, D, hD, hs => by
    rw [sum_range_succ] at hs
    have hle := abs_digits_le B hB N D fun o ho => hD o (by omega)
    have hpow : 0 < B ^ N := pow_pos hB N
    have hDN : D N = 0 := by
      have h1 : D N * B ^ N = -∑ o ∈ range N, D o * B ^ o := by linarith
      have h2 : |D N * B ^ N| ≤ B ^ N - 1 := by rw [h1, abs_neg]; exact hle
      rw [abs_mul, abs_of_pos hpow] at h2
      have h3 : |D N| < 1 := by nlinarith
      have := abs_lt.mp h3
      omega
    rw [hDN, zero_mul, add_zero] at hs
    have ih := digits_zero B hB N D (fun o ho => hD o (by omega)) hs
    intro o ho
    rcases Nat.lt_succ_iff_lt_or_eq.mp ho with ho | rfl
    · exact ih o ho
    · exact hDN

/-! ### Orbit-wise coefficient sums -/

/-- The coefficient sum of orbit `o`. -/
def fiberSum (l : List (ℕ × ℤ)) (o : ℕ) : ℤ := (l.map fun x => if x.1 = o then x.2 else 0).sum

lemma list_sum_fiber {R : Type*} [CommRing R] (g : ℕ → R) (N : ℕ) :
    ∀ l : List (ℕ × ℤ), (∀ x ∈ l, x.1 < N) →
      (l.map fun x => (x.2 : R) * g x.1).sum = ∑ o ∈ range N, (fiberSum l o : R) * g o
  | [], _ => by simp [fiberSum]
  | x :: l, hl => by
    rw [List.map_cons, List.sum_cons,
      list_sum_fiber g N l fun y hy => hl y (List.mem_cons_of_mem _ hy)]
    have hx : x.1 < N := hl x List.mem_cons_self
    simp only [fiberSum, List.map_cons, List.sum_cons, Int.cast_add, add_mul, sum_add_distrib]
    congr 1
    simp [Int.cast_ite, ite_mul, hx]

lemma abs_fiberSum_le (o : ℕ) : ∀ l : List (ℕ × ℤ), |fiberSum l o| ≤ (massOf l : ℤ)
  | [] => by simp [fiberSum, massOf]
  | x :: l => by
    have ih := abs_fiberSum_le o l
    simp only [fiberSum, massOf, List.map_cons, List.sum_cons, Nat.cast_add] at ih ⊢
    calc |(if x.1 = o then x.2 else 0) + (l.map fun x => if x.1 = o then x.2 else 0).sum|
        ≤ |if x.1 = o then x.2 else 0| + |(l.map fun x => if x.1 = o then x.2 else 0).sum| :=
          abs_add_le _ _
      _ ≤ (x.2.natAbs : ℤ) + ((l.map fun x => x.2.natAbs).sum : ℕ) := by
          refine add_le_add ?_ ih
          split_ifs <;> simp

private lemma exists_bound (l : List (ℕ × ℤ)) : ∃ N, ∀ x ∈ l, x.1 < N := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons x l ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨max N (x.1 + 1), fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · omega
    · have := hN y hy
      omega

/-- **Soundness of the packed comparison.**  Equal packed values and total mass `< 2^128` give equal
weighted sums for every weight function. -/
theorem list_sum_eq_of_packed {I J : List (ℕ × ℤ)}
    (hsum : (I.map fun x => x.2 * (2 : ℤ) ^ (128 * x.1)).sum
      = (J.map fun x => x.2 * (2 : ℤ) ^ (128 * x.1)).sum)
    (hmass : massOf I + massOf J < 2 ^ 128) (f : ℕ → ℝ) :
    (I.map fun x => (x.2 : ℝ) * f x.1).sum = (J.map fun x => (x.2 : ℝ) * f x.1).sum := by
  obtain ⟨N, hN⟩ := exists_bound (I ++ J)
  have hI : ∀ x ∈ I, x.1 < N := fun x hx => hN x (List.mem_append_left _ hx)
  have hJ : ∀ x ∈ J, x.1 < N := fun x hx => hN x (List.mem_append_right _ hx)
  have hB : (0 : ℤ) < 2 ^ 128 := by positivity
  have hv : ∀ o < N, fiberSum I o = fiberSum J o := by
    have hz := digits_zero (2 ^ 128) hB N (fun o => fiberSum I o - fiberSum J o) (fun o _ => by
        calc |fiberSum I o - fiberSum J o| ≤ |fiberSum I o| + |fiberSum J o| := abs_sub _ _
          _ ≤ (massOf I : ℤ) + massOf J := add_le_add (abs_fiberSum_le o I) (abs_fiberSum_le o J)
          _ < 2 ^ 128 := by exact_mod_cast hmass)
      (by
        have h1 := list_sum_fiber (R := ℤ) (fun o => (2 : ℤ) ^ (128 * o)) N I hI
        have h2 := list_sum_fiber (R := ℤ) (fun o => (2 : ℤ) ^ (128 * o)) N J hJ
        simp only [Int.cast_id] at h1 h2
        rw [h1, h2] at hsum
        simp only [sub_mul, sum_sub_distrib, ← pow_mul]
        rw [hsum, sub_self])
    intro o ho
    have := hz o ho
    linarith
  rw [list_sum_fiber f N I hI, list_sum_fiber f N J hJ]
  exact sum_congr rfl fun o ho => by rw [hv o (mem_range.mp ho)]

/-! ### Scaling -/

/-- Multiply every coefficient by `s`. -/
def scaleItems (s : ℕ) (l : List (ℕ × ℤ)) : List (ℕ × ℤ) := l.map fun x => (x.1, (s : ℤ) * x.2)

lemma scaleItems_packed (s : ℕ) (l : List (ℕ × ℤ)) :
    ((scaleItems s l).map fun x => x.2 * (2 : ℤ) ^ (128 * x.1)).sum
      = s * ((posOf l : ℤ) - negOf l) := by
  rw [posOf_sub_negOf, scaleItems, List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp_apply]
  ring

lemma massOf_scaleItems (s : ℕ) (l : List (ℕ × ℤ)) : massOf (scaleItems s l) = s * massOf l := by
  simp only [massOf, scaleItems, List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp [Int.natAbs_mul]

lemma sum_scaleItems (s : ℕ) (l : List (ℕ × ℤ)) (f : ℕ → ℝ) :
    ((scaleItems s l).map fun x => (x.2 : ℝ) * f x.1).sum
      = s * (l.map fun x => (x.2 : ℝ) * f x.1).sum := by
  rw [scaleItems, List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp_apply]
  push_cast
  ring

lemma packed_append (l₁ l₂ : List (ℕ × ℤ)) :
    ((l₁ ++ l₂).map fun x => x.2 * (2 : ℤ) ^ (128 * x.1)).sum
      = (l₁.map fun x => x.2 * (2 : ℤ) ^ (128 * x.1)).sum
        + (l₂.map fun x => x.2 * (2 : ℤ) ^ (128 * x.1)).sum := by
  rw [List.map_append, List.sum_append]

lemma massOf_append (l₁ l₂ : List (ℕ × ℤ)) : massOf (l₁ ++ l₂) = massOf l₁ + massOf l₂ := by
  simp [massOf]

end ApicesCommonness
