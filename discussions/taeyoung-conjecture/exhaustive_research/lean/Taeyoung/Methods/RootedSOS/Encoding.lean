import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Indexes
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Bounded positional encodings for exact matrix products

Large certificate rows are checked through base encodings.  Equality of two
encodings is enough to recover every signed entry once both sides satisfy the
recorded bound.  These lemmas are shared by the Atlas 43 and S4 checkers.
-/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

def intEncoding (base : Nat) (values : List Int) : Int :=
  (Nat.ofDigits base (values.map Int.toNat) : Int)

def shiftedEncoding (base bound : Nat) (values : List Int) : Int :=
  intEncoding base (values.map fun value => value + bound)

def geometricEncoding (base count : Nat) : Int :=
  ∑ k ∈ Finset.range count, (base : Int) ^ k

lemma shifted_digit_nonneg {value : Int} {bound : Nat}
    (h : value.natAbs ≤ bound) : 0 ≤ value + bound := by
  have habs : |value| ≤ (bound : Int) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast h
  have hlo : -(bound : Int) ≤ value :=
    le_trans (neg_le_neg habs) (neg_abs_le value)
  omega

lemma shifted_digit_lt {value : Int} {bound : Nat}
    (h : value.natAbs ≤ bound) : (value + bound).toNat < 2 * bound + 1 := by
  have hlo := shifted_digit_nonneg h
  have hhi : value ≤ (bound : Int) := by
    have habs : |value| ≤ (bound : Int) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h
    exact le_trans (le_abs_self value) habs
  rw [Int.toNat_lt hlo]
  omega

theorem shiftedEncoding_injective_of_bound
    {n base bound : Nat} (hbound : 0 < bound)
    (hbase : base = 2 * bound + 1)
    (left right : Fin n → Int)
    (hleft : ∀ i, (left i).natAbs ≤ bound)
    (hright : ∀ i, (right i).natAbs ≤ bound)
    (hencoding : shiftedEncoding base bound (List.ofFn left) =
      shiftedEncoding base bound (List.ofFn right)) :
    left = right := by
  have hbase' : 1 < base := by
    rw [hbase]
    omega
  have hnat :
      Nat.ofDigits base ((List.ofFn left).map fun value : Int =>
        (value + (bound : Int)).toNat) =
        Nat.ofDigits base ((List.ofFn right).map fun value : Int =>
          (value + (bound : Int)).toNat) := by
    have hcast := hencoding
    simp only [shiftedEncoding, intEncoding, List.map_map] at hcast
    rw [← Nat.coe_ofDigits Int base, ← Nat.coe_ofDigits Int base] at hcast
    exact_mod_cast hcast
  have hlists := Nat.ofDigits_inj_of_len_eq hbase'
    (by simp)
    (by
      intro digit hdigit
      simp only [List.mem_map, List.mem_ofFn] at hdigit
      obtain ⟨value, ⟨i, rfl⟩, rfl⟩ := hdigit
      rw [hbase]
      exact shifted_digit_lt (hleft i))
    (by
      intro digit hdigit
      simp only [List.mem_map, List.mem_ofFn] at hdigit
      obtain ⟨value, ⟨i, rfl⟩, rfl⟩ := hdigit
      rw [hbase]
      exact shifted_digit_lt (hright i))
    hnat
  funext i
  let leftDigits := (List.ofFn left).map fun value : Int =>
    (value + (bound : Int)).toNat
  let rightDigits := (List.ofFn right).map fun value : Int =>
    (value + (bound : Int)).toNat
  have hdigit := congrArg (fun values : List Nat => values.getD i.1 0) hlists
  change leftDigits.getD i.1 0 = rightDigits.getD i.1 0 at hdigit
  rw [List.getD_eq_getElem leftDigits 0 (by simp [leftDigits]),
    List.getD_eq_getElem rightDigits 0 (by simp [rightDigits])] at hdigit
  simp only [leftDigits, rightDigits, List.getElem_map, List.getElem_ofFn] at hdigit
  have hleft_nonneg := shifted_digit_nonneg (hleft i)
  have hright_nonneg := shifted_digit_nonneg (hright i)
  have hcast := congrArg (fun value : Nat => (value : Int)) hdigit
  rw [Int.toNat_of_nonneg hleft_nonneg,
    Int.toNat_of_nonneg hright_nonneg] at hcast
  omega

theorem intEncoding_ofFn_eq_sum {n base : Nat} (values : Fin n → Int)
    (hvalues : ∀ i, 0 ≤ values i) :
    intEncoding base (List.ofFn values) =
      ∑ i : Fin n, values i * (base : Int) ^ i.1 := by
  unfold intEncoding
  rw [List.map_ofFn]
  rw [← Nat.coe_ofDigits Int base]
  rw [Nat.ofDigits_eq_sum_mapIdx]
  simp only [List.mapIdx_eq_ofFn, List.length_ofFn, List.get_ofFn,
    List.sum_ofFn, Function.comp_apply]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [Int.toNat_of_nonneg (hvalues _)]
  apply congrArg₂ (· * ·)
  · exact congrArg values (Fin.ext rfl)
  · rfl

theorem shiftedEncoding_ofFn_eq_sum {n base bound : Nat}
    (values : Fin n → Int) (hvalues : ∀ i, (values i).natAbs ≤ bound) :
    shiftedEncoding base bound (List.ofFn values) =
      ∑ i : Fin n, (values i + bound) * (base : Int) ^ i.1 := by
  unfold shiftedEncoding
  rw [List.map_ofFn]
  change intEncoding base (List.ofFn (fun i => values i + bound)) = _
  exact intEncoding_ofFn_eq_sum
    (fun i => values i + bound) (fun i => shifted_digit_nonneg (hvalues i))

theorem encoded_matrix_product {m n : Nat} (base bound : Nat)
    (diagonal : Fin n → Int) (left : Fin m → Int)
    (matrix : Fin m → Fin n → Int) :
    (∑ j : Fin n, (diagonal j + (∑ i : Fin m, left i * matrix i j) + bound) *
        (base : Int) ^ j.1) =
      bound * geometricEncoding base n +
        (∑ j : Fin n, diagonal j * (base : Int) ^ j.1) +
          ∑ i : Fin m, left i *
            (∑ j : Fin n, matrix i j * (base : Int) ^ j.1) := by
  rw [geometricEncoding, ← Fin.sum_univ_eq_sum_range]
  simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  ring_nf
  rw [show (∑ x : Fin n, diagonal x * (base : Int) ^ x.1) =
      ∑ x : Fin n, (base : Int) ^ x.1 * diagonal x by
    apply Finset.sum_congr rfl
    intro x _
    ring]
  abel

theorem natAbs_sum_le_card_mul_bound {ι : Type*} [Fintype ι]
    (values : ι → Int) (bound : Nat)
    (hvalues : ∀ i, (values i).natAbs ≤ bound) :
    (∑ i, values i).natAbs ≤ Fintype.card ι * bound := by
  calc
    (∑ i, values i).natAbs ≤ ∑ i, (values i).natAbs := by
      simpa using Int.natAbs_sum_le (Finset.univ : Finset ι) values
    _ ≤ ∑ _i : ι, bound := Finset.sum_le_sum fun i _ => hvalues i
    _ = Fintype.card ι * bound := by simp

theorem matrix_product_entry_bound {m : Nat}
    (denominator leftBound matrixBound : Nat)
    (diagonal : Int) (left : Fin m → Int) (matrix : Fin m → Int)
    (hdiagonal : diagonal.natAbs ≤ leftBound)
    (hleft : ∀ i, (left i).natAbs ≤ leftBound)
    (hmatrix : ∀ i, (matrix i).natAbs ≤ matrixBound) :
    (diagonal * denominator + ∑ i, left i * matrix i).natAbs ≤
      denominator * leftBound + m * leftBound * matrixBound := by
  calc
    (diagonal * denominator + ∑ i, left i * matrix i).natAbs ≤
        (diagonal * denominator).natAbs + (∑ i, left i * matrix i).natAbs :=
      Int.natAbs_add_le _ _
    _ ≤ leftBound * denominator + m * (leftBound * matrixBound) := by
      apply Nat.add_le_add
      · simpa [Int.natAbs_mul, Nat.mul_comm] using
          Nat.mul_le_mul_right denominator hdiagonal
      · simpa using natAbs_sum_le_card_mul_bound
          (fun i => left i * matrix i) (leftBound * matrixBound)
          (fun i => by
            rw [Int.natAbs_mul]
            exact Nat.mul_le_mul (hleft i) (hmatrix i))
    _ = denominator * leftBound + m * leftBound * matrixBound := by ring

end Taeyoung.Methods.RootedSOS
