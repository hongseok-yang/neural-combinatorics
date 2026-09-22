import Taeyoung.Methods.RootedSOS.EncodedGram

/-! Balanced integer data and reusable positional matrix-product checks. -/

namespace Taeyoung.Methods.RootedSOS

inductive PackedTable where
  | leaf (value : Int)
  | node (leftSize : Nat) (left right : PackedTable)

def PackedTable.get : PackedTable → Nat → Int
  | .leaf value, _ => value
  | .node size left right, i =>
      if i < size then left.get i else right.get (i - size)

theorem packed_matrix_product_exact {m n : Nat}
    (left right result : Nat → Nat → Int)
    (leftBound rightBound resultBound base : Nat)
    (encodedRight : Fin n → Int)
    (hleft : ∀ (i : Fin m) (j : Fin n), (left i j).natAbs ≤ leftBound)
    (hright : ∀ (i j : Fin n), (right i j).natAbs ≤ rightBound)
    (hresult : ∀ (i : Fin m) (j : Fin n), (result i j).natAbs ≤ resultBound)
    (hpositive : 0 < resultBound)
    (hbase : base = 2 * resultBound + 1)
    (hbound : resultBound = n * leftBound * rightBound)
    (hencoded : ∀ i, encodedRight i = ∑ j : Fin n, right i j * (base : Int) ^ j.1)
    (hproduct : ∀ i : Fin m,
      shiftedEncoding base resultBound (List.ofFn fun j : Fin n => result i j) =
        resultBound * geometricEncoding base n + ∑ j : Fin n, left i j * encodedRight j)
    (i : Fin m) (j : Fin n) :
    result i j = ∑ k : Fin n, left i k * right k j := by
  have h := intermediate_entries_exact 0 leftBound rightBound resultBound base
    (fun i : Fin m => fun j : Fin n => left i j)
    (fun i j : Fin n => right i j)
    (fun i : Fin m => fun j : Fin n => result i j) encodedRight
    hpositive hbase (by simpa using hbound) hleft hright hresult hencoded
    (by simpa only [Nat.cast_zero, zero_mul, add_zero] using hproduct) i j
  simpa only [expectedIntermediate, Nat.cast_zero, mul_zero, zero_add] using h

theorem packed_rect_product_exact {m n p : Nat}
    (left right result : Nat → Nat → Int)
    (leftBound rightBound resultBound base : Nat)
    (encodedRight : Fin n → Int)
    (hleft : ∀ (i : Fin m) (j : Fin n), (left i j).natAbs ≤ leftBound)
    (hright : ∀ (i : Fin n) (j : Fin p), (right i j).natAbs ≤ rightBound)
    (hresult : ∀ (i : Fin m) (j : Fin p), (result i j).natAbs ≤ resultBound)
    (hpositive : 0 < resultBound)
    (hbase : base = 2 * resultBound + 1)
    (hbound : resultBound = n * leftBound * rightBound)
    (hencoded : ∀ i, encodedRight i = ∑ j : Fin p, right i j * (base : Int) ^ j.1)
    (hproduct : ∀ i : Fin m,
      shiftedEncoding base resultBound (List.ofFn fun j : Fin p => result i j) =
        resultBound * geometricEncoding base p + ∑ j : Fin n, left i j * encodedRight j)
    (i : Fin m) (j : Fin p) :
    result i j = ∑ k : Fin n, left i k * right k j := by
  have heBound (j : Fin p) :
      (∑ k : Fin n, left i k * right k j).natAbs ≤ resultBound := by
    rw [hbound, Nat.mul_assoc]
    simpa only [Fintype.card_fin] using natAbs_sum_le_card_mul_bound
      (fun k : Fin n => left i k * right k j) (leftBound * rightBound)
      (fun k => by
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul (hleft i k) (hright k j))
  have he : shiftedEncoding base resultBound (List.ofFn fun j : Fin p => result i j) =
      shiftedEncoding base resultBound
        (List.ofFn fun j : Fin p => ∑ k : Fin n, left i k * right k j) := by
    rw [shiftedEncoding_ofFn_eq_sum _ heBound]
    have hp := encoded_matrix_product base resultBound
      (fun _ : Fin p => (0 : Int)) (fun k : Fin n => left i k)
      (fun k : Fin n => fun j : Fin p => right k j)
    simp only [zero_add, zero_mul, Finset.sum_const_zero, add_zero] at hp
    rw [hp]
    simp_rw [← hencoded]
    exact hproduct i
  exact congrFun (shiftedEncoding_injective_of_bound hpositive hbase
    (fun j : Fin p => result i j) (fun j : Fin p => ∑ k : Fin n, left i k * right k j)
    (hresult i) heBound he) j

end Taeyoung.Methods.RootedSOS
