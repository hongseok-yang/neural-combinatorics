import Taeyoung.Methods.RootedSOS.PackedCoefficients
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! A checked equivalence between sparse row and column listings permits
matrix contractions to visit only the nonzero entries. -/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

theorem sparse_contraction
    {m n : Nat} (rowSize : Fin m → Nat) (columnSize : Fin n → Nat)
    (rowColumn : (Σ i, Fin (rowSize i)) → Fin n)
    (rowValue : (Σ i, Fin (rowSize i)) → Int)
    (e : (Σ j, Fin (columnSize j)) ≃ (Σ i, Fin (rowSize i)))
    (hcolumn : ∀ x, rowColumn (e x) = x.1)
    (v : Fin n → Int) (row : Fin m) :
    (∑ j : Fin n,
      (∑ k : Fin (columnSize j),
        if (e ⟨j,k⟩).1 = row then rowValue (e ⟨j,k⟩) else 0) * v j) =
      ∑ k : Fin (rowSize row), rowValue ⟨row,k⟩ * v (rowColumn ⟨row,k⟩) := by
  let f : (Σ i, Fin (rowSize i)) → Int := fun x =>
    if x.1 = row then rowValue x * v (rowColumn x) else 0
  calc
    _ = ∑ x : (Σ j, Fin (columnSize j)), f (e x) := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [f]
      rw [hcolumn]
      split <;> simp_all
    _ = ∑ x : (Σ i, Fin (rowSize i)), f x := e.sum_comp f
    _ = _ := by
      rw [Fintype.sum_sigma]
      rw [Finset.sum_eq_single row]
      · simp [f]
      · intro i _ hi
        simp [f, hi]
      · simp

def listedCoefficient {E : Type*} [Fintype E] {g : Nat}
    (group : E → Fin g) (value : E → Int) (index : Fin g) : Int :=
  ∑ e, if group e = index then value e else 0

theorem listedCoefficient_bound {E : Type*} [Fintype E] {g bound : Nat}
    (group : E → Fin g) (value : E → Int)
    (hbound : (∑ e, (value e).natAbs : Nat) ≤ bound) (index : Fin g) :
    (listedCoefficient group value index).natAbs ≤ bound := by
  apply (Int.natAbs_sum_le _ _).trans
  apply le_trans _ hbound
  apply Finset.sum_le_sum
  intro e _
  split <;> simp

theorem listedCoefficient_of_encoding {E : Type*} [Fintype E]
    {g base bound code : Nat} (group : E → Fin g) (value : E → Int)
    (hbase : base = 2 * bound + 1)
    (hbound : (∑ e, (value e).natAbs : Nat) ≤ bound)
    (hcode : (code : Int) = bound * geometricEncoding base g +
      ∑ e, value e * (base : Int)^(group e).1) (index : Fin g) :
    decodeSignedDigit base bound code index = listedCoefficient group value index := by
  have h := groupedCoefficient_of_encoding (fun e (_ : Unit) => group e)
    value (fun _ : Unit => (1 : Int)) hbase
    (by
      intro i
      simpa only [groupedCoefficient, listedCoefficient, Fintype.sum_unique, mul_one] using
        listedCoefficient_bound group value hbound i)
    (by simpa only [Fintype.sum_unique, mul_one] using hcode) index
  simpa only [groupedCoefficient, listedCoefficient, Fintype.sum_unique, mul_one] using h

end Taeyoung.Methods.RootedSOS
