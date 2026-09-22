import Taeyoung.Methods.RootedSOS.PackedCoefficients
import Taeyoung.Methods.RootedSOS.FlagGram

/-! Semantic interpretation of the compact sparse Young coefficient checks.
Sparse lists define the actual linear forms; no representation-theoretic
completeness assertion is needed to interpret their sum of squares. -/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

def sparseVector {A L : Type*} [DecidableEq A] [Fintype L]
    (index : L → A) (weight : L → Int) (a : A) : Int :=
  ∑ k, if index k = a then weight k else 0

theorem sparseVector_eval {A L : Type*} [Fintype A] [DecidableEq A] [Fintype L]
    (index : L → A) (weight : L → Int) (f : A → Real) :
    (∑ a, (sparseVector index weight a : Real) * f a) =
      ∑ k, (weight k : Real) * f (index k) := by
  simp only [sparseVector, Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp [ite_mul]

theorem sparseVector_pair_eval
    {A L R : Type*} [Fintype A] [DecidableEq A] [Fintype L] [Fintype R]
    (leftIndex : L → A) (rightIndex : R → A)
    (left : L → Int) (right : R → Int) (f : A → A → Real) :
    (∑ a, ∑ b, (sparseVector leftIndex left a : Real) *
      (sparseVector rightIndex right b : Real) * f a b) =
      ∑ i, ∑ j, (left i : Real) * (right j : Real) * f (leftIndex i) (rightIndex j) := by
  calc
    _ = ∑ a, (sparseVector leftIndex left a : Real) *
        ∑ b, (sparseVector rightIndex right b : Real) * f a b := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ a, (sparseVector leftIndex left a : Real) *
        ∑ j, (right j : Real) * f a (rightIndex j) := by
      simp_rw [sparseVector_eval]
    _ = _ := by
      rw [sparseVector_eval]
      simp only [Finset.mul_sum, mul_assoc]

theorem groupedCoefficient_eval
    {L R : Type*} [Fintype L] [Fintype R] {g : Nat}
    (group : L → R → Fin g) (left : L → Int) (right : R → Int)
    (f : Fin g → Real) :
    (∑ k, (groupedCoefficient group left right k : Real) * f k) =
      ∑ a, ∑ b, (left a : Real) * (right b : Real) * f (group a b) := by
  simp only [groupedCoefficient, Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp [ite_mul]

theorem sparseVector_pair_grouped
    {A L R : Type*} [Fintype A] [DecidableEq A] [Fintype L] [Fintype R]
    {g : Nat} (group : A → A → Fin g)
    (leftIndex : L → A) (rightIndex : R → A)
    (left : L → Int) (right : R → Int) (f : Fin g → Real) :
    (∑ a, ∑ b, (sparseVector leftIndex left a : Real) *
      (sparseVector rightIndex right b : Real) * f (group a b)) =
      ∑ k, (groupedCoefficient (fun i j => group (leftIndex i) (rightIndex j))
        left right k : Real) * f k := by
  rw [sparseVector_pair_eval, groupedCoefficient_eval]

end Taeyoung.Methods.RootedSOS
