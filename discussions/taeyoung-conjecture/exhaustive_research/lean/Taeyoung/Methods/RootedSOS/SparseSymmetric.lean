import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # Sparse symmetric matrices

This elementary representation is used by exact certificates whose dense
matrix has only a small number of exceptional upper-triangle entries.
-/

namespace Taeyoung.Methods.RootedSOS

open Finset
open scoped BigOperators

private lemma sum_two_points {R Vertex : Type*} [AddCommMonoid R]
    [Fintype Vertex] [DecidableEq Vertex]
    (left right : Vertex) (hne : left ≠ right) (f g : Vertex → R) :
    (∑ x : Vertex, if x = left then f x else if x = right then g x else 0) =
      f left + g right := by
  rw [show (∑ x : Vertex,
      if x = left then f x else if x = right then g x else 0) =
      (∑ x : Vertex, if x = left then f x else 0) +
        ∑ x : Vertex, if x = right then g x else 0 by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hleft : x = left <;> by_cases hright : x = right <;>
      simp_all]
  simp

def sparseSymmetricMatrix {R Index Vertex : Type*} [CommRing R] [Fintype Index]
    [DecidableEq Index] [DecidableEq Vertex]
    (left right : Index → Vertex) (value : Index → R) (i j : Vertex) : R :=
  ∑ entry : Index,
    if i = left entry then
      if j = right entry then value entry else 0
    else if left entry ≠ right entry then
      if i = right entry then
        if j = left entry then value entry else 0
      else 0
    else 0

def sparseSymmetricBilinear {R Index Vertex : Type*} [CommRing R] [Fintype Index]
    [DecidableEq Index] [DecidableEq Vertex]
    (left right : Index → Vertex) (value : Index → R)
    (term : Vertex → Vertex → R) : R :=
  ∑ entry : Index, value entry *
    (term (left entry) (right entry) +
      if left entry = right entry then 0
      else term (right entry) (left entry))

theorem sparseSymmetricMatrix_bilinear
    {R Index Vertex : Type*} [CommRing R] [Fintype Index] [Fintype Vertex]
    [DecidableEq Index] [DecidableEq Vertex]
    (left right : Index → Vertex) (value : Index → R)
    (term : Vertex → Vertex → R) :
    (∑ i : Vertex, ∑ j : Vertex,
      sparseSymmetricMatrix left right value i j * term i j) =
      sparseSymmetricBilinear left right value term := by
  classical
  unfold sparseSymmetricMatrix sparseSymmetricBilinear
  simp_rw [Finset.sum_mul]
  simp only [ite_mul, zero_mul]
  let f := fun (i j : Vertex) (entry : Index) ↦
    if i = left entry then
      if j = right entry then value entry * term i j else 0
    else if left entry ≠ right entry then
      if i = right entry then
        if j = left entry then value entry * term i j else 0
      else 0
    else 0
  change (∑ i : Vertex, ∑ j : Vertex, ∑ entry : Index, f i j entry) = _
  calc
    _ = ∑ i : Vertex, ∑ entry : Index, ∑ j : Vertex, f i j entry := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ entry : Index, ∑ i : Vertex, ∑ j : Vertex, f i j entry :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro entry _
      dsimp [f]
      by_cases h : left entry = right entry
      · simp [h]
      · simp [h]
        rw [sum_two_points (left entry) (right entry) h]
        exact (mul_add _ _ _).symm

end Taeyoung.Methods.RootedSOS
