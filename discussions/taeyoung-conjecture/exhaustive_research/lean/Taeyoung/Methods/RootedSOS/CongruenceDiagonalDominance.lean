import Taeyoung.Methods.RootedSOS.DiagonalDominance
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Positivity after an integer triangular change of variables

An exact rational Gram matrix need not itself be diagonally dominant.
A supplied nonsingular upper triangular matrix may make it so by congruence.
This avoids storing a large rational inverse or a fraction-free LDL witness.
-/

open Finset
open scoped BigOperators Matrix

namespace Taeyoung.Methods.RootedSOS

variable {n : Nat}

def matrixQuadratic (A : Matrix (Fin n) (Fin n) Real) (x : Fin n → Real) : Real :=
  ∑ i, ∑ j, x i * A i j * x j

theorem matrixQuadratic_nonneg_of_diagonallyDominant
    (A : Matrix (Fin n) (Fin n) Real)
    (hsymm : ∀ i j, A i j = A j i)
    (hrow : ∀ i, (∑ j, if i = j then 0 else |A i j|) ≤ A i i)
    (x : Fin n → Real) : 0 ≤ matrixQuadratic A x := by
  let C : Fin n → Fin n → Real := fun i j => A i j - if i = j then 1 else 0
  have hc : ∀ i j, C i j = C j i := by
    intro i j
    simp only [C, hsymm i j, eq_comm]
  have hr : ∀ i,
      (∑ j, |if i = j then (0 : Real) else C i j|) ≤ 1 + C i i := by
    intro i
    have he : (∑ j, |if i = j then (0 : Real) else C i j|) =
        ∑ j, if i = j then 0 else |A i j| := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i = j <;> simp [C, h]
    rw [he]
    simpa [C] using hrow i
  have hn := identity_add_correction_diagonallyDominant_nonneg C hc (by
    intro i
    exact hr i) x
  have heq : (∑ i, x i ^ 2) + ∑ i, ∑ j, x i * C i j * x j =
      matrixQuadratic A x := by
    simp only [C, mul_sub, sub_mul, Finset.sum_sub_distrib]
    have hdiag : (∑ i, ∑ j, x i * (if i = j then (1 : Real) else 0) * x j) =
        ∑ i, x i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      simp [mul_ite, ite_mul, sq]
    rw [hdiag]
    dsimp [matrixQuadratic]
    ring
  rwa [heq] at hn

theorem matrixQuadratic_congruence
    (A P : Matrix (Fin n) (Fin n) Real) (x : Fin n → Real) :
    matrixQuadratic (P.transpose * A * P) x =
      matrixQuadratic A (P.mulVec x) := by
  have heq (M : Matrix (Fin n) (Fin n) Real) (y : Fin n → Real) :
      matrixQuadratic M y = dotProduct y (M.mulVec y) := by
    simp only [matrixQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [heq, heq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem matrixQuadratic_nonneg_of_triangular_congruence
    (A P B : Matrix (Fin n) (Fin n) Real)
    (hupper : ∀ i j, j < i → P i j = 0)
    (hdiag : ∀ i, P i i ≠ 0)
    (hproduct : P.transpose * A * P = B)
    (hsymm : ∀ i j, B i j = B j i)
    (hrow : ∀ i, (∑ j, if i = j then 0 else |B i j|) ≤ B i i)
    (x : Fin n → Real) : 0 ≤ matrixQuadratic A x := by
  have hu : P.BlockTriangular id := fun i j h => hupper i j h
  have hdet : P.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular hu]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i
  have hunit : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨y, hy⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hunit) x
  rw [← hy, ← matrixQuadratic_congruence, hproduct]
  exact matrixQuadratic_nonneg_of_diagonallyDominant B hsymm hrow y

theorem matrixQuadratic_nonneg_of_integer_congruence
    (A P K B : Fin n → Fin n → Int)
    (hupper : ∀ i j, j < i → P i j = 0)
    (hdiag : ∀ i, P i i ≠ 0)
    (hK : ∀ i j, K i j = ∑ k, A i k * P k j)
    (hB : ∀ i j, B i j = ∑ k, P k i * K k j)
    (hsymm : ∀ i j, B i j = B j i)
    (hrow : ∀ i, (∑ j, if i = j then 0 else (B i j).natAbs : Nat) ≤ (B i i).toNat)
    (hdiagB : ∀ i, 0 ≤ B i i)
    (x : Fin n → Real) :
    0 ≤ matrixQuadratic (fun i j => (A i j : Real)) x := by
  apply matrixQuadratic_nonneg_of_triangular_congruence
    (P := fun i j => (P i j : Real)) (B := fun i j => (B i j : Real))
  · intro i j h
    exact_mod_cast hupper i j h
  · intro i
    exact_mod_cast hdiag i
  · rw [Matrix.mul_assoc]
    ext i j
    have hcast (i j) : (K i j : Real) = ∑ k, (A i k : Real) * (P k j : Real) := by
      exact_mod_cast hK i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    simp_rw [← hcast]
    exact_mod_cast (hB i j).symm
  · intro i j
    exact_mod_cast hsymm i j
  · intro i
    have hn : ((∑ j, if i = j then 0 else (B i j).natAbs : Nat) : Int) ≤ B i i := by
      simpa only [Int.toNat_of_nonneg (hdiagB i)] using (Int.ofNat_le.mpr (hrow i))
    have hr : ((∑ j, if i = j then 0 else (B i j).natAbs : Nat) : Real) ≤ (B i i : Real) := by
      simpa only [Int.cast_natCast] using (Int.cast_le (R := Real)).mpr hn
    convert hr using 1
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i = j <;> simp [h]

end Taeyoung.Methods.RootedSOS
