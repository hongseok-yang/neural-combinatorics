import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance
import Mathlib.Algebra.BigOperators.Fin

/-! Positive matrices after rectangular pullback and interval interpolation. -/

open Finset Matrix
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS.Induced

theorem matrixQuadratic_rectangular {m n : Nat}
    (G : Matrix (Fin n) (Fin n) Real) (P : Matrix (Fin n) (Fin m) Real)
    (x : Fin m → Real) :
    matrixQuadratic (P.transpose * G * P) x = matrixQuadratic G (P.mulVec x) := by
  have heq {d : Nat} (M : Matrix (Fin d) (Fin d) Real) (y : Fin d → Real) :
      matrixQuadratic M y = dotProduct y (M.mulVec y) := by
    simp only [matrixQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [heq, heq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem rectangular_pullback_nonneg {m n : Nat}
    (G : Matrix (Fin n) (Fin n) Real) (N : Matrix (Fin m) (Fin n) Real)
    (H : Matrix (Fin m) (Fin m) Real)
    (hG : ∀ x, 0 ≤ matrixQuadratic G x)
    (hH : ∀ a b, H a b = ∑ j, (∑ i, N a i * G i j) * N b j)
    (x : Fin m → Real) : 0 ≤ matrixQuadratic H x := by
  have he : H = (Matrix.transpose (Matrix.transpose N) * G * Matrix.transpose N) := by
    ext a b
    simpa only [Matrix.mul_apply, Matrix.transpose_apply] using hH a b
  rw [he, matrixQuadratic_rectangular]
  exact hG _

theorem integer_rectangular_pullback_nonneg {m n : Nat}
    (G : Fin n → Fin n → Int) (N : Fin m → Fin n → Int)
    (H : Fin m → Fin m → Int)
    (hG : ∀ x, 0 ≤ matrixQuadratic (fun i j => (G i j : Real)) x)
    (hH : ∀ a b, H a b = ∑ j, (∑ i, N a i * G i j) * N b j)
    (x : Fin m → Real) : 0 ≤ matrixQuadratic (fun a b => (H a b : Real)) x := by
  apply rectangular_pullback_nonneg (fun i j => (G i j : Real))
    (fun a i => (N a i : Real)) _ hG
  intro a b
  exact_mod_cast hH a b

def intervalMatrix {n : Nat} (A : Fin (n+n) → Fin (n+n) → Real)
    (B : Fin n → Fin n → Real) (s : Real) (i j : Fin n) : Real :=
  A (Fin.castAdd n i) (Fin.castAdd n j) * (1-s)^2 +
    (A (Fin.castAdd n i) (Fin.natAdd n j) +
      A (Fin.natAdd n i) (Fin.castAdd n j) + B i j) * s*(1-s) +
    A (Fin.natAdd n i) (Fin.natAdd n j) * s^2

theorem intervalMatrix_quadratic {n : Nat}
    (A : Fin (n+n) → Fin (n+n) → Real) (B : Fin n → Fin n → Real)
    (s : Real) (x : Fin n → Real) :
    matrixQuadratic (intervalMatrix A B s) x =
      matrixQuadratic A (Fin.append (fun i => (1-s)*x i) (fun i => s*x i)) +
        s*(1-s)*matrixQuadratic B x := by
  simp only [matrixQuadratic, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    Finset.sum_add_distrib, Finset.mul_sum]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold intervalMatrix
  ring

theorem intervalMatrix_nonneg {n : Nat}
    (A : Fin (n+n) → Fin (n+n) → Real) (B : Fin n → Fin n → Real)
    (hA : ∀ x, 0 ≤ matrixQuadratic A x) (hB : ∀ x, 0 ≤ matrixQuadratic B x)
    {s : Real} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : Fin n → Real) :
    0 ≤ matrixQuadratic (intervalMatrix A B s) x := by
  rw [intervalMatrix_quadratic]
  exact add_nonneg (hA _) (mul_nonneg (mul_nonneg hs0 (sub_nonneg.mpr hs1)) (hB _))

/-- Substitute three coefficient identities before instantiating concrete data.
Keeping the simplification generic avoids reducing large packed tables while
matching finite-index expressions in a certificate. -/
theorem intervalMatrix_entry_of_coefficients {n : Nat}
    (A B : Nat → Nat → Int) (r : Fin 3 → Int) (i j : Fin n)
    (h : ∀ u : Fin 3, r u =
      if u.1 = 0 then A i.1 j.1
      else if u.1 = 1 then A i.1 (n+j.1)+A (n+i.1) j.1+B i.1 j.1
      else A (n+i.1) (n+j.1)) (s : Real) :
    (r 0 : Real)*(1-s)^2+(r 1 : Real)*s*(1-s)+(r 2 : Real)*s^2 =
      intervalMatrix (fun a b : Fin (n+n) => (A a.1 b.1 : Real))
        (fun a b : Fin n => (B a.1 b.1 : Real)) s i j := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num at h0 h1 h2
  rw [h0, h1, h2]
  simp only [intervalMatrix, Int.cast_add, Fin.val_castAdd, Fin.val_natAdd]

end Taeyoung.Methods.RootedSOS.Induced
