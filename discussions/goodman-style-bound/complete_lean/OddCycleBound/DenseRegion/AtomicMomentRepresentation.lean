/-
# High-density theorem — finite spectral moment representation

This file proves E2 for an arbitrary finite-dimensional real symmetric operator.  The later P bridge
only has to construct the finite Krylov compression and identify its vector moments with
`specMoment`; diagonalizing that compression and converting the moments to finite atomic data is
handled here.
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import OddCycleBound.DenseRegion.Expansion

open scoped BigOperators InnerProductSpace

namespace OddCycleBound.DenseRegion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Iteration of a linear endomorphism, kept explicit to match graphon compression iterates. -/
def linearIter (T : E →ₗ[ℝ] E) : ℕ → E → E
  | 0 => id
  | j + 1 => fun x => T (linearIter T j x)

@[simp] lemma linearIter_zero (T : E →ₗ[ℝ] E) (x : E) : linearIter T 0 x = x := rfl

lemma linearIter_succ (T : E →ₗ[ℝ] E) (j : ℕ) (x : E) :
    linearIter T (j + 1) x = T (linearIter T j x) := rfl

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- Eigenvalues of the canonical orthonormal eigenbasis of a finite-dimensional symmetric map. -/
noncomputable def finiteAtomEigenvalue (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) :
    Fin (Module.finrank ℝ E) → ℝ := hT.eigenvalues rfl

/-- Spectral weights of `g`: squares of its coordinates in the canonical eigenbasis. -/
noncomputable def finiteAtomWeight (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (g : E) :
    Fin (Module.finrank ℝ E) → ℝ := fun i =>
  inner ℝ g (hT.eigenvectorBasis rfl i) ^ 2

lemma finiteAtomWeight_nonneg (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (g : E) (i) :
    0 ≤ finiteAtomWeight T hT g i := sq_nonneg _

/-- Coordinates of an iterated vector in the symmetric eigenbasis. -/
lemma inner_eigenvector_linearIter (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (g : E) (j : ℕ) (i : Fin (Module.finrank ℝ E)) :
    inner ℝ (hT.eigenvectorBasis rfl i) (linearIter T j g) =
      finiteAtomEigenvalue T hT i ^ j * inner ℝ (hT.eigenvectorBasis rfl i) g := by
  induction j with
  | zero => simp [finiteAtomEigenvalue]
  | succ j ih =>
      have heigen : T (hT.eigenvectorBasis rfl i) =
          finiteAtomEigenvalue T hT i • hT.eigenvectorBasis rfl i := by
        simpa [finiteAtomEigenvalue] using hT.apply_eigenvectorBasis rfl i
      rw [linearIter_succ, ← hT (hT.eigenvectorBasis rfl i) (linearIter T j g),
        heigen, real_inner_smul_left, ih]
      ring

/-- **E2, finite-dimensional form.**  Every vector moment of a symmetric finite-dimensional
operator is the atomic moment of its eigenvalues with nonnegative squared-coordinate weights. -/
theorem inner_linearIter_eq_atomicMoment (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (g : E) (j : ℕ) :
    inner ℝ g (linearIter T j g) =
      atomicMoment (finiteAtomWeight T hT g) (finiteAtomEigenvalue T hT) j := by
  let b := hT.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  rw [← b.sum_inner_mul_inner g (linearIter T j g)]
  unfold atomicMoment finiteAtomWeight
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_eigenvector_linearIter T hT g j i]
  rw [real_inner_comm (hT.eigenvectorBasis rfl i) g]
  ring

end FiniteDimensional

end OddCycleBound.DenseRegion
