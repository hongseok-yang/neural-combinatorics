-- Provenance (plan D7): copied from
--   discussions/schur_decomposition/cycle_commonality/lean/CycleCommonality/Model/StepModel.lean
--   at neural-combinatorics commit e2d96440.
-- Changes: import paths and the namespace prefix CycleCommonality -> EvenCycleApex; pruned in M11
-- to the two matrix lemmas used by `Host/Spectral.lean` (the step-graphon model itself and its
-- imports `Spectral/RankOneTrace`, `Spectral/Interlace`, `Majorization/*` are not used here).
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Matrix operators on Euclidean space

The two facts from the step-graphon model of `cycle_commonality` that this project uses: the matrix
of `Matrix.toEuclideanLin M` (and of its powers) in the standard basis is `M` (resp. `M ^ r`).
-/

namespace EvenCycleApex

namespace StepGraphon

variable {N : ℕ}

/-- The trace of a matrix operator is the matrix trace. -/
lemma toMatrix_toEuclideanLin (M : Matrix (Fin N) (Fin N) ℝ) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (Matrix.toEuclideanLin M) = M := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]

lemma toMatrix_pow (M : Matrix (Fin N) (Fin N) ℝ) (r : ℕ) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (Matrix.toEuclideanLin M ^ r) = M ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ, pow_succ, LinearMap.toMatrix_mul, ih, toMatrix_toEuclideanLin]

end StepGraphon

end EvenCycleApex
