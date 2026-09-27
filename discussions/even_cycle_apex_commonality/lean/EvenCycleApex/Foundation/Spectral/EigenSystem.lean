-- Provenance (plan D7): copied from
--   discussions/schur_decomposition/cycle_commonality/lean/CycleCommonality/Spectral/EigenSystem.lean
--   at neural-combinatorics commit e2d96440.
-- Changes: import paths and the namespace prefix CycleCommonality -> EvenCycleApex; pruned in M11
-- (declarations unused by this development removed, module docstring updated to match;
-- the removed `Spectral/Rayleigh.lean` contributed only its Mathlib imports).
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Eigensystems and traces of powers

An `EigenSystem N T` packages an orthonormal basis of eigenvectors of `T` together with the
corresponding eigenvalues, listed in nonincreasing order.  Mathlib's
`hT.eigenvectorBasis`/`hT.eigenvalues` provide one (`EigenSystem.ofSymmetric`).

Main results:

* `norm_sq_eq_sum`, `EigenSystem.inner_apply_eq_sum` — the norm and the quadratic form in
  eigencoordinates;
* `EigenSystem.trace_pow_eq_sum` — `Tr(Tⁿ) = ∑ λᵢⁿ`.
-/

namespace EvenCycleApex

open Finset Module
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

omit [FiniteDimensional ℝ E] in
/-- `‖v‖ ^ 2` is the sum of the squared coordinates of `v`. -/
lemma norm_sq_eq_sum (b : OrthonormalBasis (Fin N) ℝ E) (v : E) :
    ‖v‖ ^ 2 = ∑ i, (b.repr v i) ^ 2 := by
  rw [← b.sum_sq_norm_inner_right v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← b.repr_apply_apply, Real.norm_eq_abs, sq_abs]

omit [FiniteDimensional ℝ E] in
/-- The trace of an operator is the sum of its diagonal entries in any orthonormal basis. -/
lemma trace_eq_sum_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (T : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E T = ∑ i, ⟪b i, T (b i)⟫ := by
  rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis T]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]

/-- An orthonormal eigenbasis of `T` together with its eigenvalues in nonincreasing order. -/
structure EigenSystem (N : ℕ) (T : E →ₗ[ℝ] E) where
  /-- The orthonormal basis of eigenvectors. -/
  basis : OrthonormalBasis (Fin N) ℝ E
  /-- The eigenvalues, in nonincreasing order. -/
  val : Fin N → ℝ
  /-- `T` is symmetric. -/
  symm : T.IsSymmetric
  /-- The basis really is an eigenbasis. -/
  apply_basis : ∀ i, T (basis i) = val i • basis i
  /-- The eigenvalues are listed in nonincreasing order. -/
  antitone : Antitone val

namespace EigenSystem

variable {T : E →ₗ[ℝ] E}

/-- Mathlib's sorted spectral decomposition of a symmetric operator. -/
noncomputable def ofSymmetric (hT : T.IsSymmetric) (hn : finrank ℝ E = N) : EigenSystem N T where
  basis := hT.eigenvectorBasis hn
  val := hT.eigenvalues hn
  symm := hT
  apply_basis := fun i => by simp
  antitone := hT.eigenvalues_antitone hn

/-! ### Coordinates -/

omit [FiniteDimensional ℝ E] in
/-- In the eigenbasis, `T` acts diagonally. -/
lemma repr_apply (S : EigenSystem N T) (v : E) (i : Fin N) :
    S.basis.repr (T v) i = S.val i * S.basis.repr v i := by
  rw [S.basis.repr_apply_apply, ← S.symm (S.basis i) v, S.apply_basis i,
    real_inner_smul_left, S.basis.repr_apply_apply]

omit [FiniteDimensional ℝ E] in
/-- `⟪v, T v⟫` is the eigenvalue-weighted sum of the squared eigencoordinates of `v`. -/
lemma inner_apply_eq_sum (S : EigenSystem N T) (v : E) :
    ⟪v, T v⟫ = ∑ i, S.val i * (S.basis.repr v i) ^ 2 := by
  rw [← S.basis.sum_inner_mul_inner v (T v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ⟪v, S.basis i⟫ = S.basis.repr v i := by
    rw [S.basis.repr_apply_apply]; exact real_inner_comm _ _
  have h2 : ⟪S.basis i, T v⟫ = S.val i * S.basis.repr v i := by
    rw [← S.basis.repr_apply_apply, S.repr_apply v i]
  rw [h1, h2]
  ring

/-! ### Traces -/

omit [FiniteDimensional ℝ E] in
/-- `T` acts on the `i`-th eigenvector of `T ^ n` by `val i ^ n`. -/
lemma pow_apply_basis (S : EigenSystem N T) (n : ℕ) (i : Fin N) :
    (T ^ n) (S.basis i) = (S.val i) ^ n • S.basis i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, S.apply_basis i, smul_smul, pow_succ']
      ring_nf

omit [FiniteDimensional ℝ E] in
/-- The `n`-th powers of the eigenvalues sum to the trace of `T ^ n`. -/
lemma trace_pow_eq_sum (S : EigenSystem N T) (n : ℕ) :
    LinearMap.trace ℝ E (T ^ n) = ∑ i, (S.val i) ^ n := by
  rw [trace_eq_sum_inner S.basis (T ^ n)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [S.pow_apply_basis n i, real_inner_smul_right, real_inner_self_eq_norm_sq]
  simp

end EigenSystem


end EvenCycleApex
