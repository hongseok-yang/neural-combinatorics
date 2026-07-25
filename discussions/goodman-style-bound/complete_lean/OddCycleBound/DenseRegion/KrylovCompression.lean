/-
# High-density theorem — finite Krylov compression

This is the abstract finite-dimensional core of P.  For a bounded operator `T`, a vector `g`, and
a cutoff `d`, the span of `g,Tg,...,T^d g` is finite-dimensional.  Compressing `T` orthogonally to
that space preserves symmetry and cannot increase the operator norm.
-/

import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import OddCycleBound.DenseRegion.AtomicMomentRepresentation
import OddCycleBound.DenseRegion.AtomicSpectral

open scoped InnerProductSpace

namespace OddCycleBound.DenseRegion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The finite Krylov space `span {g,Tg,...,T^d g}`. -/
noncomputable def krylovSubspace (T : E →L[ℝ] E) (g : E) (d : ℕ) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range fun j : Fin (d + 1) => linearIter T.toLinearMap j g)

noncomputable instance krylovSubspace_finiteDimensional (T : E →L[ℝ] E) (g : E) (d : ℕ) :
    FiniteDimensional ℝ (krylovSubspace T g d) := by
  unfold krylovSubspace
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- The starting vector, regarded as an element of its Krylov space. -/
noncomputable def krylovVector (T : E →L[ℝ] E) (g : E) (d : ℕ) : krylovSubspace T g d :=
  ⟨g, Submodule.subset_span ⟨⟨0, Nat.succ_pos d⟩, by simp⟩⟩

@[simp] lemma krylovVector_coe (T : E →L[ℝ] E) (g : E) (d : ℕ) :
    (krylovVector T g d : E) = g := rfl

/-- Orthogonal compression of `T` to its finite Krylov space. -/
noncomputable def krylovCompression (T : E →L[ℝ] E) (g : E) (d : ℕ) :
    krylovSubspace T g d →L[ℝ] krylovSubspace T g d :=
  (krylovSubspace T g d).orthogonalProjectionOnto.comp
    (T.comp (krylovSubspace T g d).subtypeL)

/-- Orthogonal Krylov compression preserves self-adjointness. -/
theorem krylovCompression_isSymmetric (T : E →L[ℝ] E) (g : E) (d : ℕ)
    (hT : T.toLinearMap.IsSymmetric) :
    (krylovCompression T g d).toLinearMap.IsSymmetric := by
  intro x y
  unfold krylovCompression
  change inner ℝ ((krylovSubspace T g d).orthogonalProjectionOnto (T (x : E))) y =
    inner ℝ x ((krylovSubspace T g d).orthogonalProjectionOnto (T (y : E)))
  rw [(krylovSubspace T g d).inner_orthogonalProjectionOnto_eq_of_mem_right,
    (krylovSubspace T g d).inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact hT x y

/-- Orthogonal Krylov compression cannot increase the operator norm. -/
theorem norm_krylovCompression_le (T : E →L[ℝ] E) (g : E) (d : ℕ) :
    ‖krylovCompression T g d‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun x => ?_
  unfold krylovCompression
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  exact ((krylovSubspace T g d).norm_orthogonalProjectionOnto_apply_le (T (x : E))).trans
    (T.le_opNorm (x : E))

/-- Every iterate up to the cutoff belongs to the Krylov space. -/
lemma linearIter_mem_krylovSubspace (T : E →L[ℝ] E) (g : E) {d j : ℕ} (hj : j ≤ d) :
    linearIter T.toLinearMap j g ∈ krylovSubspace T g d := by
  apply Submodule.subset_span
  exact ⟨⟨j, by omega⟩, rfl⟩

/-- The `j`-th original iterate as an element of the cutoff Krylov space. -/
noncomputable def krylovIterVector (T : E →L[ℝ] E) (g : E) {d j : ℕ} (hj : j ≤ d) :
    krylovSubspace T g d :=
  ⟨linearIter T.toLinearMap j g, linearIter_mem_krylovSubspace T g hj⟩

@[simp] lemma krylovIterVector_coe (T : E →L[ℝ] E) (g : E) {d j : ℕ} (hj : j ≤ d) :
    (krylovIterVector T g hj : E) = linearIter T.toLinearMap j g := rfl

/-- Up to the cutoff, iterating the orthogonal compression on `g` exactly reproduces the original
iterates. -/
theorem linearIter_krylovCompression (T : E →L[ℝ] E) (g : E) {d j : ℕ} (hj : j ≤ d) :
    linearIter (krylovCompression T g d).toLinearMap j (krylovVector T g d) =
      krylovIterVector T g hj := by
  induction j with
  | zero =>
      apply Subtype.ext
      rfl
  | succ j ih =>
      have hjd : j ≤ d := by omega
      rw [linearIter_succ, ih hjd]
      unfold krylovCompression
      change (krylovSubspace T g d).orthogonalProjectionOnto
          (T (linearIter T.toLinearMap j g)) = krylovIterVector T g hj
      change (krylovSubspace T g d).orthogonalProjectionOnto
          (krylovIterVector T g hj : E) = krylovIterVector T g hj
      exact (krylovSubspace T g d).orthogonalProjectionOnto_mem_subspace_eq_self
        (krylovIterVector T g hj)

/-- The compressed and original vector moments agree through the Krylov cutoff. -/
theorem inner_linearIter_krylovCompression_eq (T : E →L[ℝ] E) (g : E)
    {d j : ℕ} (hj : j ≤ d) :
    inner ℝ (krylovVector T g d)
        (linearIter (krylovCompression T g d).toLinearMap j (krylovVector T g d)) =
      inner ℝ g (linearIter T.toLinearMap j g) := by
  rw [linearIter_krylovCompression T g hj]
  exact Submodule.coe_inner _ _ _

/-- Finite atomic representation of every original vector moment through the cutoff. -/
theorem inner_linearIter_eq_krylovAtomicMoment (T : E →L[ℝ] E) (g : E)
    (hT : T.toLinearMap.IsSymmetric) {d j : ℕ} (hj : j ≤ d) :
    inner ℝ g (linearIter T.toLinearMap j g) =
      atomicMoment
        (finiteAtomWeight (krylovCompression T g d).toLinearMap
          (krylovCompression_isSymmetric T g d hT) (krylovVector T g d))
        (finiteAtomEigenvalue (krylovCompression T g d).toLinearMap
          (krylovCompression_isSymmetric T g d hT)) j := by
  rw [← inner_linearIter_krylovCompression_eq T g hj]
  exact inner_linearIter_eq_atomicMoment _ (krylovCompression_isSymmetric T g d hT) _ j

/-- If the original operator has norm at most `1/2`, all eigenvalue atoms of the Krylov compression
lie in `[-1/2,1/2]`. -/
theorem krylovAtomEigenvalue_mem_halfInterval (T : E →L[ℝ] E) (g : E) (d : ℕ)
    (hT : T.toLinearMap.IsSymmetric) (hnorm : ‖T‖ ≤ (1 : ℝ) / 2) (i) :
    finiteAtomEigenvalue (krylovCompression T g d).toLinearMap
        (krylovCompression_isSymmetric T g d hT) i ∈
      Set.Icc (-(1 : ℝ) / 2) (1 / 2) := by
  apply eigenvalue_mem_halfInterval (krylovCompression T g d)
    ((norm_krylovCompression_le T g d).trans hnorm)
  · exact ((krylovCompression_isSymmetric T g d hT).eigenvectorBasis rfl).orthonormal.ne_zero i
  · change (krylovCompression T g d).toLinearMap
        ((krylovCompression_isSymmetric T g d hT).eigenvectorBasis rfl i) =
      finiteAtomEigenvalue (krylovCompression T g d).toLinearMap
          (krylovCompression_isSymmetric T g d hT) i •
        (krylovCompression_isSymmetric T g d hT).eigenvectorBasis rfl i
    simpa [finiteAtomEigenvalue] using
      (krylovCompression_isSymmetric T g d hT).apply_eigenvectorBasis rfl i

end OddCycleBound.DenseRegion
