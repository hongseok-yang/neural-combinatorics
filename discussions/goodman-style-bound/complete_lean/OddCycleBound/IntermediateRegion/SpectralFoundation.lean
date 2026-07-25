import OddCycleBound.IntermediateRegion.HilbertSchmidtBound
import OddCycleBound.IntermediateRegion.BoundedKernelL2
import OddCycleBound.Spectral.C9Spectral

/-!
# Reusable compact self-adjoint spectral data for the intermediate region

The C9 development contains the hard compact-spectral lemmas needed here,
but its public data structures are specialized to a nonnegative graphon
kernel.  The centered the intermediate region kernel is signed.  This file extracts the
operator-theoretic core in a kernel-independent form.

For a compact self-adjoint operator `T`, `NonzeroEigenIndex T` contains one
finite orthonormal-basis index for every nonzero eigenspace.  Its ambient
modes are orthonormal, their span is dense in the orthogonal complement of
the zero eigenspace, and they give a vector-valued expansion of `T f`.
No separability assumption on the ambient Hilbert space is used.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.Spectral
open OddCycleBound.Spectral.CompactSpectral
open OddCycleBound.Spectral.InfiniteSpectral
open OddCycleBound.Spectral.L2Kernel

universe u

section AbstractSpectrum

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [CompleteSpace E]

/-- The closed subspace carrying all nonzero spectral modes of `T`. -/
abbrev zeroEigenOrthogonal (T : E →L[Real] E) : Submodule Real E :=
  (Module.End.eigenspace (T : Module.End Real E) 0)ᗮ

/-- The canonical index type: a standard finite orthonormal-basis index in
every nonzero eigenspace.  Fibers over non-eigenvalues are empty. -/
abbrev NonzeroEigenIndex (T : E →L[Real] E) : Type :=
  Sigma fun lambda : {lambda : Real // lambda ≠ 0} =>
    Fin (Module.finrank Real
      (Module.End.eigenspace (T : Module.End Real E) lambda.1))

/-- Every nonzero eigenspace of a compact operator is finite-dimensional. -/
theorem nonzeroEigenspace_finiteDimensional
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (lambda : {lambda : Real // lambda ≠ 0}) :
    FiniteDimensional Real
      (Module.End.eigenspace (T : Module.End Real E) lambda.1) :=
  ContinuousLinearMap.finite_dimensional_eigenspace
    (T := T) hcompact lambda.1 lambda.2

/-- The standard Hilbert basis chosen in a nonzero eigenspace. -/
noncomputable def nonzeroEigenspaceBasis
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (lambda : {lambda : Real // lambda ≠ 0}) :
    HilbertBasis
      (Fin (Module.finrank Real
        (Module.End.eigenspace (T : Module.End Real E) lambda.1)))
      Real (Module.End.eigenspace (T : Module.End Real E) lambda.1) := by
  letI := nonzeroEigenspace_finiteDimensional T hcompact lambda
  exact (stdOrthonormalBasis Real
    (Module.End.eigenspace (T : Module.End Real E) lambda.1)).toHilbertBasis

/-- The eigenvalue attached to a canonical nonzero spectral index. -/
def nonzeroEigenvalue (T : E →L[Real] E)
    (i : NonzeroEigenIndex T) : Real := i.1.1

/-- The ambient eigenmode attached to a canonical nonzero spectral index. -/
noncomputable def nonzeroEigenmode
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (i : NonzeroEigenIndex T) : E :=
  ((nonzeroEigenspaceBasis T hcompact i.1 i.2 :
      Module.End.eigenspace (T : Module.End Real E) i.1.1) : E)

theorem nonzeroEigenvalue_ne
    (T : E →L[Real] E) (i : NonzeroEigenIndex T) :
    nonzeroEigenvalue T i ≠ 0 :=
  i.1.2

/-- The canonical index type is countable, even though it is presented as a
sigma over all nonzero real numbers. -/
theorem nonzeroEigenIndex_countable
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    Countable (NonzeroEigenIndex T) := by
  exact compactSelfAdjoint_countable_nonzero_eigenspace_finIndex
    T hcompact hsymm

/-- Canonical modes belonging to distinct nonzero eigenspaces (or distinct
basis positions in one eigenspace) are orthonormal. -/
theorem nonzeroEigenmode_orthonormal
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    Orthonormal Real (nonzeroEigenmode T hcompact) := by
  letI hfin : ∀ lambda : {lambda : Real // lambda ≠ 0},
      FiniteDimensional Real
        (Module.End.eigenspace (T : Module.End Real E) lambda.1) := by
    intro lambda
    exact nonzeroEigenspace_finiteDimensional T hcompact lambda
  exact compactSelfAdjoint_nonzero_eigenspace_hilbertBasis_orthonormal
    T hsymm (nonzeroEigenspaceBasis T hcompact)

/-- Each canonical mode is a genuine eigenvector. -/
theorem nonzeroEigenmode_diagonal
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (i : NonzeroEigenIndex T) :
    T (nonzeroEigenmode T hcompact i) =
      nonzeroEigenvalue T i • nonzeroEigenmode T hcompact i := by
  exact Module.End.mem_eigenspace_iff.mp
    (nonzeroEigenspaceBasis T hcompact i.1 i.2).property

/-- A nonzero mode is orthogonal to the zero eigenspace. -/
theorem nonzeroEigenmode_mem_zeroEigenOrthogonal
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) (i : NonzeroEigenIndex T) :
    nonzeroEigenmode T hcompact i ∈ zeroEigenOrthogonal T := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  have horth :
      Module.End.eigenspace (T : Module.End Real E) i.1.1 ⟂
        Module.End.eigenspace (T : Module.End Real E) 0 :=
    (LinearMap.IsSymmetric.orthogonalFamily_eigenspaces
      (T := (T : Module.End Real E)) hsymm).isOrtho i.1.2
  exact horth.symm.inner_eq hy
    (nonzeroEigenspaceBasis T hcompact i.1 i.2).property

/-- The canonical modes, regarded inside the nonzero spectral subspace. -/
noncomputable def nonzeroEigenmodeSubspace
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) (i : NonzeroEigenIndex T) :
    zeroEigenOrthogonal T :=
  ⟨nonzeroEigenmode T hcompact i,
    nonzeroEigenmode_mem_zeroEigenOrthogonal T hcompact hsymm i⟩

/-- The nonzero modes are dense in the orthogonal complement of the kernel. -/
theorem nonzeroEigenmodeSubspace_dense
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    (Submodule.span Real
      (Set.range (nonzeroEigenmodeSubspace T hcompact hsymm)))ᗮ = ⊥ := by
  letI hfin : ∀ lambda : {lambda : Real // lambda ≠ 0},
      FiniteDimensional Real
        (Module.End.eigenspace (T : Module.End Real E) lambda.1) := by
    intro lambda
    exact nonzeroEigenspace_finiteDimensional T hcompact lambda
  have h :=
    compactSelfAdjoint_nonzero_eigenspace_hilbertBasis_dense_in_zero_orthogonal
      T hcompact hsymm (nonzeroEigenspaceBasis T hcompact)
  convert h using 1
  apply congrArg (fun S : Submodule Real (zeroEigenOrthogonal T) => Sᗮ)
  apply congrArg (Submodule.span Real)
  ext x
  simp only [Set.mem_range]
  constructor <;> rintro ⟨i, rfl⟩
  · exact ⟨i, Subtype.ext rfl⟩
  · exact ⟨i, Subtype.ext rfl⟩

/-- Orthonormality after restricting the modes to their closed spectral
subspace. -/
theorem nonzeroEigenmodeSubspace_orthonormal
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    Orthonormal Real (nonzeroEigenmodeSubspace T hcompact hsymm) := by
  rw [orthonormal_iff_ite]
  intro i j
  simpa [nonzeroEigenmodeSubspace] using
    (orthonormal_iff_ite.mp
      (nonzeroEigenmode_orthonormal T hcompact hsymm) i j)

/-- The Hilbert basis of the nonzero spectral subspace assembled from all
finite-dimensional nonzero eigenspaces. -/
noncomputable def nonzeroSpectralHilbertBasis
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    HilbertBasis (NonzeroEigenIndex T) Real (zeroEigenOrthogonal T) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (nonzeroEigenmodeSubspace_orthonormal T hcompact hsymm)
    (nonzeroEigenmodeSubspace_dense T hcompact hsymm)

@[simp]
theorem coe_nonzeroSpectralHilbertBasis
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) (i : NonzeroEigenIndex T) :
    (((nonzeroSpectralHilbertBasis T hcompact hsymm i :
        zeroEigenOrthogonal T) : E)) =
      nonzeroEigenmode T hcompact i := by
  have hfun := HilbertBasis.coe_mkOfOrthogonalEqBot
    (nonzeroEigenmodeSubspace_orthonormal T hcompact hsymm)
    (nonzeroEigenmodeSubspace_dense T hcompact hsymm)
  exact congrArg (fun x : zeroEigenOrthogonal T => (x : E))
    (congrFun hfun i)

/-- The range of a symmetric operator lies in its nonzero spectral
subspace. -/
theorem apply_mem_zeroEigenOrthogonal
    (T : E →L[Real] E) (hsymm : T.IsSymmetric) (f : E) :
    T f ∈ zeroEigenOrthogonal T := by
  exact symmetric_range_le_orthogonal_zero_eigenspace hsymm
    (LinearMap.mem_range.mpr ⟨f, rfl⟩)

/-- Vector-valued compact spectral expansion, with exactly the nonzero modes
listed.  A residual component of `f` in `ker T` is harmless because `T`
annihilates it. -/
theorem compactSelfAdjoint_action_expansion
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) (f : E) :
    HasSum
      (fun i : NonzeroEigenIndex T =>
        (nonzeroEigenvalue T i *
          inner Real f (nonzeroEigenmode T hcompact i)) •
            nonzeroEigenmode T hcompact i)
      (T f) := by
  let U := zeroEigenOrthogonal T
  let b := nonzeroSpectralHilbertBasis T hcompact hsymm
  have hproj := (b.hasSum_orthogonalProjectionOnto (T f)).mapL U.subtypeL
  have hself : ((U.orthogonalProjectionOnto (T f) : U) : E) = T f := by
    let v : U := ⟨T f, apply_mem_zeroEigenOrthogonal T hsymm f⟩
    have hv := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (K := U) v
    simpa [v] using congrArg (fun x : U => (x : E)) hv
  have hproj' :
      HasSum
        (fun i : NonzeroEigenIndex T =>
          inner Real (T f) (nonzeroEigenmode T hcompact i) •
            nonzeroEigenmode T hcompact i)
        ((U.orthogonalProjectionOnto (T f) : U) : E) := by
    refine hproj.congr_fun ?_
    intro i
    simp [b, U, coe_nonzeroSpectralHilbertBasis, real_inner_comm]
  rw [hself] at hproj'
  refine hproj'.congr_fun ?_
  intro i
  have hinner :
      inner Real (T f) (nonzeroEigenmode T hcompact i) =
        nonzeroEigenvalue T i *
          inner Real f (nonzeroEigenmode T hcompact i) := by
    calc
      inner Real (T f) (nonzeroEigenmode T hcompact i) =
          inner Real f (T (nonzeroEigenmode T hcompact i)) :=
        hsymm f (nonzeroEigenmode T hcompact i)
      _ = _ := by
        rw [nonzeroEigenmode_diagonal T hcompact i]
        simp [inner_smul_right]
  rw [hinner]

end AbstractSpectrum

section CenteredSpectrum

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega → Omega → Real}

/-- The canonical nonzero spectral index for the centered graphon operator. -/
abbrev CenteredEigenIndex (hW : IsGraphon W mu) : Type :=
  NonzeroEigenIndex (OddCycleBound.DenseRegion.centeredGraphonOp hW)

/-- Centered nonzero eigenvalues. -/
def centeredEigenvalue (hW : IsGraphon W mu)
    (i : CenteredEigenIndex hW) : Real :=
  nonzeroEigenvalue (OddCycleBound.DenseRegion.centeredGraphonOp hW) i

/-- Centered nonzero eigenmodes. -/
noncomputable def centeredEigenmode (hW : IsGraphon W mu)
    (i : CenteredEigenIndex hW) : Lp Real 2 mu :=
  nonzeroEigenmode (OddCycleBound.DenseRegion.centeredGraphonOp hW)
    (centeredGraphonOp_isCompact hW) i

theorem centeredEigenmode_orthonormal (hW : IsGraphon W mu) :
    Orthonormal Real (centeredEigenmode hW) := by
  exact nonzeroEigenmode_orthonormal
    (OddCycleBound.DenseRegion.centeredGraphonOp hW)
    (centeredGraphonOp_isCompact hW)
    (OddCycleBound.DenseRegion.centeredGraphonOp_isSymmetric hW)

theorem centeredEigenmode_diagonal (hW : IsGraphon W mu)
    (i : CenteredEigenIndex hW) :
    OddCycleBound.DenseRegion.centeredGraphonOp hW (centeredEigenmode hW i) =
      centeredEigenvalue hW i • centeredEigenmode hW i := by
  exact nonzeroEigenmode_diagonal
    (OddCycleBound.DenseRegion.centeredGraphonOp hW)
    (centeredGraphonOp_isCompact hW) i

theorem centeredGraphonOp_action_expansion (hW : IsGraphon W mu)
    (f : Lp Real 2 mu) :
    HasSum
      (fun i : CenteredEigenIndex hW =>
        (centeredEigenvalue hW i * inner Real f (centeredEigenmode hW i)) •
          centeredEigenmode hW i)
      (OddCycleBound.DenseRegion.centeredGraphonOp hW f) := by
  exact compactSelfAdjoint_action_expansion
    (OddCycleBound.DenseRegion.centeredGraphonOp hW)
    (centeredGraphonOp_isCompact hW)
    (OddCycleBound.DenseRegion.centeredGraphonOp_isSymmetric hW) f

/-- Every finite collection of centered eigenvalues obeys the signed-kernel
Hilbert--Schmidt square bound. -/
theorem centeredEigenvalue_finite_square_bound (hW : IsGraphon W mu)
    (s : Finset (CenteredEigenIndex hW)) :
    s.sum (fun i => centeredEigenvalue hW i ^ 2) ≤
      kernelSqNorm mu (centeredKernel W mu) := by
  let hK := centeredKernel_goodK hW
  let row : Omega → Lp Real 2 mu := fun x =>
    OddCycleBound.Spectral.L2Kernel.goodL2 (mu := mu)
      (OddCycleBound.Spectral.L2Kernel.goodK_row hK x)
  have hdiagEnergy :
      s.sum (fun i => centeredEigenvalue hW i ^ 2) =
        s.sum (fun i => ‖centeredKernelOp hW (centeredEigenmode hW i)‖ ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hdiag :
        centeredKernelOp hW (centeredEigenmode hW i) =
          centeredEigenvalue hW i • centeredEigenmode hW i := by
      rw [centeredKernelOp_eq_centeredGraphonOp hW]
      exact centeredEigenmode_diagonal hW i
    have hnorm : ‖centeredEigenmode hW i‖ = 1 :=
      (centeredEigenmode_orthonormal hW).norm_eq_one i
    calc
      centeredEigenvalue hW i ^ 2 = |centeredEigenvalue hW i| ^ 2 := by
        rw [sq_abs]
      _ = ‖centeredEigenvalue hW i • centeredEigenmode hW i‖ ^ 2 := by
        rw [norm_smul, hnorm, mul_one, Real.norm_eq_abs]
      _ = ‖centeredKernelOp hW (centeredEigenmode hW i)‖ ^ 2 := by
        rw [hdiag]
  have hrowEnergy :
      s.sum (fun i => ‖centeredKernelOp hW (centeredEigenmode hW i)‖ ^ 2) =
        ∫ x, s.sum (fun i =>
          inner Real (row x) (centeredEigenmode hW i) ^ 2) ∂mu := by
    simpa [centeredKernelOp, hK, row] using
      (sum_norm_kernelOpGoodKCLM_sq_eq_integral_sum_row_inner_l2_sq
        (mu := mu) (centeredKernel_goodK hW)
        (by norm_num : (0 : Real) ≤ 4) (abs_centeredKernel_le_four hW)
        (centeredKernel_symm hW) (centeredEigenmode hW) s)
  have hleftInt : Integrable (fun x : Omega =>
      s.sum (fun i => inner Real (row x) (centeredEigenmode hW i) ^ 2)) mu := by
    simpa [hK, row] using
      (integrable_sum_goodK_row_inner_l2_sq
        (mu := mu) (centeredKernel_goodK hW)
        (by norm_num : (0 : Real) ≤ 4) (abs_centeredKernel_le_four hW)
        (centeredEigenmode hW) s)
  have hrowInt : Integrable (fun x : Omega => inner Real (row x) (row x)) mu := by
    simpa [hK, row] using
      (OddCycleBound.Spectral.L2Kernel.integrable_goodK_row_inner_self
        (mu := mu) (centeredKernel_goodK hW))
  have hpoint : ∀ x : Omega,
      s.sum (fun i => inner Real (row x) (centeredEigenmode hW i) ^ 2) ≤
        inner Real (row x) (row x) := by
    intro x
    exact sum_inner_sq_le_self_of_orthonormal
      (centeredEigenmode_orthonormal hW) (row x) s
  calc
    s.sum (fun i => centeredEigenvalue hW i ^ 2) =
        s.sum (fun i => ‖centeredKernelOp hW (centeredEigenmode hW i)‖ ^ 2) :=
      hdiagEnergy
    _ = ∫ x, s.sum (fun i =>
          inner Real (row x) (centeredEigenmode hW i) ^ 2) ∂mu := hrowEnergy
    _ ≤ ∫ x, inner Real (row x) (row x) ∂mu :=
      integral_mono hleftInt hrowInt hpoint
    _ = kernelSqNorm mu (centeredKernel W mu) := by
      simpa [hK, row] using
        (OddCycleBound.Spectral.L2Kernel.integral_goodK_row_inner_self_eq_kernelSqNorm
          (mu := mu) (centeredKernel_goodK hW))

/-- Square summability of the complete nonzero centered spectrum. -/
theorem centeredEigenvalue_square_summable (hW : IsGraphon W mu) :
    Summable (fun i : CenteredEigenIndex hW => centeredEigenvalue hW i ^ 2) := by
  apply summable_of_sum_le (fun i => sq_nonneg (centeredEigenvalue hW i))
  intro s
  simpa using centeredEigenvalue_finite_square_bound hW s

/-- The intermediate-region square trace is the sum of the squares of all nonzero
centered eigenvalues. -/
noncomputable def centeredTraceSq (hW : IsGraphon W mu) : Real :=
  ∑' i : CenteredEigenIndex hW, centeredEigenvalue hW i ^ 2

theorem centeredTraceSq_le_kernelSqNorm (hW : IsGraphon W mu) :
    centeredTraceSq hW ≤ kernelSqNorm mu (centeredKernel W mu) := by
  unfold centeredTraceSq
  exact Real.tsum_le_of_sum_le
    (fun i => sq_nonneg (centeredEigenvalue hW i))
    (fun s => by
      simpa using centeredEigenvalue_finite_square_bound hW s)

/-- Spectral form of the centered variance bound from the intermediate-region paper:
`Tr(A²) + 2 ‖g‖₂² ≤ p q`. -/
theorem centeredTraceSq_add_degree_bound (hW : IsGraphon W mu) :
    centeredTraceSq hW +
        2 * ‖OddCycleBound.DenseRegion.centeredDegreeL2 hW‖ ^ 2 ≤
      edgeDensity W mu * (1 - edgeDensity W mu) := by
  calc
    centeredTraceSq hW +
          2 * ‖OddCycleBound.DenseRegion.centeredDegreeL2 hW‖ ^ 2 ≤
        kernelSqNorm mu (centeredKernel W mu) +
          2 * ‖OddCycleBound.DenseRegion.centeredDegreeL2 hW‖ ^ 2 :=
      add_le_add (centeredTraceSq_le_kernelSqNorm hW) (le_refl _)
    _ ≤ edgeDensity W mu * (1 - edgeDensity W mu) :=
      centeredKernel_hilbertSchmidt_bound hW

end CenteredSpectrum

end OddCycleBound.IntermediateRegion
