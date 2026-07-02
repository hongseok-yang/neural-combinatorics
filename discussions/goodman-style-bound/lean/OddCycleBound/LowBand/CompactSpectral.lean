import OddCycleBound.LowBand.L2Kernel
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Compact self-adjoint spectral skeleton

This file records the part of the graphon spectral argument that is already
available from Mathlib's Hilbert-space operator theory.

It does not prove the trace-class/Lidskii identities needed for C9 graphons.
Instead, it cleanly separates the basic compact self-adjoint spectral theorem
from the remaining trace/eigenvalue-enumeration bridge used in
`OddCycleBound.LowBand.InfiniteSpectral`.
-/

noncomputable section

open MeasureTheory

namespace OddCycleBound
namespace LowBand
namespace CompactSpectral

open Module End

/-- A continuous linear map whose range is contained in a finite-dimensional
submodule is compact.

This is the finite-rank compactness principle used by both tensor-simple and
Hilbert-Schmidt approximation arguments. -/
theorem isCompactOperator_of_finiteDimensional_range
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [LocallyCompactSpace 𝕜]
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (T : E →L[𝕜] F) (U : Submodule 𝕜 F)
    [FiniteDimensional 𝕜 U]
    (hTU : ∀ x, T x ∈ U) :
    IsCompactOperator T := by
  let TU : E →L[𝕜] U := T.codRestrict U hTU
  haveI : ProperSpace U := FiniteDimensional.proper 𝕜 U
  have hcompactTU : IsCompactOperator TU :=
    isCompactOperator_of_locallyCompactSpace_dom TU
  have hcompact : IsCompactOperator (U.subtypeL.comp TU) :=
    hcompactTU.clm_comp U.subtypeL
  have hcomp_eq : U.subtypeL.comp TU = T := by
    ext x
    rfl
  simpa [hcomp_eq] using hcompact

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The compact self-adjoint Hilbert-space spectral facts used as the skeleton
behind the C9 graphon spectral package.

The still-missing graphon work is not these facts, but the construction of a
countable eigenvalue sequence for the graphon integral operator together with
the square/cube/ninth trace identities. -/
structure CompactSelfAdjointSkeleton (T : E →L[𝕜] E) : Prop where
  orthogonal_family_eigenspaces :
    OrthogonalFamily 𝕜
      (fun μ => eigenspace (T : End 𝕜 E) μ)
      (fun μ => (eigenspace (T : End 𝕜 E) μ).subtypeₗᵢ)
  eigenspaces_complete :
    (⨆ μ, eigenspace (T : End 𝕜 E) μ)ᗮ = ⊥
  finite_dimensional_nonzero_eigenspace :
    ∀ μ : 𝕜, μ ≠ 0 -> FiniteDimensional 𝕜 (eigenspace T.toLinearMap μ)
  zero_iff_only_zero_eigenvalue :
    (∀ μ : 𝕜, HasEigenvalue (T : End 𝕜 E) μ -> μ = 0) ↔ T = 0

/-- Mathlib's compact self-adjoint spectral theorem, packaged in the shape
needed by the C9 operator discussion. -/
theorem compactSelfAdjointSkeleton
    {T : E →L[𝕜] E}
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    CompactSelfAdjointSkeleton T where
  orthogonal_family_eigenspaces :=
    LinearMap.IsSymmetric.orthogonalFamily_eigenspaces
      (T := (T : End 𝕜 E)) hsymm
  eigenspaces_complete :=
    ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
      hcompact hsymm
  finite_dimensional_nonzero_eigenspace :=
    fun μ hμ =>
      ContinuousLinearMap.finite_dimensional_eigenspace
        (T := T) hcompact μ hμ
  zero_iff_only_zero_eigenvalue :=
    ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero
      hcompact hsymm

/-- If a compact self-adjoint operator has no nonzero eigenvalue, then it is
zero.  This is often the first compact-spectral reduction used when extracting
nonzero modes. -/
theorem compactSelfAdjoint_eq_zero_of_no_nonzero_eigenvalue
    {T : E →L[𝕜] E}
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric)
    (hzero : ∀ μ : 𝕜, HasEigenvalue (T : End 𝕜 E) μ -> μ = 0) :
    T = 0 :=
  (compactSelfAdjointSkeleton hcompact hsymm).zero_iff_only_zero_eigenvalue.mp
    hzero

omit [CompleteSpace E] in
/-- Eigenspaces of a compact self-adjoint operator are mutually orthogonal.

The compactness assumption keeps this theorem aligned with the compact
spectral skeleton; the orthogonality itself is the standard self-adjoint
Hilbert-space fact.  It makes no finite-spectrum assertion. -/
theorem compactSelfAdjoint_orthogonalFamily_eigenspaces
    {T : E →L[𝕜] E}
    (_hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    OrthogonalFamily 𝕜
      (fun μ => eigenspace (T : End 𝕜 E) μ)
      (fun μ => (eigenspace (T : End 𝕜 E) μ).subtypeₗᵢ) :=
  LinearMap.IsSymmetric.orthogonalFamily_eigenspaces
    (T := (T : End 𝕜 E)) hsymm

omit [CompleteSpace E] in
/-- The range of a symmetric operator is orthogonal to its zero eigenspace.

For compact spectral decompositions this is the first half of the statement
that `T f` lives in the closed span of the nonzero eigenspaces: if
`T u = 0`, then `⟪u, T f⟫ = ⟪T u, f⟫ = 0`. -/
theorem symmetric_range_le_orthogonal_zero_eigenspace
    {T : E →L[𝕜] E}
    (hsymm : T.IsSymmetric) :
    LinearMap.range T.toLinearMap ≤
      (eigenspace (T : End 𝕜 E) 0)ᗮ := by
  intro y hy
  rw [Submodule.mem_orthogonal]
  rcases LinearMap.mem_range.mp hy with ⟨x, rfl⟩
  intro u hu
  have hTu : T u = 0 := by
    simpa using hu
  calc
    inner 𝕜 u (T x) = inner 𝕜 (T u) x := by
      simpa using (hsymm u x).symm
    _ = 0 := by simp [hTu]

/-- Inside the orthogonal complement of the zero eigenspace, the nonzero
eigenspaces are dense.

Equivalently, a vector which is orthogonal to the zero eigenspace and to every
nonzero eigenspace is zero.  This is the abstract compact self-adjoint
statement needed before choosing a Hilbert basis of nonzero eigenvectors. -/
theorem compactSelfAdjoint_nonzero_iSup_orthogonal_inf_zero_eigenspace_orthogonal_eq_bot
    {T : E →L[𝕜] E}
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    ((⨆ lambda : {lambda : 𝕜 // lambda ≠ 0},
        eigenspace (T : End 𝕜 E) lambda.1)ᗮ ⊓
      (eigenspace (T : End 𝕜 E) 0)ᗮ) = ⊥ := by
  let N : Submodule 𝕜 E :=
    ⨆ lambda : {lambda : 𝕜 // lambda ≠ 0},
      eigenspace (T : End 𝕜 E) lambda.1
  let Z : Submodule 𝕜 E := eigenspace (T : End 𝕜 E) 0
  have hcover : N ⊔ Z = ⨆ lambda : 𝕜, eigenspace (T : End 𝕜 E) lambda := by
    refine le_antisymm ?_ ?_
    · refine sup_le ?_ ?_
      · refine iSup_le ?_
        intro lambda
        exact le_iSup (fun lambda : 𝕜 =>
          eigenspace (T : End 𝕜 E) lambda) lambda.1
      · exact le_iSup (fun lambda : 𝕜 =>
          eigenspace (T : End 𝕜 E) lambda) 0
    · refine iSup_le ?_
      intro lambda
      by_cases hlambda : lambda = 0
      · subst lambda
        exact le_sup_right
      · have hleN :
            eigenspace (T : End 𝕜 E) lambda ≤ N :=
          le_iSup (fun lambda : {lambda : 𝕜 // lambda ≠ 0} =>
            eigenspace (T : End 𝕜 E) lambda.1) ⟨lambda, hlambda⟩
        exact hleN.trans le_sup_left
  calc
    ((⨆ lambda : {lambda : 𝕜 // lambda ≠ 0},
        eigenspace (T : End 𝕜 E) lambda.1)ᗮ ⊓
      (eigenspace (T : End 𝕜 E) 0)ᗮ)
        = Nᗮ ⊓ Zᗮ := by rfl
    _ = (N ⊔ Z)ᗮ := Submodule.inf_orthogonal N Z
    _ = (⨆ lambda : 𝕜, eigenspace (T : End 𝕜 E) lambda)ᗮ := by
      rw [hcover]
    _ = ⊥ :=
      (compactSelfAdjointSkeleton hcompact hsymm).eigenspaces_complete

section Real

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H]
  [CompleteSpace H]

/-- A nonzero compact self-adjoint real Hilbert-space operator has a nonzero
eigenvalue at one of the two norm-radius spectral endpoints.

This is the infinite-dimensional replacement for the finite-dimensional
statement that a self-adjoint matrix has an eigenvalue of maximal absolute
value.  It uses Mathlib's spectral-radius theorem and the Fredholm alternative
for compact operators; it does not assert finite spectrum. -/
theorem compactSelfAdjoint_hasEigenvalue_norm_or_neg_norm
    {T : H →L[Real] H}
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric)
    (hne : T ≠ 0) :
    Module.End.HasEigenvalue T.toLinearMap ‖T‖ ∨
      Module.End.HasEigenvalue T.toLinearMap (-‖T‖) := by
  have hsa : IsSelfAdjoint T := hsymm.isSelfAdjoint
  have hsr : spectralRadius Real T = (‖T‖₊ : ENNReal) :=
    ContinuousLinearMap.spectralRadius_eq_nnnorm T hsa
  have hspec_nonempty : (spectrum Real T).Nonempty := by
    by_contra hneempty
    have hempty : spectrum Real T = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hneempty
    have hsr0 : spectralRadius Real T = 0 := by
      simp [spectralRadius, hempty]
    have hnormnn : (‖T‖₊ : ENNReal) = 0 := by
      simpa [hsr] using hsr0
    have hnormnn' : ‖T‖₊ = 0 := by
      exact_mod_cast hnormnn
    have hnorm : ‖T‖ = 0 := by
      simpa using congrArg (fun x : NNReal => (x : Real)) hnormnn'
    exact hne ((ContinuousLinearMap.opNorm_zero_iff T).mp hnorm)
  have hspec := Real.spectralRadius_mem_spectrum_or (a := T) hspec_nonempty
  have hnorm_toReal : (spectralRadius Real T).toReal = ‖T‖ := by
    rw [hsr]
    simp
  rcases hspec with hpos | hneg
  · left
    have hmem : ‖T‖ ∈ spectrum Real T := by
      simpa [hnorm_toReal] using hpos
    have hnorm_ne : ‖T‖ ≠ 0 := by
      intro h0
      exact hne ((ContinuousLinearMap.opNorm_zero_iff T).mp h0)
    exact (IsCompactOperator.hasEigenvalue_iff_mem_spectrum hcompact hnorm_ne).mpr
      hmem
  · right
    have hmem : -‖T‖ ∈ spectrum Real T := by
      simpa [hnorm_toReal] using hneg
    have hnorm_ne : -‖T‖ ≠ 0 := by
      intro h0
      apply hne
      apply (ContinuousLinearMap.opNorm_zero_iff T).mp
      linarith
    exact (IsCompactOperator.hasEigenvalue_iff_mem_spectrum hcompact hnorm_ne).mpr
      hmem

/-- The norm-radius endpoint eigenvalue of a nonzero compact self-adjoint real
Hilbert-space operator has finite-dimensional eigenspace.

This packages together spectral-radius endpoint extraction and the
finite-multiplicity theorem for nonzero compact-operator eigenvalues. -/
theorem compactSelfAdjoint_exists_finiteDimensional_norm_endpoint_eigenspace
    {T : H →L[Real] H}
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric)
    (hne : T ≠ 0) :
    Exists (fun lambda : Real =>
      (lambda = ‖T‖ ∨ lambda = -‖T‖) ∧
        lambda ≠ 0 ∧
        Module.End.HasEigenvalue T.toLinearMap lambda ∧
        FiniteDimensional Real (eigenspace T.toLinearMap lambda)) := by
  have hend :=
    compactSelfAdjoint_hasEigenvalue_norm_or_neg_norm
      (T := T) hcompact hsymm hne
  rcases hend with hpos | hneg
  · refine ⟨‖T‖, Or.inl rfl, ?_, hpos, ?_⟩
    · intro h0
      exact hne ((ContinuousLinearMap.opNorm_zero_iff T).mp h0)
    · exact ContinuousLinearMap.finite_dimensional_eigenspace
        (T := T) hcompact ‖T‖ (by
          intro h0
          exact hne ((ContinuousLinearMap.opNorm_zero_iff T).mp h0))
  · refine ⟨-‖T‖, Or.inr rfl, ?_, hneg, ?_⟩
    · intro h0
      apply hne
      apply (ContinuousLinearMap.opNorm_zero_iff T).mp
      linarith
    · exact ContinuousLinearMap.finite_dimensional_eigenspace
        (T := T) hcompact (-‖T‖) (by
          intro h0
          apply hne
          apply (ContinuousLinearMap.opNorm_zero_iff T).mp
          linarith)

omit [CompleteSpace H] in
/-- Eigenvectors of a real self-adjoint operator with distinct eigenvalues are
orthogonal. -/
theorem selfAdjoint_eigenvectors_orthogonal_of_ne
    {T : H →L[Real] H}
    (hsymm : T.IsSymmetric)
    {lambda mu : Real} (hneq : lambda ≠ mu) {v w : H}
    (hv : Module.End.HasEigenvector T.toLinearMap lambda v)
    (hw : Module.End.HasEigenvector T.toLinearMap mu w) :
    inner Real w v = 0 := by
  have horth :=
    (LinearMap.IsSymmetric.orthogonalFamily_eigenspaces
      (T := (T : End Real H)) hsymm).pairwise hneq
  exact horth hv.1 w hw.1

omit [CompleteSpace H] in
private lemma dist_smul_orthonormal_sq
    {mode : Nat → H} (horth : Orthonormal Real mode)
    {i j : Nat} (hij : i ≠ j) (a b : Real) :
    dist (a • mode i) (b • mode j) ^ 2 = a ^ 2 + b ^ 2 := by
  have hinner_mode : inner Real (mode i) (mode j) = 0 :=
    horth.inner_eq_zero hij
  have hinner : inner Real (a • mode i) (b • mode j) = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, hinner_mode]
    ring
  have hnorm_i : ‖mode i‖ = 1 := horth.norm_eq_one i
  have hnorm_j : ‖mode j‖ = 1 := horth.norm_eq_one j
  calc
    dist (a • mode i) (b • mode j) ^ 2
        = ‖a • mode i - b • mode j‖ ^ 2 := by rw [dist_eq_norm]
    _ = ‖a • mode i‖ ^ 2 + ‖b • mode j‖ ^ 2 := by
        simpa [pow_two] using
          norm_sub_sq_eq_norm_sq_add_norm_sq_real hinner
    _ = a ^ 2 + b ^ 2 := by
        simp [norm_smul, Real.norm_eq_abs, hnorm_i, hnorm_j, sq_abs]

omit [CompleteSpace H] in
private lemma le_dist_smul_orthonormal_of_le_abs
    {mode : Nat → H} (horth : Orthonormal Real mode)
    {i j : Nat} (hij : i ≠ j) {eps a b : Real}
    (heps : 0 < eps) (ha : eps ≤ |a|) :
    eps ≤ dist (a • mode i) (b • mode j) := by
  by_contra hnot
  have hlt : dist (a • mode i) (b • mode j) < eps :=
    lt_of_not_ge hnot
  have hlt_sq :
      dist (a • mode i) (b • mode j) ^ 2 < eps ^ 2 := by
    refine sq_lt_sq.mpr ?_
    simpa [abs_of_nonneg dist_nonneg, abs_of_pos heps] using hlt
  have ha_sq : eps ^ 2 ≤ a ^ 2 := by
    exact sq_le_sq.mpr (by simpa [abs_of_pos heps] using ha)
  have hdist_sq :=
    dist_smul_orthonormal_sq (H := H) horth hij a b
  have hdist_ge : eps ^ 2 ≤ dist (a • mode i) (b • mode j) ^ 2 := by
    rw [hdist_sq]
    nlinarith [sq_nonneg b]
  nlinarith

omit [CompleteSpace H] in
/-- A compact operator cannot have infinitely many orthonormal eigenmodes whose
eigenvalues stay uniformly away from zero along a subsequence.

This is the graphon-safe replacement for a finite-spectrum intuition: compact
operators may have infinitely many nonzero eigenvalues, but no infinite
orthonormal eigenmode subsequence can keep them bounded below in absolute
value. -/
theorem compactOperator_no_orthonormal_eigen_subsequence_bounded_away
    {T : H →L[Real] H}
    (hcompact : IsCompactOperator T)
    {mode : Nat → H} {eigen : Nat → Real}
    (horth : Orthonormal Real mode)
    (hdiag : ∀ n, T (mode n) = eigen n • mode n)
    {φ : Nat → Nat} (hφ : StrictMono φ)
    {eps : Real} (heps : 0 < eps)
    (hlower : ∀ n, eps ≤ |eigen (φ n)|) :
    False := by
  obtain ⟨K, hK, hsub⟩ := hcompact.image_closedBall_subset_compact 1
  let yseq : Nat → H := fun n => T (mode (φ n))
  have hyseq : ∀ n, yseq n ∈ K := by
    intro n
    apply hsub
    refine ⟨mode (φ n), ?_, rfl⟩
    simp [Metric.mem_closedBall, dist_eq_norm, horth.norm_eq_one (φ n)]
  obtain ⟨y, _hyK, ψ, hψ, hlim⟩ := hK.tendsto_subseq hyseq
  have hhalf : 0 < eps / 2 := by linarith
  have hev : ∀ᶠ n in Filter.atTop, yseq (ψ n) ∈ Metric.ball y (eps / 2) :=
    hlim (Metric.ball_mem_nhds y hhalf)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have hN0 : dist (yseq (ψ N)) y < eps / 2 := by
    simpa [Metric.mem_ball] using hN N le_rfl
  have hN1 : dist (yseq (ψ (N + 1))) y < eps / 2 := by
    simpa [Metric.mem_ball] using hN (N + 1) (Nat.le_succ N)
  have hdist_lt : dist (yseq (ψ N)) (yseq (ψ (N + 1))) < eps := by
    calc
      dist (yseq (ψ N)) (yseq (ψ (N + 1)))
          ≤ dist (yseq (ψ N)) y + dist y (yseq (ψ (N + 1))) :=
            dist_triangle _ _ _
      _ = dist (yseq (ψ N)) y + dist (yseq (ψ (N + 1))) y := by
            rw [dist_comm y (yseq (ψ (N + 1)))]
      _ < eps := by linarith
  have hidx_ne : φ (ψ N) ≠ φ (ψ (N + 1)) := by
    exact ne_of_lt (hφ (hψ (Nat.lt_succ_self N)))
  have hdist_ge : eps ≤ dist (yseq (ψ N)) (yseq (ψ (N + 1))) := by
    have hbase :=
      le_dist_smul_orthonormal_of_le_abs
        (H := H) horth hidx_ne heps (hlower (ψ N))
        (b := eigen (φ (ψ (N + 1))))
    simpa [yseq, hdiag] using hbase
  exact not_lt_of_ge hdist_ge hdist_lt

omit [CompleteSpace H] in
/-- Eigenvalues attached to an orthonormal diagonalization sequence of a compact
operator tend to zero.

This permits infinitely many nonzero eigenvalues.  What compactness rules out is
an infinite orthonormal subsequence whose eigenvalues are bounded away from
zero. -/
theorem compactOperator_orthonormal_eigenvalues_tendsto_zero
    {T : H →L[Real] H}
    (hcompact : IsCompactOperator T)
    {mode : Nat → H} {eigen : Nat → Real}
    (horth : Orthonormal Real mode)
    (hdiag : ∀ n, T (mode n) = eigen n • mode n) :
    Filter.Tendsto eigen Filter.atTop (nhds 0) := by
  by_contra hnot
  obtain ⟨s, hs, hfreq⟩ :=
    (Filter.not_tendsto_iff_exists_frequently_notMem
      (f := eigen) (l₁ := Filter.atTop) (l₂ := nhds (0 : Real))).mp hnot
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hs
  have hfreq_lower : ∃ᶠ n in Filter.atTop, eps ≤ |eigen n| := by
    refine hfreq.mono ?_
    intro n hn
    have hnot_ball : eigen n ∉ Metric.ball (0 : Real) eps := by
      intro hmem
      exact hn (hball hmem)
    have hge : eps ≤ dist (eigen n) 0 := by
      exact le_of_not_gt (by simpa [Metric.mem_ball] using hnot_ball)
    simpa [dist_eq_norm] using hge
  obtain ⟨φ, hφ, hlower⟩ :=
    Filter.extraction_of_frequently_atTop hfreq_lower
  exact
    compactOperator_no_orthonormal_eigen_subsequence_bounded_away
      (T := T) hcompact horth hdiag hφ heps hlower

omit [CompleteSpace H] in
/-- Normalize a nonzero eigenvector of a continuous real-linear operator. -/
private theorem exists_unit_eigenvector_of_hasEigenvalue
    {T : H →L[Real] H} {lambda : Real}
    (hlambda : Module.End.HasEigenvalue T.toLinearMap lambda) :
    ∃ v : H, v ≠ 0 ∧ ‖v‖ = 1 ∧ T v = lambda • v := by
  obtain ⟨v, hv⟩ := hlambda.exists_hasEigenvector
  let u : H := (‖v‖)⁻¹ • v
  have hvne : v ≠ 0 := hv.2
  have hvnorm_ne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hvne
  have hvact : T v = lambda • v := by
    simpa using hv.apply_eq_smul
  have hunorm : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
    exact inv_mul_cancel₀ hvnorm_ne
  have huact : T u = lambda • u := by
    dsimp [u]
    calc
      T ((‖v‖)⁻¹ • v) = (‖v‖)⁻¹ • T v := by simp
      _ = (‖v‖)⁻¹ • (lambda • v) := by rw [hvact]
      _ = lambda • ((‖v‖)⁻¹ • v) := by
          rw [smul_smul, smul_smul]
          ring_nf
  have hune : u ≠ 0 := by
    intro hzero
    have : ‖u‖ = 0 := by simp [hzero]
    linarith
  exact ⟨u, hune, hunorm, huact⟩

/-- A nonzero compact self-adjoint real Hilbert-space operator has a genuine
unit eigenvector at one of the two norm-radius spectral endpoints.

This is still an infinite-dimensional compact-operator statement: it extracts
one endpoint mode and makes no finite-spectrum assertion. -/
theorem compactSelfAdjoint_exists_norm_endpoint_unit_eigenvector
    {T : H →L[Real] H}
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric)
    (hne : T ≠ 0) :
    ∃ lambda : Real, ∃ v : H,
      (lambda = ‖T‖ ∨ lambda = -‖T‖) ∧
        lambda ≠ 0 ∧ v ≠ 0 ∧ ‖v‖ = 1 ∧ T v = lambda • v := by
  have hend :=
    compactSelfAdjoint_hasEigenvalue_norm_or_neg_norm
      (T := T) hcompact hsymm hne
  rcases hend with hpos | hneg
  · obtain ⟨v, hvne, hvnorm, hvact⟩ :=
      exists_unit_eigenvector_of_hasEigenvalue (T := T) hpos
    refine ⟨‖T‖, v, Or.inl rfl, ?_, hvne, hvnorm, hvact⟩
    intro h0
    exact hne ((ContinuousLinearMap.opNorm_zero_iff T).mp h0)
  · obtain ⟨v, hvne, hvnorm, hvact⟩ :=
      exists_unit_eigenvector_of_hasEigenvalue (T := T) hneg
    refine ⟨-‖T‖, v, Or.inr rfl, ?_, hvne, hvnorm, hvact⟩
    intro h0
    apply hne
    apply (ContinuousLinearMap.opNorm_zero_iff T).mp
    linarith

omit [CompleteSpace H] in
/-- A compact self-adjoint operator has no infinite sequence of distinct
eigenvalues bounded uniformly away from zero.

This is the eigenvalue-level version of compactness: the nonzero spectrum may
be infinite, but any infinite list of distinct eigenvalues must accumulate only
at zero. -/
theorem compactSelfAdjoint_no_distinct_eigenvalue_sequence_bounded_away
    {T : H →L[Real] H}
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric)
    {lambda : Nat → Real}
    (heigen :
      ∀ n, Module.End.HasEigenvalue T.toLinearMap (lambda n))
    (hdistinct : Pairwise fun i j => lambda i ≠ lambda j)
    {eps : Real} (heps : 0 < eps)
    (hlower : ∀ n, eps <= |lambda n|) :
    False := by
  classical
  choose mode hmode_ne hmode_norm hmode_diag using
    fun n => exists_unit_eigenvector_of_hasEigenvalue (T := T) (heigen n)
  have hhas_vec :
      ∀ n, Module.End.HasEigenvector T.toLinearMap (lambda n) (mode n) := by
    intro n
    refine ⟨?_, hmode_ne n⟩
    simpa [Module.End.mem_eigenspace_iff] using hmode_diag n
  have horth : Orthonormal Real mode := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hij : i = j
    · subst j
      simp [hmode_norm i, inner_self_eq_norm_sq_to_K]
    · have hneqji : lambda j ≠ lambda i := (hdistinct hij).symm
      have hzero :
          inner Real (mode i) (mode j) = 0 :=
        selfAdjoint_eigenvectors_orthogonal_of_ne
          (T := T) hsymm hneqji (hhas_vec j) (hhas_vec i)
      simp [hij, hzero]
  exact
    compactOperator_no_orthonormal_eigen_subsequence_bounded_away
      (T := T) hcompact horth hmode_diag
      (φ := id) strictMono_id heps (by simpa using hlower)

omit [CompleteSpace H] in
/-- Any sequence of distinct eigenvalues of a compact self-adjoint operator
tends to zero.

This is another precise infinite-dimensional replacement for finite-spectrum
reasoning: one may list infinitely many distinct eigenvalues, but compactness
forces every such list to converge to `0`. -/
theorem compactSelfAdjoint_distinct_eigenvalues_tendsto_zero
    {T : H →L[Real] H}
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric)
    {lambda : Nat -> Real}
    (heigen :
      ∀ n, Module.End.HasEigenvalue T.toLinearMap (lambda n))
    (hdistinct : Pairwise fun i j => lambda i ≠ lambda j) :
    Filter.Tendsto lambda Filter.atTop (nhds 0) := by
  by_contra hnot
  obtain ⟨s, hs, hfreq⟩ :=
    (Filter.not_tendsto_iff_exists_frequently_notMem
      (f := lambda) (l₁ := Filter.atTop) (l₂ := nhds (0 : Real))).mp hnot
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hs
  have hfreq_lower : ∃ᶠ n in Filter.atTop, eps <= |lambda n| := by
    refine hfreq.mono ?_
    intro n hn
    have hnot_ball : lambda n ∉ Metric.ball (0 : Real) eps := by
      intro hmem
      exact hn (hball hmem)
    have hge : eps <= dist (lambda n) 0 := by
      exact le_of_not_gt (by simpa [Metric.mem_ball] using hnot_ball)
    simpa [dist_eq_norm] using hge
  obtain ⟨φ, hφ, hlower⟩ :=
    Filter.extraction_of_frequently_atTop hfreq_lower
  have heigen_sub :
      ∀ n, Module.End.HasEigenvalue T.toLinearMap (lambda (φ n)) := by
    intro n
    exact heigen (φ n)
  have hdistinct_sub : Pairwise fun i j => lambda (φ i) ≠ lambda (φ j) := by
    intro i j hij
    exact hdistinct (hφ.injective.ne hij)
  exact
    compactSelfAdjoint_no_distinct_eigenvalue_sequence_bounded_away
      (T := T) hcompact hsymm heigen_sub hdistinct_sub heps hlower

omit [CompleteSpace H] in
/-- For a compact self-adjoint operator, only finitely many eigenvalues can lie
outside any fixed neighborhood of zero.

This is the set-level compact spectral finiteness statement used before
enumerating the nonzero spectrum by shells. -/
theorem compactSelfAdjoint_finite_eigenvalues_abs_ge
    {T : H →L[Real] H}
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric)
    {eps : Real} (heps : 0 < eps) :
    {lambda : Real |
      Module.End.HasEigenvalue T.toLinearMap lambda ∧ eps <= |lambda|}.Finite := by
  classical
  let s : Set Real :=
    {lambda : Real |
      Module.End.HasEigenvalue T.toLinearMap lambda ∧ eps <= |lambda|}
  by_contra hfinite
  have hfinite' : ¬s.Finite := by
    intro hs
    exact hfinite (by simpa [s] using hs)
  have hinf : s.Infinite := by
    exact hfinite'
  let e : Nat ↪ s := Set.Infinite.natEmbedding s hinf
  let lambdaSeq : Nat → Real := fun n => (e n : Real)
  have heigen :
      ∀ n, Module.End.HasEigenvalue T.toLinearMap (lambdaSeq n) := by
    intro n
    exact (e n).property.1
  have hdistinct : Pairwise fun i j => lambdaSeq i ≠ lambdaSeq j := by
    intro i j hij heq
    exact hij (e.injective (Subtype.ext heq))
  have hlower : ∀ n, eps <= |lambdaSeq n| := by
    intro n
    exact (e n).property.2
  exact
    compactSelfAdjoint_no_distinct_eigenvalue_sequence_bounded_away
      (T := T) hcompact hsymm heigen hdistinct heps hlower

omit [CompleteSpace H] in
/-- The nonzero eigenvalue set of a compact self-adjoint operator is
countable.

This is the graphon-safe replacement for a finite-spectrum assertion: compact
self-adjoint operators may have infinitely many nonzero eigenvalues, but by
the finite-away-from-zero theorem they are a countable union of finite shells
and can accumulate only at `0`. -/
theorem compactSelfAdjoint_countable_nonzero_eigenvalues
    {T : H →L[Real] H}
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    {lambda : Real |
      Module.End.HasEigenvalue T.toLinearMap lambda ∧ lambda ≠ 0}.Countable := by
  classical
  let shell : Nat -> Set Real := fun n =>
    {lambda : Real |
      Module.End.HasEigenvalue T.toLinearMap lambda ∧
        1 / ((n : Real) + 1) <= |lambda|}
  have hshell : ∀ n, (shell n).Countable := by
    intro n
    exact (compactSelfAdjoint_finite_eigenvalues_abs_ge
      (T := T) hcompact hsymm
      (eps := 1 / ((n : Real) + 1)) (by positivity)).countable
  have hUnion : (⋃ n : Nat, shell n).Countable :=
    Set.countable_iUnion hshell
  refine Set.Countable.mono ?_ hUnion
  intro lambda hlambda
  have habs_pos : 0 < |lambda| := abs_pos.mpr hlambda.2
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt habs_pos
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  exact ⟨hlambda.1, le_of_lt hn⟩

omit [CompleteSpace H] in
/-- A compact self-adjoint operator admits a sequence that enumerates its
nonzero eigenvalues, with zero padding allowed.

The two clauses say exactly that every nonzero eigenvalue appears somewhere in
the sequence, and every nonzero sequence entry is a genuine eigenvalue.  The
sequence may repeat values and may contain zeros; this is intentional, since a
compact operator may have no nonzero eigenvalues or infinitely many accumulating
at zero. -/
theorem compactSelfAdjoint_exists_nonzero_eigenvalue_sequence
    {T : H →L[Real] H}
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    ∃ eigen : Nat -> Real,
      (∀ lambda : Real,
        Module.End.HasEigenvalue T.toLinearMap lambda ->
        lambda ≠ 0 ->
        ∃ n : Nat, eigen n = lambda) ∧
      (∀ n : Nat,
        eigen n ≠ 0 ->
        Module.End.HasEigenvalue T.toLinearMap (eigen n)) := by
  classical
  let s : Set Real :=
    {lambda : Real |
      Module.End.HasEigenvalue T.toLinearMap lambda ∧ lambda ≠ 0}
  have hs : s.Countable :=
    compactSelfAdjoint_countable_nonzero_eigenvalues
      (T := T) hcompact hsymm
  let eigen : Nat -> Real := Set.enumerateCountable hs 0
  refine ⟨eigen, ?_, ?_⟩
  · intro lambda hlambda hne
    have hmem : lambda ∈ s := ⟨hlambda, hne⟩
    exact Set.subset_range_enumerate hs 0 hmem
  · intro n hne
    have hrange : eigen n ∈ Set.range eigen := ⟨n, rfl⟩
    have hmem_insert :
        eigen n ∈ insert 0 s :=
      Set.range_enumerateCountable_subset hs 0 hrange
    rcases hmem_insert with hzero | hs_mem
    · exact False.elim (hne hzero)
    · exact hs_mem.1

end Real

set_option linter.unusedSectionVars false in
/-- A continuous linear map whose range is contained in a finite-dimensional
subspace is compact.

This is the exact finite-rank/range compactness input used by Hilbert-space
kernel arguments.  It does not assert that a graphon operator has finitely many
nonzero eigenvalues; it only supplies compactness for genuinely finite-range
approximants. -/
theorem isCompactOperator_of_range_le_finiteDimensional
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {T : ContinuousLinearMap (RingHom.id 𝕜) E F} {V : Submodule 𝕜 F}
    [FiniteDimensional 𝕜 V]
    (hV : forall x, (V : Set F) (T x)) :
    IsCompactOperator T := by
  let TV : ContinuousLinearMap (RingHom.id 𝕜) E V :=
    { T.toLinearMap.codRestrict V hV with
      cont := T.continuous.subtype_mk hV }
  haveI := FiniteDimensional.proper_rclike 𝕜 V
  have hTV : IsCompactOperator TV :=
    isCompactOperator_of_locallyCompactSpace_dom TV
  cases hTV with
  | intro C hC =>
      refine Exists.intro (V.subtypeL '' C) ?_
      refine And.intro (hC.1.image V.subtypeL.continuous) ?_
      filter_upwards [hC.2] with x hx
      exact Exists.intro (TV x) (And.intro hx rfl)

set_option linter.unusedSectionVars false in
/-- An operator-norm limit of finite-dimensional-range continuous linear maps is
compact.

This is the standard compactness bridge for Hilbert-Schmidt-style graphon
operators: first prove compactness of exact finite-range approximants, then
pass to the norm limit using the closedness of compact operators. -/
theorem isCompactOperator_of_tendsto_finiteDimensional_range
    {I F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [CompleteSpace F]
    {l : Filter I} [l.NeBot]
    {Tn : I -> ContinuousLinearMap (RingHom.id 𝕜) E F}
    {T : ContinuousLinearMap (RingHom.id 𝕜) E F}
    (hT : Filter.Tendsto Tn l (nhds T))
    (Vn : I -> Submodule 𝕜 F)
    [hVnFinite : forall i, FiniteDimensional 𝕜 (Vn i)]
    (hVn : forall i x, (Vn i : Set F) (Tn i x)) :
    IsCompactOperator T := by
  refine isCompactOperator_of_tendsto hT ?_
  refine Filter.Eventually.of_forall ?_
  intro i
  haveI := hVnFinite i
  exact isCompactOperator_of_range_le_finiteDimensional
    (T := Tn i) (V := Vn i) (hVn i)

section Graphon

universe u

variable {Omega : Type u} [MeasurableSpace Omega] {mu : Measure Omega}
variable [IsProbabilityMeasure mu] {W : Omega -> Omega -> Real}

/-- A bounded-kernel `L²` operator is compact once its range is known to lie in
a finite-dimensional subspace.

This is the graphon-facing finite-rank step: it applies only to exact
finite-dimensional-range approximants, and makes no claim that a graphon
operator itself has finite spectrum or finite-dimensional range. -/
theorem boundedKernelCompact_of_range_le_finiteDimensional
    {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    {V : Submodule Real (Lp Real 2 mu)}
    [FiniteDimensional Real V]
    (hV : forall f : Lp Real 2 mu,
      (V : Set (Lp Real 2 mu))
        (L2Kernel.kernelOpGoodKCLM (mu := mu) hK hC0 hKC f)) :
    IsCompactOperator (L2Kernel.kernelOpGoodKCLM (mu := mu) hK hC0 hKC) :=
  isCompactOperator_of_range_le_finiteDimensional
    (T := L2Kernel.kernelOpGoodKCLM (mu := mu) hK hC0 hKC)
    (V := V) hV

set_option linter.unusedSectionVars false in
/-- The simple-function part of a finite separable kernel has finite-dimensional
range.  If `K x y = sum_i a_i x * b_i y`, then applying `K` to a simple
function gives a linear combination of the finitely many `a_i` vectors. -/
theorem kernelOpGoodKSimple_mem_span_of_finiteRank
    {ι : Type*} [Fintype ι]
    {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {a b : ι -> Omega -> Real}
    (ha : forall i, Good (a i)) (hb : forall i, Good (b i))
    (hsep : forall x y, K x y = ∑ i : ι, a i x * b i y)
    (s : Lp.simpleFunc Real 2 mu) :
    L2Kernel.kernelOpGoodKSimple (mu := mu) hK s ∈
      Submodule.span Real
        (Set.range fun i : ι => L2Kernel.goodL2 (mu := mu) (ha i)) := by
  classical
  let sf : Omega -> Real := Lp.simpleFunc.toSimpleFunc s
  let hs : Good sf := L2Kernel.simpleFunc_good (mu := mu) s
  let coeff : ι -> Real := fun i => ∫ y, b i y * sf y ∂mu
  let V : Submodule Real (Lp Real 2 mu) :=
    Submodule.span Real
      (Set.range fun i : ι => L2Kernel.goodL2 (mu := mu) (ha i))
  let v : Lp Real 2 mu :=
    ∑ i : ι, coeff i • L2Kernel.goodL2 (mu := mu) (ha i)
  have hv : v ∈ V := by
    dsimp [v, V]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem _ (coeff i)
      (Submodule.subset_span (Set.mem_range_self i))
  have hterm_int :
      forall (x : Omega) (i : ι),
        Integrable (fun y => (a i x * b i y) * sf y) mu := by
    intro x i
    have hi : Integrable (fun y => b i y * sf y) mu :=
      (Good.mul (hb i) hs).integrable
    simpa [mul_assoc] using hi.const_mul (a i x)
  have hpoint : forall x : Omega,
      kernelOp K mu sf x = ∑ i : ι, coeff i * a i x := by
    intro x
    calc
      kernelOp K mu sf x
          = ∫ y, (∑ i : ι, a i x * b i y) * sf y ∂mu := by
            simp only [kernelOp]
            refine integral_congr_ae (ae_of_all _ fun y => ?_)
            simp [hsep x y]
      _ = ∫ y, ∑ i : ι, (a i x * b i y) * sf y ∂mu := by
            refine integral_congr_ae (ae_of_all _ fun y => ?_)
            simp [Finset.sum_mul]
      _ = ∑ i : ι, ∫ y, (a i x * b i y) * sf y ∂mu := by
            rw [integral_finsetSum]
            intro i _hi
            exact hterm_int x i
      _ = ∑ i : ι, a i x * coeff i := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simp only [coeff]
            rw [← integral_const_mul]
            refine integral_congr_ae (ae_of_all _ fun y => ?_)
            ring
      _ = ∑ i : ι, coeff i * a i x := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            ring
  have hright : (v : Omega -> Real) =ᵐ[mu]
      fun x => ∑ i : ι, coeff i * a i x := by
    have hsum :=
      Lp.coeFn_fun_finsetSum (μ := mu) (p := (2 : ENNReal))
        (Finset.univ) (fun i : ι =>
          coeff i • L2Kernel.goodL2 (mu := mu) (ha i))
    have hterms : forall i : ι,
        ((coeff i • L2Kernel.goodL2 (mu := mu) (ha i) :
            Lp Real 2 mu) : Omega -> Real) =ᵐ[mu]
          fun x => coeff i * a i x := by
      intro i
      filter_upwards
        [Lp.coeFn_smul (μ := mu) (p := (2 : ENNReal))
         (coeff i) (L2Kernel.goodL2 (mu := mu) (ha i)),
         L2Kernel.goodL2_ae_eq (mu := mu) (ha i)] with x hxsmul hxae
      rw [hxsmul]
      simp [Pi.smul_apply, smul_eq_mul, hxae]
    have hall : (∀ᵐ x ∂mu, forall i : ι,
        ((coeff i • L2Kernel.goodL2 (mu := mu) (ha i) :
            Lp Real 2 mu) : Omega -> Real) x = coeff i * a i x) := by
      rw [Filter.eventually_all]
      exact hterms
    filter_upwards [hsum, hall] with x hxsum hxterms
    rw [hxsum]
    exact Finset.sum_congr rfl (fun i _hi => hxterms i)
  have hop : L2Kernel.kernelOpGoodKSimple (mu := mu) hK s = v := by
    apply Lp.ext
    change
      ((L2Kernel.kernelOpL2OfGoodK (mu := mu) hK hs : Lp Real 2 mu) :
          Omega -> Real) =ᵐ[mu] (v : Omega -> Real)
    filter_upwards
      [L2Kernel.kernelOpL2OfGoodK_ae_eq (mu := mu) hK hs,
       hright] with x hxop hxv
    rw [hxop, hxv, hpoint x]
  rw [hop]
  exact hv

set_option linter.unusedSectionVars false in
/-- The full bounded-kernel operator of an exact finite separable kernel has
range in the finite span of the left factors. -/
theorem kernelOpGoodKCLM_mem_span_of_finiteRank
    {ι : Type*} [Fintype ι]
    {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    {a b : ι -> Omega -> Real}
    (ha : forall i, Good (a i)) (hb : forall i, Good (b i))
    (hsep : forall x y, K x y = ∑ i : ι, a i x * b i y)
    (f : Lp Real 2 mu) :
    L2Kernel.kernelOpGoodKCLM (mu := mu) hK hC0 hKC f ∈
      Submodule.span Real
        (Set.range fun i : ι => L2Kernel.goodL2 (mu := mu) (ha i)) := by
  classical
  let V : Submodule Real (Lp Real 2 mu) :=
    Submodule.span Real
      (Set.range fun i : ι => L2Kernel.goodL2 (mu := mu) (ha i))
  haveI : FiniteDimensional Real V :=
    FiniteDimensional.span_of_finite Real (Set.finite_range _)
  change
    L2Kernel.kernelOpGoodKCLM (mu := mu) hK hC0 hKC f ∈ V
  let T := L2Kernel.kernelOpGoodKCLM (mu := mu) hK hC0 hKC
  let e := L2Kernel.simpleFuncToL2 (mu := mu)
  have hdense : DenseRange e :=
    Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
      (by norm_num)
  refine hdense.induction_on
    (p := fun f : Lp Real 2 mu => (V : Set (Lp Real 2 mu)) (T f))
    f ?closed ?simple
  · have hclosedV : IsClosed (V : Set (Lp Real 2 mu)) :=
      V.closed_of_finiteDimensional
    change IsClosed {f : Lp Real 2 mu | T f ∈ V}
    simpa [Set.preimage, T] using hclosedV.preimage
      (L2Kernel.kernelOpGoodKCLM (mu := mu) hK hC0 hKC).continuous
  · intro s
    change
      L2Kernel.kernelOpGoodKCLM (mu := mu) hK hC0 hKC
          (s : Lp Real 2 mu) ∈ V
    rw [L2Kernel.kernelOpGoodKCLM_simpleFunc (mu := mu) hK hC0 hKC s]
    exact kernelOpGoodKSimple_mem_span_of_finiteRank
      (mu := mu) hK ha hb hsep s

set_option linter.unusedSectionVars false in
/-- Exact finite separable kernels define compact `L²` operators.

This is the graphon-facing finite-rank step: compactness comes from the
operator range lying in the finite span of the left factors `a_i`, not from any
finite-spectrum assertion about a limiting graphon operator. -/
theorem boundedKernelCompact_of_finiteRank
    {ι : Type*} [Fintype ι]
    {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    {a b : ι -> Omega -> Real}
    (ha : forall i, Good (a i)) (hb : forall i, Good (b i))
    (hsep : forall x y, K x y = ∑ i : ι, a i x * b i y) :
    IsCompactOperator (L2Kernel.kernelOpGoodKCLM (mu := mu) hK hC0 hKC) := by
  classical
  let V : Submodule Real (Lp Real 2 mu) :=
    Submodule.span Real
      (Set.range fun i : ι => L2Kernel.goodL2 (mu := mu) (ha i))
  haveI : FiniteDimensional Real V :=
    FiniteDimensional.span_of_finite Real (Set.finite_range _)
  refine boundedKernelCompact_of_range_le_finiteDimensional
    (mu := mu) hK hC0 hKC (V := V) ?_
  exact kernelOpGoodKCLM_mem_span_of_finiteRank
    (mu := mu) hK hC0 hKC ha hb hsep

set_option linter.unusedSectionVars false in
/-- Compactness of the canonical graphon operator from finite-dimensional-range
bounded-kernel approximants converging uniformly to the graphon kernel.

This is an operator-norm compactness bridge.  It is intentionally stated with
an explicit uniform error `eps i`, not as a finite-spectrum claim: each
approximant may have finite-dimensional range, and the graphon operator is
compact because it is their operator-norm limit. -/
theorem canonicalGraphonCompact_of_uniform_finiteDimensional_approx
    {I : Type*} {l : Filter I} [l.NeBot]
    (hW : IsGraphon W mu)
    (K : I -> Omega -> Omega -> Real)
    (B eps : I -> Real)
    (hK : forall i, GoodK (K i))
    (hB0 : forall i, 0 <= B i)
    (hKB : forall i x y, |K i x y| <= B i)
    (heps0 : forall i, 0 <= eps i)
    (happrox : forall i x y, |K i x y - W x y| <= eps i)
    (heps_tendsto : Filter.Tendsto eps l (nhds 0))
    (V : I -> Submodule Real (Lp Real 2 mu))
    [hVFinite : forall i, FiniteDimensional Real (V i)]
    (hV : forall i f,
      (V i : Set (Lp Real 2 mu))
        (L2Kernel.kernelOpGoodKCLM (mu := mu)
          (hK i) (hB0 i) (hKB i) f)) :
    IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW) := by
  have hTendsto :
      Filter.Tendsto
        (fun i =>
          L2Kernel.kernelOpGoodKCLM (mu := mu)
            (hK i) (hB0 i) (hKB i))
        l
        (nhds (L2Kernel.kernelOpCLM (mu := mu) hW)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun i => norm_nonneg _) ?_ heps_tendsto
    intro i
    calc
      ‖L2Kernel.kernelOpGoodKCLM (mu := mu)
          (hK i) (hB0 i) (hKB i) -
          L2Kernel.kernelOpCLM (mu := mu) hW‖
          =
        ‖L2Kernel.kernelOpGoodKCLM (mu := mu)
            (hK i) (hB0 i) (hKB i) -
            L2Kernel.kernelOpGoodKCLM (mu := mu)
              (goodK_of_isGraphon hW)
              zero_le_one (L2Kernel.graphon_abs_le_one (mu := mu) hW)‖ := by
            rw [L2Kernel.kernelOpCLM_eq_kernelOpGoodKCLM (mu := mu) hW]
      _ <= eps i := by
            exact L2Kernel.norm_kernelOpGoodKCLM_sub_le
              (mu := mu)
              (hK i) (goodK_of_isGraphon hW)
              (hB0 i) (hKB i)
              zero_le_one (L2Kernel.graphon_abs_le_one (mu := mu) hW)
              (heps0 i) (happrox i)
  exact isCompactOperator_of_tendsto_finiteDimensional_range
    (hT := hTendsto) V hV

set_option linter.unusedSectionVars false in
/-- Compactness of the canonical graphon operator from finite-dimensional-range
bounded-kernel approximants converging in Hilbert-Schmidt kernel mass.

This is the graphon-compatible compactness bridge: the approximants may have
finite-dimensional range, but the exact graphon operator is obtained as an
operator-norm limit controlled by the `L²(Ω × Ω)` mass of the kernel
difference.  No finite-spectrum assertion is made. -/
theorem canonicalGraphonCompact_of_hilbertSchmidt_finiteDimensional_approx
    {I : Type*} {l : Filter I} [l.NeBot]
    (hW : IsGraphon W mu)
    (K : I -> Omega -> Omega -> Real)
    (B : I -> Real)
    (hK : forall i, GoodK (K i))
    (hB0 : forall i, 0 <= B i)
    (hKB : forall i x y, |K i x y| <= B i)
    (hsqrt_tendsto :
      Filter.Tendsto
        (fun i =>
          Real.sqrt
            (L2Kernel.kernelSqNorm mu
              (fun x y => K i x y - W x y)))
        l (nhds 0))
    (V : I -> Submodule Real (Lp Real 2 mu))
    [hVFinite : forall i, FiniteDimensional Real (V i)]
    (hV : forall i f,
      (V i : Set (Lp Real 2 mu))
        (L2Kernel.kernelOpGoodKCLM (mu := mu)
          (hK i) (hB0 i) (hKB i) f)) :
    IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW) := by
  have hTendsto :
      Filter.Tendsto
        (fun i =>
          L2Kernel.kernelOpGoodKCLM (mu := mu)
            (hK i) (hB0 i) (hKB i))
        l
        (nhds (L2Kernel.kernelOpCLM (mu := mu) hW)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun i => norm_nonneg _) ?_ hsqrt_tendsto
    intro i
    have hSub0 : 0 <= B i + 1 := add_nonneg (hB0 i) zero_le_one
    have hSub : forall x y, |K i x y - W x y| <= B i + 1 := by
      intro x y
      calc
        |K i x y - W x y| <= |K i x y| + |W x y| := abs_sub _ _
        _ <= B i + 1 := by
              exact add_le_add (hKB i x y)
                (L2Kernel.graphon_abs_le_one (mu := mu) hW x y)
    calc
      ‖L2Kernel.kernelOpGoodKCLM (mu := mu)
          (hK i) (hB0 i) (hKB i) -
          L2Kernel.kernelOpCLM (mu := mu) hW‖
          =
        ‖L2Kernel.kernelOpGoodKCLM (mu := mu)
            (hK i) (hB0 i) (hKB i) -
            L2Kernel.kernelOpGoodKCLM (mu := mu)
              (goodK_of_isGraphon hW)
              zero_le_one (L2Kernel.graphon_abs_le_one (mu := mu) hW)‖ := by
            rw [L2Kernel.kernelOpCLM_eq_kernelOpGoodKCLM (mu := mu) hW]
      _ <=
          Real.sqrt
            (L2Kernel.kernelSqNorm mu
              (fun x y => K i x y - W x y)) := by
            exact L2Kernel.norm_kernelOpGoodKCLM_sub_le_sqrt_kernelSqNorm
              (mu := mu)
              (hK i) (goodK_of_isGraphon hW)
              (hB0 i) (hKB i)
              zero_le_one (L2Kernel.graphon_abs_le_one (mu := mu) hW)
              hSub0 hSub
  exact isCompactOperator_of_tendsto_finiteDimensional_range
    (hT := hTendsto) V hV

set_option linter.unusedSectionVars false in
/-- Compactness of the canonical graphon operator from Hilbert-Schmidt
convergence of exact finite-rank kernel approximants.

The finite ranks may depend on the approximation index.  This packages the
honest finite-rank range proof with the Hilbert-Schmidt operator-norm bridge,
so no graphon-facing theorem needs to assume that the graphon operator itself
has finitely many nonzero eigenvalues. -/
theorem canonicalGraphonCompact_of_hilbertSchmidt_finiteRank_approx
    {I : Type*} {l : Filter I} [l.NeBot]
    (hW : IsGraphon W mu)
    (κ : I -> Type*) [hκ : forall i, Fintype (κ i)]
    (K : I -> Omega -> Omega -> Real)
    (B : I -> Real)
    (hK : forall i, GoodK (K i))
    (hB0 : forall i, 0 <= B i)
    (hKB : forall i x y, |K i x y| <= B i)
    (a b : forall i, κ i -> Omega -> Real)
    (ha : forall i j, Good (a i j))
    (hb : forall i j, Good (b i j))
    (hsep : forall i x y, K i x y = ∑ j : κ i, a i j x * b i j y)
    (hsqrt_tendsto :
      Filter.Tendsto
        (fun i =>
          Real.sqrt
            (L2Kernel.kernelSqNorm mu
              (fun x y => K i x y - W x y)))
        l (nhds 0)) :
    IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW) := by
  classical
  let V : I -> Submodule Real (Lp Real 2 mu) := fun i =>
    Submodule.span Real
      (Set.range fun j : κ i => L2Kernel.goodL2 (mu := mu) (ha i j))
  haveI : forall i, FiniteDimensional Real (V i) := by
    intro i
    dsimp [V]
    exact FiniteDimensional.span_of_finite Real (Set.finite_range _)
  refine canonicalGraphonCompact_of_hilbertSchmidt_finiteDimensional_approx
    (mu := mu) hW K B hK hB0 hKB hsqrt_tendsto V ?_
  intro i f
  dsimp [V]
  exact kernelOpGoodKCLM_mem_span_of_finiteRank
    (mu := mu) (ι := κ i)
    (hK i) (hB0 i) (hKB i)
    (ha i) (hb i) (hsep i) f

/-- Finite-rank Hilbert-Schmidt approximation data for one graphon kernel.

This is the remaining standard measure-theoretic approximation statement in a
fixed-graphon form: the graphon kernel is an `L²(mu × mu)` limit of bounded
finite separable kernels. -/
def GraphonHilbertSchmidtFiniteRankApproxFor
    (_hW : IsGraphon W mu) : Prop :=
  exists (I : Type u) (l : Filter I),
    Filter.NeBot l /\
    exists (J : I -> Type u) (hJ : forall i, Fintype (J i))
      (K : I -> Omega -> Omega -> Real) (B : I -> Real)
      (a b : forall i, J i -> Omega -> Real),
      (forall i, GoodK (K i)) /\
      (forall i, 0 <= B i) /\
      (forall i x y, |K i x y| <= B i) /\
      (forall i j, Good (a i j)) /\
      (forall i j, Good (b i j)) /\
      (forall i x y,
        K i x y = (@Finset.univ (J i) (hJ i)).sum
          (fun j : J i => a i j x * b i j y)) /\
      Filter.Tendsto
        (fun i =>
          Real.sqrt
            (L2Kernel.kernelSqNorm mu
              (fun x y => K i x y - W x y)))
        l (nhds 0)

/-- Every graphon kernel admits bounded exact finite-rank Hilbert-Schmidt
approximants.

This is the graphon compactness input proved from the concrete measure
approximation layer: simple functions are dense in `L²(mu × mu)`, and each
simple-function atom can be approximated by a finite union of measurable
rectangles, hence by a finite separable kernel. -/
theorem graphonHilbertSchmidtFiniteRankApproxFor
    (hW : IsGraphon W mu) :
    GraphonHilbertSchmidtFiniteRankApproxFor (mu := mu) hW := by
  classical
  let eps : Nat -> Real := fun n => (1 : Real) / (n + 1)
  have heps : forall n, 0 < eps n := by
    intro n
    dsimp [eps]
    positivity
  have hex :
      forall n : Nat,
        exists J : Type u, exists hJ : Fintype J,
        exists K : Omega -> Omega -> Real, exists B : Real,
        exists a b : J -> Omega -> Real,
          GoodK K /\
          0 <= B /\
          (forall x y, |K x y| <= B) /\
          (forall j, Good (a j)) /\
          (forall j, Good (b j)) /\
          (forall x y, K x y = (@Finset.univ J hJ).sum
            (fun j : J => a j x * b j y)) /\
          Real.sqrt (L2Kernel.kernelSqNorm mu
            (fun x y => K x y - W x y)) < eps n := by
    intro n
    exact L2Kernel.exists_finiteRank_kernel_sqrt_kernelSqNorm_sub_lt_of_goodK
      (mu := mu) (goodK_of_isGraphon hW) (heps n)
  choose J hJ K B a b hK hB0 hKB ha hb hsep hsqrt_lt using hex
  let I : Type u := ULift.{u} Nat
  let up : Nat -> I := fun n => ULift.up n
  let l : Filter I := Filter.map up Filter.atTop
  refine ⟨I, l, ?_, (fun i : I => J i.down), (fun i : I => hJ i.down),
    (fun i : I => K i.down), (fun i : I => B i.down),
    (fun i : I => a i.down), (fun i : I => b i.down),
    (fun i : I => hK i.down), (fun i : I => hB0 i.down),
    (fun i : I => hKB i.down), (fun i : I => ha i.down),
    (fun i : I => hb i.down), (fun i : I => hsep i.down), ?_⟩
  · dsimp [l]
    exact Filter.NeBot.map inferInstance up
  · have hNat :
        Filter.Tendsto
          (fun n : Nat =>
            Real.sqrt
              (L2Kernel.kernelSqNorm mu
                (fun x y => K n x y - W x y)))
          Filter.atTop (nhds 0) := by
      refine squeeze_zero
        (f := fun n : Nat =>
          Real.sqrt
            (L2Kernel.kernelSqNorm mu
              (fun x y => K n x y - W x y)))
        (g := eps)
        (fun n => Real.sqrt_nonneg _) ?_ ?_
      · intro n
        exact (hsqrt_lt n).le
      · simpa [eps] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    dsimp [l]
    rw [Filter.tendsto_map'_iff]
    simpa [Function.comp_def, up]
      using hNat

/-- Finite-rank Hilbert-Schmidt approximation data imply compactness of the
canonical graphon operator. -/
theorem canonicalGraphonCompact_of_hilbertSchmidtFiniteRankApproxFor
    (hW : IsGraphon W mu)
    (happrox : GraphonHilbertSchmidtFiniteRankApproxFor (mu := mu) hW) :
    IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW) := by
  rcases happrox with
    ⟨I, l, hl, J, hJ, K, B, a, b,
      hK, hB0, hKB, ha, hb, hsep, hsqrt_tendsto⟩
  letI : Filter.NeBot l := hl
  letI : forall i, Fintype (J i) := hJ
  exact
    canonicalGraphonCompact_of_hilbertSchmidt_finiteRank_approx
      (mu := mu) hW J K B hK hB0 hKB a b ha hb hsep hsqrt_tendsto

set_option linter.unusedSectionVars false in
/-- The compact self-adjoint spectral skeleton obtained directly from
Hilbert-Schmidt convergence of exact finite-rank kernel approximants. -/
theorem canonicalGraphonCompactSelfAdjointSkeleton_of_hilbertSchmidt_finiteRank_approx
    {I : Type*} {l : Filter I} [l.NeBot]
    (hW : IsGraphon W mu)
    (κ : I -> Type*) [hκ : forall i, Fintype (κ i)]
    (K : I -> Omega -> Omega -> Real)
    (B : I -> Real)
    (hK : forall i, GoodK (K i))
    (hB0 : forall i, 0 <= B i)
    (hKB : forall i x y, |K i x y| <= B i)
    (a b : forall i, κ i -> Omega -> Real)
    (ha : forall i j, Good (a i j))
    (hb : forall i j, Good (b i j))
    (hsep : forall i x y, K i x y = ∑ j : κ i, a i j x * b i j y)
    (hsqrt_tendsto :
      Filter.Tendsto
        (fun i =>
          Real.sqrt
            (L2Kernel.kernelSqNorm mu
              (fun x y => K i x y - W x y)))
        l (nhds 0)) :
    CompactSelfAdjointSkeleton (L2Kernel.kernelOpCLM (mu := mu) hW) := by
  exact compactSelfAdjointSkeleton
    (canonicalGraphonCompact_of_hilbertSchmidt_finiteRank_approx
      (mu := mu) hW κ K B hK hB0 hKB a b ha hb hsep hsqrt_tendsto)
    (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW)

/-- Compactness of the canonical `L²` graphon operator is enough to put it
under Mathlib's compact self-adjoint spectral theorem.

This theorem does not assert finite spectrum.  It gives the standard compact
self-adjoint skeleton for the exact graphon operator `L2Kernel.kernelOpCLM hW`:
the eigenspaces span densely/orthogonally and each nonzero eigenspace is
finite-dimensional.  The remaining C9-specific work is still the trace/Lidskii
bridge turning this skeleton into the required countable trace identities. -/
theorem canonicalGraphonCompactSelfAdjointSkeleton
    (hW : IsGraphon W mu)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW)) :
    CompactSelfAdjointSkeleton (L2Kernel.kernelOpCLM (mu := mu) hW) :=
  compactSelfAdjointSkeleton hcompact
    (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW)

/-- The eigenspaces of the compact canonical graphon operator are mutually
orthogonal.  This is a graphon specialization of self-adjoint Hilbert-space
orthogonality, not a finite-spectrum statement. -/
theorem canonicalGraphonCompact_orthogonalFamily_eigenspaces
    (hW : IsGraphon W mu)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW)) :
    OrthogonalFamily Real
      (fun lambda =>
        eigenspace
          (L2Kernel.kernelOpCLM (mu := mu) hW : End Real (Lp Real 2 mu))
          lambda)
      (fun lambda =>
        (eigenspace
          (L2Kernel.kernelOpCLM (mu := mu) hW : End Real (Lp Real 2 mu))
          lambda).subtypeₗᵢ) :=
  compactSelfAdjoint_orthogonalFamily_eigenspaces hcompact
    (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW)

/-- Eigenvectors of the canonical graphon operator with distinct eigenvalues
are orthogonal. -/
theorem canonicalGraphonCompact_eigenvectors_orthogonal_of_ne
    (hW : IsGraphon W mu)
    {lambda nu : Real} (hneq : lambda ≠ nu)
    {v w : Lp Real 2 mu}
    (hv :
      Module.End.HasEigenvector
        (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap lambda v)
    (hw :
      Module.End.HasEigenvector
        (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap nu w) :
    inner Real w v = 0 :=
  selfAdjoint_eigenvectors_orthogonal_of_ne
    (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW)
    hneq hv hw

/-- The range of the canonical graphon operator is orthogonal to its zero
eigenspace.  This is the graphon specialization of the elementary symmetric
operator identity `range T ≤ (ker T)ᗮ`. -/
theorem canonicalGraphon_range_le_orthogonal_zero_eigenspace
    (hW : IsGraphon W mu) :
    LinearMap.range (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap ≤
      (eigenspace
        (L2Kernel.kernelOpCLM (mu := mu) hW :
          End Real (Lp Real 2 mu))
        0)ᗮ :=
  symmetric_range_le_orthogonal_zero_eigenspace
    (T := L2Kernel.kernelOpCLM (mu := mu) hW)
    (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW)

/-- Pointwise membership form of
`canonicalGraphon_range_le_orthogonal_zero_eigenspace`. -/
theorem canonicalGraphon_apply_mem_orthogonal_zero_eigenspace
    (hW : IsGraphon W mu)
    (f : Lp Real 2 mu) :
    (L2Kernel.kernelOpCLM (mu := mu) hW) f ∈
      (eigenspace
        (L2Kernel.kernelOpCLM (mu := mu) hW :
          End Real (Lp Real 2 mu))
        0)ᗮ := by
  exact canonicalGraphon_range_le_orthogonal_zero_eigenspace
    (mu := mu) hW ⟨f, rfl⟩

/-- The constant-one Rayleigh quotient of the canonical graphon operator is
the edge density. -/
theorem canonicalGraphon_rayleigh_oneL2_eq_edgeDensity
    (hW : IsGraphon W mu) :
    (L2Kernel.kernelOpCLM (mu := mu) hW).rayleighQuotient
        (L2Kernel.oneL2 (Omega := Omega) mu) =
      edgeDensity W mu := by
  have hnum :
      (L2Kernel.kernelOpCLM (mu := mu) hW).reApplyInnerSelf
          (L2Kernel.oneL2 (Omega := Omega) mu) =
        edgeDensity W mu := by
    rw [ContinuousLinearMap.reApplyInnerSelf_apply,
      L2Kernel.kernelOpCLM_one_eq_degreeL2 hW]
    simpa [real_inner_comm] using
      L2Kernel.inner_oneL2_degreeL2_eq_edgeDensity hW
  rw [ContinuousLinearMap.rayleighQuotient, hnum,
    L2Kernel.norm_oneL2_sq]
  ring

/-- The graphon edge density is bounded by the operator norm of the canonical
`L²` graphon operator.

This is the Rayleigh-quotient estimate at the constant-one vector.  It is the
principal-bound input needed when the spectral enumeration chooses index `0`
to be a positive top/Rayleigh mode. -/
theorem canonicalGraphon_edgeDensity_le_opNorm
    (hW : IsGraphon W mu) :
    edgeDensity W mu <= ‖L2Kernel.kernelOpCLM (mu := mu) hW‖ := by
  have h :=
    (L2Kernel.kernelOpCLM (mu := mu) hW).rayleighQuotient_le_norm
      (L2Kernel.oneL2 (Omega := Omega) mu)
  rw [canonicalGraphon_rayleigh_oneL2_eq_edgeDensity (mu := mu) hW] at h
  have hp0 : 0 <= edgeDensity W mu :=
    integral_nonneg fun x => integral_nonneg fun y => hW.nonneg x y
  simpa [abs_of_nonneg hp0] using h

/-- For a compact canonical graphon operator, the nonzero eigenspaces are
dense inside the orthogonal complement of the zero eigenspace.

This is the graphon-facing dense-span statement needed to construct the
Hilbert basis of nonzero eigenvectors used by the C9 spectral package. -/
theorem canonicalGraphonCompact_nonzero_iSup_orthogonal_inf_zero_eigenspace_orthogonal_eq_bot
    (hW : IsGraphon W mu)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW)) :
    ((⨆ lambda : {lambda : Real // lambda ≠ 0},
        eigenspace
          (L2Kernel.kernelOpCLM (mu := mu) hW :
            End Real (Lp Real 2 mu))
          lambda.1)ᗮ ⊓
      (eigenspace
        (L2Kernel.kernelOpCLM (mu := mu) hW :
          End Real (Lp Real 2 mu))
        0)ᗮ) = ⊥ :=
  compactSelfAdjoint_nonzero_iSup_orthogonal_inf_zero_eigenspace_orthogonal_eq_bot
    (T := L2Kernel.kernelOpCLM (mu := mu) hW)
    hcompact
    (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW)

/-- Along any orthonormal sequence of eigenmodes of a compact canonical graphon
operator, the corresponding eigenvalues tend to zero.

This is the graphon-facing compactness statement: it allows infinitely many
nonzero eigenvalues and only rules out an infinite orthonormal subsequence
bounded away from zero. -/
theorem canonicalGraphonCompact_orthonormal_eigenvalues_tendsto_zero
    (hW : IsGraphon W mu)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW))
    {mode : Nat → Lp Real 2 mu} {eigen : Nat → Real}
    (horth : Orthonormal Real mode)
    (hdiag :
      ∀ n, L2Kernel.kernelOpCLM (mu := mu) hW (mode n) =
        eigen n • mode n) :
    Filter.Tendsto eigen Filter.atTop (nhds 0) :=
  compactOperator_orthonormal_eigenvalues_tendsto_zero
    (T := L2Kernel.kernelOpCLM (mu := mu) hW)
    hcompact horth hdiag

/-- Any sequence of distinct eigenvalues of a compact canonical graphon
operator tends to zero.

This is useful when the spectral theorem enumerates eigenvalues as values
rather than as orthonormal modes.  It still permits an infinite nonzero
spectrum; the only possible accumulation point is `0`. -/
theorem canonicalGraphonCompact_distinct_eigenvalues_tendsto_zero
    (hW : IsGraphon W mu)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW))
    {eigen : Nat -> Real}
    (heigen :
      ∀ n,
        Module.End.HasEigenvalue
          (L2Kernel.kernelOpCLM (mu := mu) hW :
            End Real (Lp Real 2 mu))
          (eigen n))
    (hdistinct : Pairwise fun i j => eigen i ≠ eigen j) :
    Filter.Tendsto eigen Filter.atTop (nhds 0) :=
  compactSelfAdjoint_distinct_eigenvalues_tendsto_zero
    (T := L2Kernel.kernelOpCLM (mu := mu) hW)
    hcompact (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW)
    heigen hdistinct

/-- For a compact canonical graphon operator, only finitely many eigenvalues
can lie outside any fixed neighborhood of zero.

This is an exact compact-operator statement about `L2Kernel.kernelOpCLM hW`;
it does not assert finite spectrum. -/
theorem canonicalGraphonCompact_finite_eigenvalues_abs_ge
    (hW : IsGraphon W mu)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW))
    {eps : Real} (heps : 0 < eps) :
    {lambda : Real |
      Module.End.HasEigenvalue
        (L2Kernel.kernelOpCLM (mu := mu) hW :
          End Real (Lp Real 2 mu))
        lambda ∧ eps <= |lambda|}.Finite :=
  compactSelfAdjoint_finite_eigenvalues_abs_ge
    (T := L2Kernel.kernelOpCLM (mu := mu) hW)
    hcompact (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW) heps

/-- The nonzero eigenvalues of a compact canonical graphon operator are
countable.

This is the graphon-facing form of the compact spectral fact we actually need:
there may be infinitely many nonzero eigenvalues, but they form a countable set
with no nonzero accumulation point. -/
theorem canonicalGraphonCompact_countable_nonzero_eigenvalues
    (hW : IsGraphon W mu)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW)) :
    {lambda : Real |
      Module.End.HasEigenvalue
        (L2Kernel.kernelOpCLM (mu := mu) hW :
          End Real (Lp Real 2 mu))
        lambda ∧ lambda ≠ 0}.Countable :=
  compactSelfAdjoint_countable_nonzero_eigenvalues
    (T := L2Kernel.kernelOpCLM (mu := mu) hW)
    hcompact (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW)

/-- A compact canonical graphon operator admits a sequence that enumerates all
nonzero eigenvalues, with zero padding allowed.

This is the exact graphon-safe enumeration statement: it does not say the
nonzero spectrum is finite, and it does not use finite-rank approximation. -/
theorem canonicalGraphonCompact_exists_nonzero_eigenvalue_sequence
    (hW : IsGraphon W mu)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW)) :
    ∃ eigen : Nat -> Real,
      (∀ lambda : Real,
        Module.End.HasEigenvalue
          (L2Kernel.kernelOpCLM (mu := mu) hW :
            End Real (Lp Real 2 mu))
          lambda ->
        lambda ≠ 0 ->
        ∃ n : Nat, eigen n = lambda) ∧
      (∀ n : Nat,
        eigen n ≠ 0 ->
        Module.End.HasEigenvalue
          (L2Kernel.kernelOpCLM (mu := mu) hW :
            End Real (Lp Real 2 mu))
          (eigen n)) :=
  compactSelfAdjoint_exists_nonzero_eigenvalue_sequence
    (T := L2Kernel.kernelOpCLM (mu := mu) hW)
    hcompact (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW)

/-- A nonzero compact canonical graphon operator has an eigenvalue at one of
the two operator-norm endpoints.

This is a direct graphon specialization of
`compactSelfAdjoint_hasEigenvalue_norm_or_neg_norm`, still without any
finite-spectrum assertion. -/
theorem canonicalGraphonCompact_hasEigenvalue_norm_or_neg_norm
    (hW : IsGraphon W mu)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW))
    (hne : L2Kernel.kernelOpCLM (mu := mu) hW ≠ 0) :
    Module.End.HasEigenvalue
        (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap
        ‖L2Kernel.kernelOpCLM (mu := mu) hW‖ ∨
      Module.End.HasEigenvalue
        (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap
        (-‖L2Kernel.kernelOpCLM (mu := mu) hW‖) :=
  compactSelfAdjoint_hasEigenvalue_norm_or_neg_norm hcompact
    (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW) hne

/-- A positive-density compact canonical graphon operator has an eigenvalue at
one of the two operator-norm endpoints. -/
theorem canonicalGraphonCompact_hasEigenvalue_norm_or_neg_norm_of_edgeDensity_pos
    (hW : IsGraphon W mu)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW))
    (hp : 0 < edgeDensity W mu) :
    Module.End.HasEigenvalue
        (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap
        ‖L2Kernel.kernelOpCLM (mu := mu) hW‖ ∨
      Module.End.HasEigenvalue
        (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap
        (-‖L2Kernel.kernelOpCLM (mu := mu) hW‖) :=
  canonicalGraphonCompact_hasEigenvalue_norm_or_neg_norm hW hcompact
    (L2Kernel.kernelOpCLM_ne_zero_of_edgeDensity_pos
      (mu := mu) hW hp)

/-- A positive-density compact canonical graphon operator has an eigenvalue at
the positive operator-norm endpoint.

The compact self-adjoint theorem first gives an endpoint eigenvalue at either
`‖T‖` or `-‖T‖`.  Positivity of the graphon kernel orients this endpoint:
if `v` is a unit eigenvector for `-‖T‖`, then the quadratic-form domination
`|⟪v, Tv⟫| ≤ ⟪|v|, T |v|⟫` makes `|v|` a maximizer of the Rayleigh numerator
on the unit sphere.  The Rayleigh extremum theorem then gives an eigenvector
with eigenvalue `‖T‖`. -/
theorem canonicalGraphonCompact_hasEigenvalue_norm_of_edgeDensity_pos
    (hW : IsGraphon W mu)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW))
    (hp : 0 < edgeDensity W mu) :
    Module.End.HasEigenvalue
        (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap
        ‖L2Kernel.kernelOpCLM (mu := mu) hW‖ := by
  let T : Lp Real 2 mu →L[Real] Lp Real 2 mu :=
    L2Kernel.kernelOpCLM (mu := mu) hW
  rcases
      canonicalGraphonCompact_hasEigenvalue_norm_or_neg_norm_of_edgeDensity_pos
        (mu := mu) hW hcompact hp with hpos | hneg
  · simpa [T] using hpos
  · obtain ⟨v, hv_ne, hv_norm, hv_eig⟩ :=
      exists_unit_eigenvector_of_hasEigenvalue (T := T) hneg
    let u : Lp Real 2 mu := |v|
    have hu_norm : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_abs_eq_norm, hv_norm]
    have hu_ne : u ≠ 0 := by
      intro hu_zero
      have : ‖u‖ = 0 := by simp [hu_zero]
      linarith
    have hinner_self : inner Real v v = 1 := by
      rw [real_inner_self_eq_norm_sq, hv_norm]
      norm_num
    have hnum_abs :
        |inner Real v (T v)| = ‖T‖ := by
      calc
        |inner Real v (T v)|
            = |inner Real v ((-‖T‖) • v)| := by rw [hv_eig]
        _ = |(-‖T‖) * inner Real v v| := by rw [inner_smul_right]
        _ = ‖T‖ := by
          rw [hinner_self]
          simp
    have hdom :
        |inner Real v (T v)| <= inner Real u (T u) := by
      simpa [T, u] using
        L2Kernel.abs_inner_kernelOpCLM_self_le_abs (mu := mu) hW v
    have hu_ge_norm : ‖T‖ <= inner Real u (T u) := by
      simpa [hnum_abs] using hdom
    have hu_ge_reApply : ‖T‖ <= T.reApplyInnerSelf u := by
      simpa [ContinuousLinearMap.reApplyInnerSelf_apply, real_inner_comm] using hu_ge_norm
    have hmax : IsMaxOn T.reApplyInnerSelf (Metric.sphere (0 : Lp Real 2 mu) ‖u‖) u := by
      intro y hy
      have hy_norm : ‖y‖ = 1 := by
        have hy_norm_u : ‖y‖ = ‖u‖ := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hy
        rw [hy_norm_u, hu_norm]
      have hy_ne : y ≠ 0 := by
        intro hy_zero
        have : ‖y‖ = 0 := by simp [hy_zero]
        linarith
      have hray_abs := T.rayleighQuotient_le_norm y
      have hray_le : T.rayleighQuotient y <= ‖T‖ :=
        (le_abs_self (T.rayleighQuotient y)).trans hray_abs
      have hy_sq : ‖y‖ ^ 2 = 1 := by
        rw [hy_norm]
        norm_num
      have hre_le_norm : T.reApplyInnerSelf y <= ‖T‖ := by
        simpa [ContinuousLinearMap.rayleighQuotient, hy_sq] using hray_le
      exact hre_le_norm.trans hu_ge_reApply
    have hevec :
        Module.End.HasEigenvector
          (T : Module.End Real (Lp Real 2 mu))
          (T.rayleighQuotient u) u :=
      (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW).isSelfAdjoint
        |>.hasEigenvector_of_isLocalExtrOn hu_ne (Or.inr hmax.localize)
    have hq_eq_norm : T.rayleighQuotient u = ‖T‖ := by
      have hray_abs := T.rayleighQuotient_le_norm u
      have hray_le : T.rayleighQuotient u <= ‖T‖ :=
        (le_abs_self (T.rayleighQuotient u)).trans hray_abs
      have hu_sq : ‖u‖ ^ 2 = 1 := by
        rw [hu_norm]
        norm_num
      have hge : ‖T‖ <= T.rayleighQuotient u := by
        simpa [ContinuousLinearMap.rayleighQuotient, hu_sq] using hu_ge_reApply
      exact le_antisymm hray_le hge
    exact Module.End.hasEigenvalue_of_hasEigenvector (by simpa [hq_eq_norm] using hevec)

/-- A positive-density compact canonical graphon operator has a
finite-dimensional eigenspace at one of the two operator-norm endpoints. -/
theorem canonicalGraphonCompact_exists_finiteDimensional_norm_endpoint_eigenspace_of_edgeDensity_pos
    (hW : IsGraphon W mu)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW))
    (hp : 0 < edgeDensity W mu) :
    Exists (fun lambda : Real =>
      (lambda = ‖L2Kernel.kernelOpCLM (mu := mu) hW‖ ∨
          lambda = -‖L2Kernel.kernelOpCLM (mu := mu) hW‖) ∧
        lambda ≠ 0 ∧
        Module.End.HasEigenvalue
          (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap lambda ∧
        FiniteDimensional Real
          (eigenspace
            (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap lambda)) :=
  compactSelfAdjoint_exists_finiteDimensional_norm_endpoint_eigenspace
    (T := L2Kernel.kernelOpCLM (mu := mu) hW)
    hcompact
    (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW)
    (L2Kernel.kernelOpCLM_ne_zero_of_edgeDensity_pos
      (mu := mu) hW hp)

/-- A positive-density compact canonical graphon operator has a genuine unit
eigenvector at one of the two operator-norm endpoints.

This is a graphon specialization of compact self-adjoint Hilbert-space theory.
It extracts one nonzero mode and does not assert finite spectrum. -/
theorem canonicalGraphonCompact_exists_norm_endpoint_unit_eigenvector_of_edgeDensity_pos
    (hW : IsGraphon W mu)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW))
    (hp : 0 < edgeDensity W mu) :
    ∃ lambda : Real, ∃ v : Lp Real 2 mu,
      (lambda = ‖L2Kernel.kernelOpCLM (mu := mu) hW‖ ∨
        lambda = -‖L2Kernel.kernelOpCLM (mu := mu) hW‖) ∧
        lambda ≠ 0 ∧ v ≠ 0 ∧ ‖v‖ = 1 ∧
          L2Kernel.kernelOpCLM (mu := mu) hW v = lambda • v := by
  exact
    compactSelfAdjoint_exists_norm_endpoint_unit_eigenvector
      (T := L2Kernel.kernelOpCLM (mu := mu) hW)
      hcompact
      (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW)
      (L2Kernel.kernelOpCLM_ne_zero_of_edgeDensity_pos
        (mu := mu) hW hp)

/-- If the canonical compact graphon operator has no nonzero eigenvalue, it is
the zero operator.  This is the graphon-specialized compact spectral
separation principle used when extracting nonzero modes. -/
theorem canonicalGraphonCompact_eq_zero_of_no_nonzero_eigenvalue
    (hW : IsGraphon W mu)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW))
    (hzero :
      ∀ lambda : Real,
        HasEigenvalue
          (L2Kernel.kernelOpCLM (mu := mu) hW :
            Module.End Real (Lp Real 2 mu))
          lambda ->
        lambda = 0) :
    L2Kernel.kernelOpCLM (mu := mu) hW = 0 :=
  compactSelfAdjoint_eq_zero_of_no_nonzero_eigenvalue hcompact
    (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW) hzero

/-- A positive-density compact canonical graphon operator has a nonzero
eigenvalue.

This is a compact self-adjoint consequence, not a finite-spectrum statement:
it only extracts one genuine nonzero mode from nonvanishing of the operator. -/
theorem canonicalGraphonCompact_exists_nonzero_eigenvalue_of_edgeDensity_pos
    (hW : IsGraphon W mu)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW))
    (hp : 0 < edgeDensity W mu) :
    Exists (fun lambda : Real =>
      Ne lambda 0 ∧
        HasEigenvalue
          (L2Kernel.kernelOpCLM (mu := mu) hW :
            Module.End Real (Lp Real 2 mu))
          lambda) := by
  by_contra hnone
  have hzero_eigs :
      forall lambda : Real,
        HasEigenvalue
          (L2Kernel.kernelOpCLM (mu := mu) hW :
            Module.End Real (Lp Real 2 mu))
          lambda ->
        lambda = 0 := by
    intro lambda hlambda
    by_contra hlambda0
    exact hnone ⟨lambda, hlambda0, hlambda⟩
  have hzero :=
    canonicalGraphonCompact_eq_zero_of_no_nonzero_eigenvalue
      (mu := mu) hW hcompact hzero_eigs
  exact
    (L2Kernel.kernelOpCLM_ne_zero_of_edgeDensity_pos
      (mu := mu) hW hp) hzero

/-- The nonzero mode extracted from a positive-density compact canonical
graphon operator has finite-dimensional eigenspace.

This records the finite-multiplicity part of compact spectral theory without
asserting that there are only finitely many nonzero modes. -/
theorem canonicalGraphonCompact_exists_finiteDimensional_nonzero_eigenspace_of_edgeDensity_pos
    (hW : IsGraphon W mu)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW))
    (hp : 0 < edgeDensity W mu) :
    Exists (fun lambda : Real =>
      Ne lambda 0 ∧
        HasEigenvalue
          (L2Kernel.kernelOpCLM (mu := mu) hW :
            Module.End Real (Lp Real 2 mu))
          lambda ∧
        FiniteDimensional Real
          (eigenspace
            (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap lambda)) := by
  obtain ⟨lambda, hlambda0, hlambda⟩ :=
    canonicalGraphonCompact_exists_nonzero_eigenvalue_of_edgeDensity_pos
      (mu := mu) hW hcompact hp
  refine ⟨lambda, hlambda0, hlambda, ?_⟩
  exact ContinuousLinearMap.finite_dimensional_eigenspace
    (T := L2Kernel.kernelOpCLM (mu := mu) hW) hcompact lambda hlambda0

end Graphon

end CompactSpectral
end LowBand
end OddCycleBound
