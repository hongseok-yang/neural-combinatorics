import OddCycleBound.IntermediateRegion.SpectralFoundation

/-!
# Trace powers for the signed centered kernel

The C9 trace extraction was originally phrased only for graphons and a
`Nat`-indexed spectral list.  the intermediate region needs the same argument for the signed
centered kernel and its canonical (possibly non-`Nat`-presented) nonzero
spectrum.  This file supplies that reusable bridge.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.Spectral
open OddCycleBound.Spectral.InfiniteSpectral
open OddCycleBound.Spectral.L2Kernel

universe u v

section BoundedKernelTrace

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {K : Omega → Omega → Real}

/-- A bounded-kernel operator iterate is represented by the corresponding
composed kernel on every bounded representative. -/
lemma kernelOpGoodKCLM_iter_goodL2_eq_compPow
    (hK : GoodK K) {C : Real} (hC0 : 0 ≤ C)
    (hKC : ∀ x y, |K x y| ≤ C)
    {f : Omega → Real} (hf : Good f) (n : Nat) :
    clmIter (mu := mu) (kernelOpGoodKCLM (mu := mu) hK hC0 hKC) (n + 1)
        (goodL2 (mu := mu) hf) =
      kernelOpL2OfGoodK (mu := mu) (goodK_compPow (μ := mu) hK n) hf := by
  rw [kernelOpGoodKCLM_iter_goodL2 (mu := mu) hK hC0 hKC hf (n + 1)]
  rw [← kernelOpL2OfGoodK_compPow_eq_goodL2_iter_succ
    (mu := mu) hK hf n]

/-- Signed bounded-kernel version of the graphon row/trace identity. -/
lemma trace_compPow_eq_integral_row_inner_goodK_clmIter
    (hK : GoodK K) {C : Real} (hC0 : 0 ≤ C)
    (hKC : ∀ x y, |K x y| ≤ C)
    (hsymm : ∀ x y, K x y = K y x) (k : Nat) :
    trace mu (compPow mu K (k + 2)) =
      ∫ x, inner Real
        (goodL2 (mu := mu) (goodK_row hK x))
        (clmIter (mu := mu) (kernelOpGoodKCLM (mu := mu) hK hC0 hKC)
          (k + 1) (goodL2 (mu := mu) (goodK_row hK x))) ∂mu := by
  have hpowk : GoodK (compPow mu K k) := goodK_compPow (μ := mu) hK k
  have hpowks : GoodK (compPow mu K (k + 1)) :=
    goodK_compPow (μ := mu) hK (k + 1)
  have htrace_rotate :
      trace mu (compPow mu K (k + 2)) =
        trace mu (comp mu (compPow mu K (k + 1)) K) := by
    change trace mu (comp mu K (compPow mu K (k + 1))) =
      trace mu (comp mu (compPow mu K (k + 1)) K)
    exact trace_comp_comm (μ := mu) hK hpowks
  rw [htrace_rotate, trace]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  let hrow : Good (fun y : Omega => K x y) := goodK_row hK x
  have hiter :
      clmIter (mu := mu) (kernelOpGoodKCLM (mu := mu) hK hC0 hKC) (k + 1)
          (goodL2 (mu := mu) hrow) =
        kernelOpL2OfGoodK (mu := mu) hpowk hrow := by
    exact kernelOpGoodKCLM_iter_goodL2_eq_compPow
      (mu := mu) hK hC0 hKC hrow k
  have hkernel :
      kernelOp K mu
          (fun y : Omega =>
            (kernelOpL2OfGoodK (mu := mu) hpowk hrow : Lp Real 2 mu) y)
          x =
        kernelOp K mu (kernelOp (compPow mu K k) mu (fun y => K x y)) x := by
    unfold kernelOp
    refine integral_congr_ae ?_
    filter_upwards [kernelOpL2OfGoodK_ae_eq (mu := mu) hpowk hrow] with y hy
    rw [hy]
    simp [kernelOp]
  calc
    comp mu (compPow mu K (k + 1)) K x x
        = kernelOp (compPow mu K (k + 1)) mu (fun y : Omega => K x y) x := by
          unfold comp kernelOp
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          change compPow mu K (k + 1) x y * K y x =
            compPow mu K (k + 1) x y * K x y
          rw [hsymm y x]
    _ = kernelOp K mu (kernelOp (compPow mu K k) mu (fun y => K x y)) x := by
          rw [← kernelOp_comp_eq_kernelOp_kernelOp
            (mu := mu) hK hpowk hrow]
          rfl
    _ = kernelOp K mu
          (fun y : Omega =>
            (kernelOpL2OfGoodK (mu := mu) hpowk hrow : Lp Real 2 mu) y)
          x := hkernel.symm
    _ = inner Real (goodL2 (mu := mu) hrow)
          (kernelOpL2OfGoodK (mu := mu) hpowk hrow) := by
          rw [inner_goodK_row_l2_eq_kernelOp (mu := mu) hK
            (kernelOpL2OfGoodK (mu := mu) hpowk hrow) x]
    _ = inner Real (goodL2 (mu := mu) hrow)
          (clmIter (mu := mu) (kernelOpGoodKCLM (mu := mu) hK hC0 hKC)
            (k + 1) (goodL2 (mu := mu) hrow)) := by rw [hiter]

end BoundedKernelTrace

section IndexedExpansion

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable {ι : Type v}

/-- An indexed diagonal action expansion propagates through all positive
operator iterates.  Unlike the older C9 helper, the index type is arbitrary. -/
theorem indexed_action_expansion_iter
    (T : E →L[Real] E) (mode : ι → E) (eigen : ι → Real)
    (hdiag : ∀ i, T (mode i) = eigen i • mode i)
    (haction : ∀ f : E, HasSum
      (fun i : ι => (eigen i * inner Real f (mode i)) • mode i) (T f)) :
    ∀ k f, HasSum
      (fun i : ι => (eigen i ^ (k + 1) * inner Real f (mode i)) • mode i)
      (opIter T (k + 1) f) := by
  intro k
  induction k with
  | zero =>
      intro f
      simpa [opIter] using haction f
  | succ k ih =>
      intro f
      have hmap := (ih f).mapL T
      simpa [opIter, hdiag, smul_smul, pow_succ, mul_assoc, mul_comm,
        mul_left_comm] using hmap

/-- Quadratic-form version of `indexed_action_expansion_iter`. -/
theorem indexed_quadratic_expansion_iter
    (T : E →L[Real] E) (mode : ι → E) (eigen : ι → Real)
    (hdiag : ∀ i, T (mode i) = eigen i • mode i)
    (haction : ∀ f : E, HasSum
      (fun i : ι => (eigen i * inner Real f (mode i)) • mode i) (T f)) :
    ∀ k f, HasSum
      (fun i : ι => eigen i ^ (k + 1) * inner Real f (mode i) ^ 2)
      (inner Real f (opIter T (k + 1) f)) := by
  intro k f
  have hvec := indexed_action_expansion_iter T mode eigen hdiag haction k f
  have hinner := hvec.mapL ((innerSL Real) f)
  simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hinner

end IndexedExpansion

section CenteredTrace

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega → Omega → Real}

/-- Every centered eigenvalue lies in the crude uniform interval `[-4,4]`.
The sharper the intermediate region interval is established later from graphon structure;
this bound is enough for dominated trace extraction. -/
theorem abs_centeredEigenvalue_le_four (hW : IsGraphon W mu)
    (i : CenteredEigenIndex hW) :
    |centeredEigenvalue hW i| ≤ 4 := by
  have hnormMode : ‖centeredEigenmode hW i‖ = 1 :=
    (centeredEigenmode_orthonormal hW).norm_eq_one i
  have hop : ‖centeredKernelOp hW‖ ≤ 4 := by
    exact norm_kernelOpGoodKCLM_le (mu := mu) (centeredKernel_goodK hW)
      (by norm_num : (0 : Real) ≤ 4) (abs_centeredKernel_le_four hW)
  calc
    |centeredEigenvalue hW i| =
        ‖centeredEigenvalue hW i • centeredEigenmode hW i‖ := by
          rw [norm_smul, hnormMode, mul_one, Real.norm_eq_abs]
    _ = ‖centeredKernelOp hW (centeredEigenmode hW i)‖ := by
          rw [centeredKernelOp_eq_centeredGraphonOp hW,
            centeredEigenmode_diagonal hW i]
    _ ≤ ‖centeredKernelOp hW‖ * ‖centeredEigenmode hW i‖ :=
          ContinuousLinearMap.le_opNorm _ _
    _ = ‖centeredKernelOp hW‖ * 1 := by rw [hnormMode]
    _ ≤ 4 * 1 := mul_le_mul_of_nonneg_right hop (by norm_num)
    _ = 4 := by norm_num

/-- The centered spectral expansion paired with any positive operator
iterate. -/
theorem centered_quadratic_expansion_clmIter (hW : IsGraphon W mu)
    (k : Nat) (f : Lp Real 2 mu) :
    HasSum
      (fun i : CenteredEigenIndex hW =>
        centeredEigenvalue hW i ^ (k + 1) *
          inner Real f (centeredEigenmode hW i) ^ 2)
      (inner Real f
        (clmIter (mu := mu) (centeredKernelOp hW) (k + 1) f)) := by
  have hquad := indexed_quadratic_expansion_iter
    (OddCycleBound.DenseRegion.centeredGraphonOp hW)
    (centeredEigenmode hW) (centeredEigenvalue hW)
    (centeredEigenmode_diagonal hW)
    (centeredGraphonOp_action_expansion hW) k f
  rw [centeredKernelOp_eq_centeredGraphonOp hW]
  simpa [opIter_eq_l2_clmIter (mu := mu)] using hquad

/-- The integral of a centered row-coordinate square is the square of the
corresponding centered eigenvalue. -/
theorem integral_centered_row_inner_sq_eq_eigen_sq
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW) :
    (∫ x, inner Real
        (goodL2 (mu := mu) (goodK_row (centeredKernel_goodK hW) x))
        (centeredEigenmode hW i) ^ 2 ∂mu) =
      centeredEigenvalue hW i ^ 2 := by
  classical
  have hrowEnergy :
      ‖centeredKernelOp hW (centeredEigenmode hW i)‖ ^ 2 =
        ∫ x, inner Real
          (goodL2 (mu := mu) (goodK_row (centeredKernel_goodK hW) x))
          (centeredEigenmode hW i) ^ 2 ∂mu := by
    simpa [centeredKernelOp] using
      (sum_norm_kernelOpGoodKCLM_sq_eq_integral_sum_row_inner_l2_sq
        (mu := mu) (centeredKernel_goodK hW)
        (by norm_num : (0 : Real) ≤ 4) (abs_centeredKernel_le_four hW)
        (centeredKernel_symm hW) (centeredEigenmode hW)
        ({i} : Finset (CenteredEigenIndex hW)))
  rw [← hrowEnergy, centeredKernelOp_eq_centeredGraphonOp hW,
    centeredEigenmode_diagonal hW i]
  have hnormMode : ‖centeredEigenmode hW i‖ = 1 :=
    (centeredEigenmode_orthonormal hW).norm_eq_one i
  rw [norm_smul, hnormMode, mul_one, Real.norm_eq_abs, sq_abs]

/-- Term-by-term integration of the centered row quadratic expansion. -/
theorem hasSum_integral_centered_row_weighted_inner_sq
    (hW : IsGraphon W mu) (k : Nat) :
    HasSum
      (fun i : CenteredEigenIndex hW =>
        ∫ x, centeredEigenvalue hW i ^ (k + 1) *
          inner Real
            (goodL2 (mu := mu) (goodK_row (centeredKernel_goodK hW) x))
            (centeredEigenmode hW i) ^ 2 ∂mu)
      (∫ x, inner Real
        (goodL2 (mu := mu) (goodK_row (centeredKernel_goodK hW) x))
        (clmIter (mu := mu) (centeredKernelOp hW) (k + 1)
          (goodL2 (mu := mu) (goodK_row (centeredKernel_goodK hW) x))) ∂mu) := by
  letI : Countable (CenteredEigenIndex hW) :=
    nonzeroEigenIndex_countable
      (OddCycleBound.DenseRegion.centeredGraphonOp hW)
      (centeredGraphonOp_isCompact hW)
      (OddCycleBound.DenseRegion.centeredGraphonOp_isSymmetric hW)
  classical
  let row : Omega → Lp Real 2 mu := fun x =>
    goodL2 (mu := mu) (goodK_row (centeredKernel_goodK hW) x)
  let coordSq : CenteredEigenIndex hW → Omega → Real := fun i x =>
    inner Real (row x) (centeredEigenmode hW i) ^ 2
  let F : CenteredEigenIndex hW → Omega → Real := fun i x =>
    centeredEigenvalue hW i ^ (k + 1) * coordSq i x
  let f : Omega → Real := fun x =>
    inner Real (row x)
      (clmIter (mu := mu) (centeredKernelOp hW) (k + 1) (row x))
  have hcoordIntegrable : ∀ i : CenteredEigenIndex hW,
      Integrable (fun x : Omega => coordSq i x) mu := by
    intro i
    simpa [coordSq, row] using
      (integrable_sum_goodK_row_inner_l2_sq
        (mu := mu) (centeredKernel_goodK hW)
        (by norm_num : (0 : Real) ≤ 4) (abs_centeredKernel_le_four hW)
        (centeredEigenmode hW) ({i} : Finset (CenteredEigenIndex hW)))
  have hFIntegrable : ∀ i : CenteredEigenIndex hW, Integrable (F i) mu := by
    intro i
    exact (hcoordIntegrable i).const_mul (centeredEigenvalue hW i ^ (k + 1))
  have hFIntegralNormLe : ∀ i : CenteredEigenIndex hW,
      (∫ x, ‖F i x‖ ∂mu) ≤
        4 ^ (k + 1) * centeredEigenvalue hW i ^ 2 := by
    intro i
    have hpowAbs : |centeredEigenvalue hW i ^ (k + 1)| ≤ 4 ^ (k + 1) := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_centeredEigenvalue_le_four hW i) _
    have hpoint : (fun x : Omega => ‖F i x‖) ≤
        fun x => 4 ^ (k + 1) * coordSq i x := by
      intro x
      have hcoordNonneg : 0 ≤ coordSq i x := sq_nonneg _
      calc
        ‖F i x‖ = |centeredEigenvalue hW i ^ (k + 1)| * coordSq i x := by
          simp [F, coordSq, Real.norm_eq_abs]
        _ ≤ 4 ^ (k + 1) * coordSq i x :=
          mul_le_mul_of_nonneg_right hpowAbs hcoordNonneg
    calc
      (∫ x, ‖F i x‖ ∂mu) ≤
          ∫ x, 4 ^ (k + 1) * coordSq i x ∂mu := by
            exact integral_mono (hFIntegrable i).norm
              ((hcoordIntegrable i).const_mul _) hpoint
      _ = 4 ^ (k + 1) * centeredEigenvalue hW i ^ 2 := by
            rw [integral_const_mul]
            rw [integral_centered_row_inner_sq_eq_eigen_sq hW i]
  have hFIntegralNormSummable :
      Summable fun i : CenteredEigenIndex hW => ∫ x, ‖F i x‖ ∂mu := by
    refine ((centeredEigenvalue_square_summable hW).mul_left
      (4 ^ (k + 1))).of_norm_bounded ?_
    intro i
    have hnonneg : 0 ≤ ∫ x, ‖F i x‖ ∂mu := integral_nonneg fun x => norm_nonneg _
    calc
      ‖∫ x, ‖F i x‖ ∂mu‖ = ∫ x, ‖F i x‖ ∂mu := Real.norm_of_nonneg hnonneg
      _ ≤ 4 ^ (k + 1) * centeredEigenvalue hW i ^ 2 := hFIntegralNormLe i
  have hseries :
      HasSum (fun i : CenteredEigenIndex hW => ∫ x, F i x ∂mu)
        (∫ x, ∑' i : CenteredEigenIndex hW, F i x ∂mu) :=
    hasSum_integral_of_summable_integral_norm
      (F := F) hFIntegrable hFIntegralNormSummable
  have htsumFun : (fun x : Omega => ∑' i : CenteredEigenIndex hW, F i x) = f := by
    funext x
    simpa [F, f, coordSq, row] using
      (centered_quadratic_expansion_clmIter hW k (row x)).tsum_eq
  rw [htsumFun] at hseries
  simpa [F, f, coordSq, row] using hseries

/-- Every centered kernel trace power of exponent at least three is the
corresponding spectral moment. -/
theorem centered_trace_compPow_hasSum_eigen_pow
    (hW : IsGraphon W mu) (k : Nat) :
    HasSum (fun i : CenteredEigenIndex hW => centeredEigenvalue hW i ^ (k + 3))
      (trace mu (compPow mu (centeredKernel W mu) (k + 2))) := by
  rw [trace_compPow_eq_integral_row_inner_goodK_clmIter
    (mu := mu) (centeredKernel_goodK hW)
    (by norm_num : (0 : Real) ≤ 4) (abs_centeredKernel_le_four hW)
    (centeredKernel_symm hW) k]
  have hseries := hasSum_integral_centered_row_weighted_inner_sq hW k
  refine hseries.congr_fun ?_
  intro i
  symm
  rw [integral_const_mul]
  rw [integral_centered_row_inner_sq_eq_eigen_sq hW i]
  calc
    centeredEigenvalue hW i ^ (k + 1) * centeredEigenvalue hW i ^ 2 =
        centeredEigenvalue hW i ^ ((k + 1) + 2) := by rw [← pow_add]
    _ = centeredEigenvalue hW i ^ (k + 3) := rfl

/-- `tsum` form of the centered trace-power identity. -/
theorem centered_trace_compPow_eq_tsum_eigen_pow
    (hW : IsGraphon W mu) (k : Nat) :
    trace mu (compPow mu (centeredKernel W mu) (k + 2)) =
      ∑' i : CenteredEigenIndex hW, centeredEigenvalue hW i ^ (k + 3) := by
  exact (centered_trace_compPow_hasSum_eigen_pow hW k).tsum_eq.symm

end CenteredTrace

end OddCycleBound.IntermediateRegion
