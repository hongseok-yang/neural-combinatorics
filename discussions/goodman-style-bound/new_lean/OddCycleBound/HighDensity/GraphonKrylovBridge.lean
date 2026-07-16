/-
# High-density theorem — graphon L² compression and Krylov moments

This file realizes the abstract Krylov construction on graphon `L²`.  The centered operator is
`P T_W P`, where `P = I - |1><1|`.  Its distinguished vector is the centered degree function.
Iterating this operator reproduces the pointwise `compressIter`, so its vector moments are exactly
`specMoment`.
-/

import OddCycleBound.LowBand.GraphonL2Operator
import OddCycleBound.HighDensity.KrylovCompression
import OddCycleBound.HighDensity.MomentExpansion
import Mathlib.Analysis.InnerProductSpace.Rayleigh

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace OddCycleBound.HighDensity

open OddCycleBound.LowBand.L2Kernel

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega → Omega → ℝ}

/-- Pairing with the constant-one `L²` vector is the pointwise mean. -/
lemma inner_oneL2_goodL2_eq_mean {f : Omega → ℝ} (hf : Good f) :
    inner ℝ (oneL2 (Omega := Omega) mu) (goodL2 (mu := mu) hf) = mean mu f := by
  rw [← goodL2_one_eq_oneL2 (Omega := Omega) (mu := mu),
    inner_goodL2_eq_integral_mul]
  simp [mean]

lemma good_const (c : ℝ) : Good (fun _ : Omega => c) := by
  exact ⟨stronglyMeasurable_const, ⟨|c|, abs_nonneg c, fun _ => le_rfl⟩⟩

lemma goodL2_const (c : ℝ) :
    goodL2 (mu := mu) (good_const (Omega := Omega) c) =
      c • oneL2 (Omega := Omega) mu := by
  rw [Lp.ext_iff]
  filter_upwards [goodL2_ae_eq (mu := mu) (good_const (Omega := Omega) c),
    Lp.coeFn_smul c (oneL2 (Omega := Omega) mu),
    oneL2_ae_eq_one (Omega := Omega) (mu := mu)] with x hconst hsmul hone
  rw [hconst, hsmul]
  simp [Pi.smul_apply, hone]

/-- The orthogonal projection away from the constant functions. -/
noncomputable def centerProjection :
  Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu :=
  1 - InnerProductSpace.rankOne ℝ
    (oneL2 (Omega := Omega) mu) (oneL2 (Omega := Omega) mu)

/-- Concrete action of the mean-zero projection on a bounded representative. -/
lemma centerProjection_apply_goodL2 {f : Omega → ℝ} (hf : Good f) :
    centerProjection (Omega := Omega) (mu := mu) (goodL2 (mu := mu) hf) =
      goodL2 (mu := mu)
        (good_sub hf (good_const (Omega := Omega) (mean mu f))) := by
  unfold centerProjection
  simp only [sub_apply, one_apply_eq_self, InnerProductSpace.rankOne_apply]
  rw [inner_oneL2_goodL2_eq_mean hf,
    goodL2_sub hf (good_const (Omega := Omega) (mean mu f)), goodL2_const]

lemma centerProjection_apply_of_mean_zero {f : Omega → ℝ} (hf : Good f)
    (hmean : mean mu f = 0) :
    centerProjection (Omega := Omega) (mu := mu) (goodL2 (mu := mu) hf) =
      goodL2 (mu := mu) hf := by
  unfold centerProjection
  simp only [sub_apply, one_apply_eq_self, InnerProductSpace.rankOne_apply,
    inner_oneL2_goodL2_eq_mean hf, hmean, zero_smul,
    sub_zero]

/-- The completed graphon operator sends a `Good` representative to the `Good` representative of
its pointwise kernel transform. -/
lemma kernelOpCLM_goodL2_eq_goodL2 (hW : IsGraphon W mu)
    {f : Omega → ℝ} (hf : Good f) :
    kernelOpCLM (mu := mu) hW (goodL2 (mu := mu) hf) =
      goodL2 (mu := mu) (good_kernelOp hW hf) := by
  rw [kernelOpCLM_goodL2 (mu := mu) hW hf]
  exact MemLp.toLp_congr
    (kernelOp_memLp_two hW hf)
    (good_memLp_two (good_kernelOp hW hf))
    (ae_of_all _ fun _ => rfl)

/-- The self-adjoint centered graphon compression `P T_W P` on all of `L²`. -/
noncomputable def centeredGraphonOp (hW : IsGraphon W mu) :
    Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu :=
  (centerProjection (Omega := Omega) (mu := mu)).comp
    ((kernelOpCLM (mu := mu) hW).comp
      (centerProjection (Omega := Omega) (mu := mu)))

lemma centerProjection_isSymmetric :
    (centerProjection (Omega := Omega) (mu := mu)).toLinearMap.IsSymmetric := by
  exact LinearMap.IsSymmetric.sub LinearMap.IsSymmetric.one
    (InnerProductSpace.isSymmetric_rankOne_self (oneL2 (Omega := Omega) mu))

/-- The centering map is the orthogonal projection onto the mean-zero subspace. -/
lemma centerProjection_isSymmetricProjection :
    (centerProjection (Omega := Omega) (mu := mu)).toLinearMap.IsSymmetricProjection := by
  have hone : ‖oneL2 (Omega := Omega) mu‖ = 1 := by
    have hs := norm_oneL2_sq (Omega := Omega) (mu := mu)
    nlinarith [norm_nonneg (oneL2 (Omega := Omega) mu)]
  have hQ := InnerProductSpace.isSymmetricProjection_rankOne_self
    (𝕜 := ℝ) (E := Lp ℝ 2 mu) hone
  have hI : (1 : Module.End ℝ (Lp ℝ 2 mu)).IsSymmetricProjection := by
    exact ⟨IsIdempotentElem.one, LinearMap.IsSymmetric.one⟩
  have hQI : LinearMap.range (InnerProductSpace.rankOne ℝ
      (oneL2 (Omega := Omega) mu) (oneL2 (Omega := Omega) mu)).toLinearMap ≤
      LinearMap.range (1 : Module.End ℝ (Lp ℝ 2 mu)) := by
    intro x _hx
    exact ⟨x, rfl⟩
  simpa only [centerProjection, ContinuousLinearMap.toLinearMap_sub,
    ContinuousLinearMap.toLinearMap_one] using hQ.sub_of_range_le_range hI hQI

/-- Orthogonal centering cannot increase the `L²` norm. -/
lemma norm_centerProjection_apply_le (f : Lp ℝ 2 mu) :
    ‖centerProjection (Omega := Omega) (mu := mu) f‖ ≤ ‖f‖ := by
  let P := (centerProjection (Omega := Omega) (mu := mu)).toLinearMap
  have hP : P.IsSymmetricProjection :=
    centerProjection_isSymmetricProjection (Omega := Omega) (mu := mu)
  have hsq : ‖P f‖ ^ 2 = inner ℝ (P f) f := by
    calc
      ‖P f‖ ^ 2 = inner ℝ (P f) (P f) := by rw [real_inner_self_eq_norm_sq]
      _ = inner ℝ (P (P f)) f := (hP.isSymmetric (P f) f).symm
      _ = inner ℝ (P f) f := by
        rw [← Module.End.mul_apply, hP.isIdempotentElem]
  have hcs : ‖P f‖ ^ 2 ≤ ‖P f‖ * ‖f‖ := by
    rw [hsq]
    exact real_inner_le_norm _ _
  change ‖P f‖ ≤ ‖f‖
  nlinarith [norm_nonneg (P f), norm_nonneg f]

lemma centeredGraphonOp_isSymmetric (hW : IsGraphon W mu) :
    (centeredGraphonOp hW).toLinearMap.IsSymmetric := by
  intro f g
  have hP := centerProjection_isSymmetric (Omega := Omega) (mu := mu)
  have hT := kernelOpCLM_isSymmetric (mu := mu) hW
  change inner ℝ
      (centerProjection (Omega := Omega) (mu := mu)
        (kernelOpCLM (mu := mu) hW
          (centerProjection (Omega := Omega) (mu := mu) f))) g =
    inner ℝ f
      (centerProjection (Omega := Omega) (mu := mu)
        (kernelOpCLM (mu := mu) hW
          (centerProjection (Omega := Omega) (mu := mu) g)))
  calc
    _ = inner ℝ
        (kernelOpCLM (mu := mu) hW
          (centerProjection (Omega := Omega) (mu := mu) f))
        (centerProjection (Omega := Omega) (mu := mu) g) := hP.apply_clm _ _
    _ = inner ℝ
        (centerProjection (Omega := Omega) (mu := mu) f)
        (kernelOpCLM (mu := mu) hW
          (centerProjection (Omega := Omega) (mu := mu) g)) := hT.apply_clm _ _
    _ = _ := hP.apply_clm _ _

/-- On a mean-zero bounded function, the centered `L²` operator agrees with pointwise `compress`. -/
lemma centeredGraphonOp_apply_mean_zero_goodL2 (hW : IsGraphon W mu)
    {f : Omega → ℝ} (hf : Good f) (hmean : mean mu f = 0) :
    centeredGraphonOp hW (goodL2 (mu := mu) hf) =
      goodL2 (mu := mu) (good_compress hW hf) := by
  unfold centeredGraphonOp
  change centerProjection (Omega := Omega) (mu := mu)
      (kernelOpCLM (mu := mu) hW
        (centerProjection (Omega := Omega) (mu := mu) (goodL2 (mu := mu) hf))) = _
  rw [centerProjection_apply_of_mean_zero hf hmean]
  rw [kernelOpCLM_goodL2_eq_goodL2 hW hf]
  rw [centerProjection_apply_goodL2 (good_kernelOp hW hf)]
  exact MemLp.toLp_congr
    (good_memLp_two
      (good_sub (good_kernelOp hW hf)
        (good_const (Omega := Omega) (mean mu (kernelOp W mu f)))))
    (good_memLp_two (good_compress hW hf))
    (ae_of_all _ fun _ => by rfl)

/-- The distinguished compression vector, namely the centered degree function. -/
noncomputable def centeredDegreeL2 (hW : IsGraphon W mu) : Lp ℝ 2 mu :=
  goodL2 (mu := mu) (good_degCentered hW)

/-- Iterating the centered `L²` operator reproduces the graphon's pointwise compression iterates. -/
theorem linearIter_centeredGraphonOp (hW : IsGraphon W mu) : ∀ j : ℕ,
    linearIter (centeredGraphonOp hW).toLinearMap j (centeredDegreeL2 hW) =
      goodL2 (mu := mu) (good_compressIter hW j)
  | 0 => rfl
  | j + 1 => by
      rw [linearIter_succ, linearIter_centeredGraphonOp hW j]
      exact centeredGraphonOp_apply_mean_zero_goodL2 hW
        (good_compressIter hW j) (mean_compressIter hW j)

/-- **Graphon moment bridge for P/E2.**  Compression vector moments in `L²` are exactly the
pointwise `specMoment` sequence. -/
theorem inner_linearIter_centeredGraphonOp_eq_specMoment (hW : IsGraphon W mu) (j : ℕ) :
    inner ℝ (centeredDegreeL2 hW)
        (linearIter (centeredGraphonOp hW).toLinearMap j (centeredDegreeL2 hW)) =
      specMoment W mu j := by
  rw [linearIter_centeredGraphonOp hW j]
  exact inner_goodL2_eq_integral_mul (good_degCentered hW) (good_compressIter hW j)

/-! ## Finite atomic data attached to a graphon cutoff -/

/-- The eigenvalue atoms of the finite Krylov compression of the centered graphon operator. -/
noncomputable def graphonAtomEigenvalue (hW : IsGraphon W mu) (d : ℕ) :
    Fin (Module.finrank ℝ
      (krylovSubspace (centeredGraphonOp hW) (centeredDegreeL2 hW) d)) → ℝ :=
  finiteAtomEigenvalue
    (krylovCompression (centeredGraphonOp hW) (centeredDegreeL2 hW) d).toLinearMap
    (krylovCompression_isSymmetric _ _ _ (centeredGraphonOp_isSymmetric hW))

/-- Nonnegative squared-coordinate weights of the centered degree vector. -/
noncomputable def graphonAtomWeight (hW : IsGraphon W mu) (d : ℕ) :
    Fin (Module.finrank ℝ
      (krylovSubspace (centeredGraphonOp hW) (centeredDegreeL2 hW) d)) → ℝ :=
  finiteAtomWeight
    (krylovCompression (centeredGraphonOp hW) (centeredDegreeL2 hW) d).toLinearMap
    (krylovCompression_isSymmetric _ _ _ (centeredGraphonOp_isSymmetric hW))
    (krylovVector (centeredGraphonOp hW) (centeredDegreeL2 hW) d)

lemma graphonAtomWeight_nonneg (hW : IsGraphon W mu) (d : ℕ) (i) :
    0 ≤ graphonAtomWeight hW d i := by
  exact finiteAtomWeight_nonneg _ _ _ i

/-- **P/E2 finite graphon representation.**  For every `j ≤ d`, the graphon compression moment is
the atomic moment of the cutoff Krylov compression. -/
theorem specMoment_eq_graphonAtomicMoment (hW : IsGraphon W mu)
    {d j : ℕ} (hj : j ≤ d) :
    specMoment W mu j =
      atomicMoment (graphonAtomWeight hW d) (graphonAtomEigenvalue hW d) j := by
  rw [← inner_linearIter_centeredGraphonOp_eq_specMoment hW j]
  simpa only [graphonAtomWeight, graphonAtomEigenvalue] using
    inner_linearIter_eq_krylovAtomicMoment
      (centeredGraphonOp hW) (centeredDegreeL2 hW)
      (centeredGraphonOp_isSymmetric hW) hj

/-- The graphon Krylov atoms have the required support as soon as the centered graphon compression
has the sharp norm bound. -/
theorem graphonAtomEigenvalue_mem_halfInterval_of_norm (hW : IsGraphon W mu) (d : ℕ)
    (hnorm : ‖centeredGraphonOp hW‖ ≤ (1 : ℝ) / 2) (i) :
    graphonAtomEigenvalue hW d i ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) := by
  exact krylovAtomEigenvalue_mem_halfInterval
    (centeredGraphonOp hW) (centeredDegreeL2 hW) d
    (centeredGraphonOp_isSymmetric hW) hnorm i

/-! ## The sharp compression quadratic-form estimate -/

/-- For a bounded mean-zero function, the graphon quadratic form has absolute value at most half
its `L²` square.  The proof applies positivity domination to both `W` and `1-W`; their two positive
majorants add to `(∫|f|)²`, which is at most `∫f²`. -/
lemma abs_integral_mul_kernelOp_le_half (hW : IsGraphon W mu)
    {f : Omega → ℝ} (hf : Good f) (hmean : mean mu f = 0) :
    |∫ x, f x * kernelOp W mu f x ∂mu| ≤
      (1 : ℝ) / 2 * ∫ x, f x * f x ∂mu := by
  let U := compl W
  have hU : IsGraphon U mu := isGraphon_compl hW
  have hdomW :
      |∫ x, f x * kernelOp W mu f x ∂mu| ≤
        ∫ x, |f x| * kernelOp W mu (fun y => |f y|) x ∂mu := by
    simpa only [inner_goodL2_kernelOpL2OfGood_eq_integral] using
      (abs_inner_goodL2_kernelOpL2OfGood_self_le_abs (mu := mu) hW hf)
  have hdomU :
      |∫ x, f x * kernelOp U mu f x ∂mu| ≤
        ∫ x, |f x| * kernelOp U mu (fun y => |f y|) x ∂mu := by
    simpa only [inner_goodL2_kernelOpL2OfGood_eq_integral] using
      (abs_inner_goodL2_kernelOpL2OfGood_self_le_abs (mu := mu) hU hf)
  have hcomp :
      (∫ x, f x * kernelOp U mu f x ∂mu) =
        -(∫ x, f x * kernelOp W mu f x ∂mu) := by
    calc
      (∫ x, f x * kernelOp U mu f x ∂mu) =
          ∫ x, -(f x * kernelOp W mu f x) ∂mu := by
            refine integral_congr_ae (ae_of_all _ fun x => ?_)
            change f x * kernelOp (compl W) mu f x = _
            rw [kernelOp_compl hW hf x, hmean]
            ring
      _ = -(∫ x, f x * kernelOp W mu f x ∂mu) := by rw [integral_neg]
  have hdomU' :
      |∫ x, f x * kernelOp W mu f x ∂mu| ≤
        ∫ x, |f x| * kernelOp U mu (fun y => |f y|) x ∂mu := by
    simpa only [hcomp, abs_neg] using hdomU
  have hsum :
      (∫ x, |f x| * kernelOp W mu (fun y => |f y|) x ∂mu) +
          (∫ x, |f x| * kernelOp U mu (fun y => |f y|) x ∂mu) =
        (∫ x, |f x| ∂mu) ^ 2 := by
    have hWa := (good_abs hf).mul (good_kernelOp hW (good_abs hf))
    have hUa := (good_abs hf).mul (good_kernelOp hU (good_abs hf))
    rw [← integral_add hWa.integrable hUa.integrable]
    calc
      (∫ x,
          (|f x| * kernelOp W mu (fun y => |f y|) x +
            |f x| * kernelOp U mu (fun y => |f y|) x) ∂mu) =
          ∫ x, (∫ y, |f y| ∂mu) * |f x| ∂mu := by
            refine integral_congr_ae (ae_of_all _ fun x => ?_)
            change _ + |f x| * kernelOp (compl W) mu (fun y => |f y|) x = _
            rw [kernelOp_compl hW (good_abs hf) x]
            simp only [mean]
            ring
      _ = (∫ x, |f x| ∂mu) ^ 2 := by
            rw [integral_const_mul]
            ring
  have hL1 := integral_abs_sq_le_integral_mul_self (mu := mu) hf
  linarith

/-- The sharp quadratic-form bound on the dense subspace of bounded `L²` representatives. -/
lemma abs_inner_centeredGraphonOp_goodL2_le_half (hW : IsGraphon W mu)
    {f : Omega → ℝ} (hf : Good f) :
    |inner ℝ (goodL2 (mu := mu) hf)
        (centeredGraphonOp hW (goodL2 (mu := mu) hf))| ≤
      (1 : ℝ) / 2 * ‖goodL2 (mu := mu) hf‖ ^ 2 := by
  let fc : Omega → ℝ := fun x => f x - mean mu f
  have hfc : Good fc := good_sub hf (good_const (Omega := Omega) (mean mu f))
  have hfc_mean : mean mu fc = 0 := by
    unfold fc mean
    rw [integral_sub hf.integrable (integrable_const _)]
    simp
  have hP : centerProjection (Omega := Omega) (mu := mu)
      (goodL2 (mu := mu) hf) = goodL2 (mu := mu) hfc := by
    simpa only [fc] using centerProjection_apply_goodL2 (mu := mu) hf
  have hpoint := abs_integral_mul_kernelOp_le_half (mu := mu) hW hfc hfc_mean
  have hcontract := norm_centerProjection_apply_le (Omega := Omega) (mu := mu)
    (goodL2 (mu := mu) hf)
  have hsquare : ‖goodL2 (mu := mu) hfc‖ ^ 2 ≤
      ‖goodL2 (mu := mu) hf‖ ^ 2 := by
    rw [hP] at hcontract
    nlinarith [norm_nonneg (goodL2 (mu := mu) hfc),
      norm_nonneg (goodL2 (mu := mu) hf)]
  have hquad :
      |inner ℝ (goodL2 (mu := mu) hfc)
          (kernelOpCLM (mu := mu) hW (goodL2 (mu := mu) hfc))| ≤
        (1 : ℝ) / 2 * ‖goodL2 (mu := mu) hfc‖ ^ 2 := by
    rw [kernelOpCLM_goodL2_eq_goodL2 hW hfc,
      inner_goodL2_eq_integral_mul,
      norm_goodL2_sq_eq_integral_mul]
    exact hpoint
  change |inner ℝ (goodL2 (mu := mu) hf)
      (centerProjection (Omega := Omega) (mu := mu)
        (kernelOpCLM (mu := mu) hW
          (centerProjection (Omega := Omega) (mu := mu)
            (goodL2 (mu := mu) hf))))| ≤ _
  rw [← (centerProjection_isSymmetric (Omega := Omega) (mu := mu)).apply_clm,
    hP]
  linarith

/-- The sharp quadratic-form bound for every `L²` vector. -/
lemma abs_inner_centeredGraphonOp_self_le_half (hW : IsGraphon W mu)
    (f : Lp ℝ 2 mu) :
    |inner ℝ f (centeredGraphonOp hW f)| ≤ (1 : ℝ) / 2 * ‖f‖ ^ 2 := by
  let p : Lp ℝ 2 mu → Prop := fun f =>
    |inner ℝ f (centeredGraphonOp hW f)| ≤ (1 : ℝ) / 2 * ‖f‖ ^ 2
  change p f
  exact DenseRange.induction_on
    (denseRange_goodL2 (Omega := Omega) (mu := mu)) f
    (by
      dsimp [p]
      exact isClosed_le (by fun_prop) (by fun_prop))
    (by
      intro a
      rcases a with ⟨g, hg⟩
      dsimp [p]
      exact abs_inner_centeredGraphonOp_goodL2_le_half (mu := mu) hW hg)

/-- The centered graphon compression has the sharp operator norm bound `1/2`. -/
theorem norm_centeredGraphonOp_le_half (hW : IsGraphon W mu) :
    ‖centeredGraphonOp hW‖ ≤ (1 : ℝ) / 2 := by
  rw [(centeredGraphonOp hW).norm_eq_iSup_rayleighQuotient
    (centeredGraphonOp_isSymmetric hW)]
  refine ciSup_le fun f => ?_
  by_cases hf : f = 0
  · simp [hf]
  have hnorm : 0 < ‖f‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
  have hquad := abs_inner_centeredGraphonOp_self_le_half (mu := mu) hW f
  rw [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply]
  simp only [RCLike.re_to_real, abs_div, abs_sq]
  rw [div_le_iff₀ hnorm]
  simpa only [real_inner_comm, mul_assoc] using hquad

/-- **P/E2 support.** Every graphon Krylov atom lies in the sharp interval
`[-1/2, 1/2]`. -/
theorem graphonAtomEigenvalue_mem_halfInterval (hW : IsGraphon W mu) (d : ℕ) (i) :
    graphonAtomEigenvalue hW d i ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) := by
  exact graphonAtomEigenvalue_mem_halfInterval_of_norm hW d
    (norm_centeredGraphonOp_le_half hW) i

/-- The cutoff atomic sequence may replace the graphon moments in `momentPhi`. -/
theorem momentPhi_specMoment_eq_graphonAtomicMoment (hW : IsGraphon W mu)
    (m : ℕ) (q : ℝ) :
    momentPhi m q (specMoment W mu) =
      momentPhi m q
        (atomicMoment (graphonAtomWeight hW m) (graphonAtomEigenvalue hW m)) := by
  apply momentPhi_congr_of_le q
  intro j hj
  exact specMoment_eq_graphonAtomicMoment hW hj

/-- **P/E1/E2 graphon endpoint.** Diagonal-kernel positivity implies nonnegativity of the actual
graphon moment defect, using only the finite Krylov cutoff at `m`. -/
theorem momentPhi_specMoment_nonneg {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    (hW : IsGraphon W mu) (q : ℝ)
    (hdiag : ∀ r, 1 ≤ r ∧ 2 * r < m →
      ∀ ell ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2), 0 ≤ diagKernel m r q ell) :
    0 ≤ momentPhi m q (specMoment W mu) := by
  rw [momentPhi_specMoment_eq_graphonAtomicMoment hW m q]
  exact momentPhi_nonneg_of_atomic hm hm3 q
    (graphonAtomWeight hW m) (graphonAtomEigenvalue hW m)
    (graphonAtomWeight_nonneg hW m)
    (graphonAtomEigenvalue_mem_halfInterval hW m)
    (fun r hr hrm => hdiag r ⟨hr, hrm⟩)

end OddCycleBound.HighDensity
