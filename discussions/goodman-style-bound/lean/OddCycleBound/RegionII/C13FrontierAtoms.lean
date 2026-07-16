import OddCycleBound.RegionII.Certificate.C13BernsteinSound
import OddCycleBound.RegionII.SafeFrontier
import OddCycleBound.RegionII.CouplingChannels
import OddCycleBound.HighDensity.KrylovCompression

/-!
# Frontier-plus-Krylov atoms for C13

For the complemented graphon, remove the unique frontier eigenmode from the
centered degree vector and Krylov-compress only the orthogonal residual.  An
`Option` index then adjoins the frontier atom back to the finite safe atomic
measure.
-/

open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

namespace OddCycleBound.RegionII

open OddCycleBound.HighDensity
open OddCycleBound.LowBand.L2Kernel

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

/-- Complementation negates the centered graphon operator on all of `L²`. -/
theorem centeredGraphonOp_compl_eq_neg (hW : IsGraphon W μ) :
    centeredGraphonOp (isGraphon_compl hW) = -centeredGraphonOp hW := by
  apply ContinuousLinearMap.ext (R₁ := ℝ)
  intro v
  exact DenseRange.induction_on
    (denseRange_goodL2 (Omega := Ω) (mu := μ)) v
    (by exact isClosed_eq (by fun_prop) (by fun_prop))
    (by
      intro a
      rcases a with ⟨f, hf⟩
      let fc : Ω → ℝ := centeredInput μ f
      have hfc : Good fc := good_centeredInput (mu := μ) hf
      have hmean : mean μ fc = 0 := mean_centeredInput (mu := μ) hf
      have hP : centerProjection (Omega := Ω) (mu := μ) (goodL2 (mu := μ) hf) =
          goodL2 (mu := μ) hfc := by
        have hPraw := centerProjection_apply_goodL2 (mu := μ) hf
        calc
          centerProjection (Omega := Ω) (mu := μ) (goodL2 (mu := μ) hf) =
              goodL2 (mu := μ)
                (good_sub hf (good_const (Omega := Ω) (mean μ f))) := hPraw
          _ = goodL2 (mu := μ) hfc := by congr
      have hPc : centerProjection (Omega := Ω) (mu := μ) (goodL2 (mu := μ) hfc) =
          goodL2 (mu := μ) hfc :=
        centerProjection_apply_of_mean_zero hfc hmean
      have hcomp := centeredGraphonOp_compl_goodL2_eq_neg hW hfc hmean
      change centeredGraphonOp (isGraphon_compl hW) (goodL2 (mu := μ) hf) =
        (-centeredGraphonOp hW) (goodL2 (mu := μ) hf)
      unfold centeredGraphonOp
      change centerProjection (Omega := Ω) (mu := μ)
          (kernelOpCLM (mu := μ) (isGraphon_compl hW)
            (centerProjection (Omega := Ω) (mu := μ) (goodL2 (mu := μ) hf))) =
        -centerProjection (Omega := Ω) (mu := μ)
          (kernelOpCLM (mu := μ) hW
            (centerProjection (Omega := Ω) (mu := μ) (goodL2 (mu := μ) hf)))
      rw [hP]
      simpa [centeredGraphonOp, hPc] using hcomp)

/-- The original centered eigenmode is a positive eigenmode of the centered
operator of the complemented graphon. -/
theorem centeredGraphonOp_compl_frontier_eigen
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW) :
    centeredGraphonOp (isGraphon_compl hW) (centeredEigenmode hW i) =
      complementEigenvalue hW i • centeredEigenmode hW i := by
  rw [centeredGraphonOp_compl_eq_neg hW, ContinuousLinearMap.neg_apply,
    centeredEigenmode_diagonal]
  simp [complementEigenvalue]

noncomputable def c13FrontierCoefficient
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW) : ℝ :=
  inner ℝ (centeredDegreeL2 (isGraphon_compl hW)) (centeredEigenmode hW i)

noncomputable def c13SafeVector
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW) : Lp ℝ 2 μ :=
  centeredDegreeL2 (isGraphon_compl hW) -
    c13FrontierCoefficient hW i • centeredEigenmode hW i

lemma inner_c13SafeVector_frontier
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW) :
    inner ℝ (c13SafeVector hW i) (centeredEigenmode hW i) = 0 := by
  rw [c13SafeVector, inner_sub_left, inner_smul_left]
  have hnorm := (centeredEigenmode_orthonormal hW).norm_eq_one i
  rw [real_inner_self_eq_norm_sq, hnorm]
  simp [c13FrontierCoefficient]

lemma inner_linearIter_c13SafeVector_frontier
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW) : ∀ j : ℕ,
    inner ℝ
      (linearIter (centeredGraphonOp (isGraphon_compl hW)).toLinearMap j
        (c13SafeVector hW i))
      (centeredEigenmode hW i) = 0
  | 0 => inner_c13SafeVector_frontier hW i
  | j + 1 => by
      rw [linearIter_succ]
      change inner ℝ
        (centeredGraphonOp (isGraphon_compl hW)
          (linearIter (centeredGraphonOp (isGraphon_compl hW)).toLinearMap j
            (c13SafeVector hW i)))
        (centeredEigenmode hW i) = 0
      rw [(centeredGraphonOp_isSymmetric (isGraphon_compl hW)).apply_clm,
        centeredGraphonOp_compl_frontier_eigen hW i,
        real_inner_smul_right,
        inner_linearIter_c13SafeVector_frontier hW i j, mul_zero]

lemma linearIter_centeredDegree_compl_decomp
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW) : ∀ j : ℕ,
    linearIter (centeredGraphonOp (isGraphon_compl hW)).toLinearMap j
        (centeredDegreeL2 (isGraphon_compl hW)) =
      (c13FrontierCoefficient hW i * complementEigenvalue hW i ^ j) •
          centeredEigenmode hW i +
        linearIter (centeredGraphonOp (isGraphon_compl hW)).toLinearMap j
          (c13SafeVector hW i)
  | 0 => by
      simp only [linearIter_zero, pow_zero, mul_one]
      unfold c13SafeVector
      abel
  | j + 1 => by
      rw [linearIter_succ, linearIter_centeredDegree_compl_decomp hW i j,
        map_add, map_smul]
      change
        (c13FrontierCoefficient hW i * complementEigenvalue hW i ^ j) •
            centeredGraphonOp (isGraphon_compl hW) (centeredEigenmode hW i) +
          centeredGraphonOp (isGraphon_compl hW)
            (linearIter (centeredGraphonOp (isGraphon_compl hW)).toLinearMap j
              (c13SafeVector hW i)) = _
      rw [centeredGraphonOp_compl_frontier_eigen hW i]
      change
        (c13FrontierCoefficient hW i * complementEigenvalue hW i ^ j) •
            (complementEigenvalue hW i • centeredEigenmode hW i) +
          linearIter (centeredGraphonOp (isGraphon_compl hW)).toLinearMap (j + 1)
            (c13SafeVector hW i) = _
      rw [pow_succ]
      congr 1
      simp only [smul_smul]
      ring_nf

theorem specMoment_compl_frontier_decomp
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW) (j : ℕ) :
    specMoment (compl W) μ j =
      c13FrontierCoefficient hW i ^ 2 * complementEigenvalue hW i ^ j +
        inner ℝ (c13SafeVector hW i)
          (linearIter (centeredGraphonOp (isGraphon_compl hW)).toLinearMap j
            (c13SafeVector hW i)) := by
  rw [← inner_linearIter_centeredGraphonOp_eq_specMoment (isGraphon_compl hW) j,
    linearIter_centeredDegree_compl_decomp hW i j]
  have hg : centeredDegreeL2 (isGraphon_compl hW) =
      c13FrontierCoefficient hW i • centeredEigenmode hW i +
        c13SafeVector hW i := by
    dsimp [c13SafeVector]
    abel
  have hgsphi : inner ℝ (c13SafeVector hW i) (centeredEigenmode hW i) = 0 :=
    inner_c13SafeVector_frontier hW i
  have hitphi : inner ℝ
      (linearIter (centeredGraphonOp (isGraphon_compl hW)).toLinearMap j
      (c13SafeVector hW i)) (centeredEigenmode hW i) = 0 :=
    inner_linearIter_c13SafeVector_frontier hW i j
  have hphiit : inner ℝ (centeredEigenmode hW i)
      (linearIter (centeredGraphonOp (isGraphon_compl hW)).toLinearMap j
        (c13SafeVector hW i)) = 0 := by
    rw [real_inner_comm]
    exact hitphi
  have hphigs : inner ℝ (centeredEigenmode hW i) (c13SafeVector hW i) = 0 := by
    rw [real_inner_comm]
    exact hgsphi
  have hnormphi : inner ℝ (centeredEigenmode hW i) (centeredEigenmode hW i) = 1 := by
    rw [real_inner_self_eq_norm_sq,
      (centeredEigenmode_orthonormal hW).norm_eq_one i]
    norm_num
  rw [hg, inner_add_left, inner_add_right]
  simp only [real_inner_smul_left, real_inner_smul_right, hphiit, hitphi,
    hgsphi, hphigs, hnormphi, mul_zero, zero_mul, mul_one, add_zero, zero_add]
  rw [inner_add_right, real_inner_smul_right, hgsphi, mul_zero, zero_add]
  ring

abbrev C13SafeIndex (hW : IsGraphon W μ) (i : CenteredEigenIndex hW) :=
  Fin (Module.finrank ℝ
    (krylovSubspace (centeredGraphonOp (isGraphon_compl hW))
      (c13SafeVector hW i) 13))

noncomputable def c13SafeAtomEigenvalue
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW) :
    C13SafeIndex hW i → ℝ :=
  finiteAtomEigenvalue
    (krylovCompression (centeredGraphonOp (isGraphon_compl hW))
      (c13SafeVector hW i) 13).toLinearMap
    (krylovCompression_isSymmetric _ _ _
      (centeredGraphonOp_isSymmetric (isGraphon_compl hW)))

noncomputable def c13SafeAtomWeight
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW) :
    C13SafeIndex hW i → ℝ :=
  finiteAtomWeight
    (krylovCompression (centeredGraphonOp (isGraphon_compl hW))
      (c13SafeVector hW i) 13).toLinearMap
    (krylovCompression_isSymmetric _ _ _
      (centeredGraphonOp_isSymmetric (isGraphon_compl hW)))
    (krylovVector (centeredGraphonOp (isGraphon_compl hW))
      (c13SafeVector hW i) 13)

noncomputable def c13FrontierAtomEigenvalue
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW) :
    Option (C13SafeIndex hW i) → ℝ
  | none => complementEigenvalue hW i
  | some k => c13SafeAtomEigenvalue hW i k

noncomputable def c13FrontierAtomWeight
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW) :
    Option (C13SafeIndex hW i) → ℝ
  | none => c13FrontierCoefficient hW i ^ 2
  | some k => c13SafeAtomWeight hW i k

theorem c13FrontierAtomWeight_nonneg
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW) :
    ∀ k, 0 ≤ c13FrontierAtomWeight hW i k := by
  intro k
  cases k with
  | none => exact sq_nonneg _
  | some k => exact finiteAtomWeight_nonneg _ _ _ k

theorem specMoment_compl_eq_c13FrontierAtomicMoment
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW)
    {j : ℕ} (hj : j ≤ 13) :
    specMoment (compl W) μ j =
      atomicMoment (c13FrontierAtomWeight hW i)
        (c13FrontierAtomEigenvalue hW i) j := by
  rw [specMoment_compl_frontier_decomp hW i j]
  have hsafe := inner_linearIter_eq_krylovAtomicMoment
    (centeredGraphonOp (isGraphon_compl hW)) (c13SafeVector hW i)
    (centeredGraphonOp_isSymmetric (isGraphon_compl hW)) hj
  rw [hsafe]
  unfold atomicMoment
  rw [Fintype.sum_option]
  rfl

/-! ## Safe support -/

theorem frontierSafeRadius_le_seven_fiftieth
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW)
    (hqlo : 481 / 1000 ≤ 1 - edgeDensity W μ)
    (hfront : 1 - edgeDensity W μ < complementEigenvalue hW i) :
    frontierSafeRadius hW i ≤ 7 / 50 := by
  let q := 1 - edgeDensity W μ
  let alpha := complementEigenvalue hW i
  let L := frontierSafeRadius hW i
  have hq0 : 0 ≤ q := by dsimp [q] at *; linarith
  have halpha0 : 0 ≤ alpha := by dsimp [alpha, q] at *; linarith
  have hL0 : 0 ≤ L := by
    exact frontierSafeRadius_nonneg hW i
  have hLsq : L ^ 2 = (1 - q) * q - alpha ^ 2 := by
    simpa [L, q, alpha] using frontierSafeRadius_sq hW i
  have halphaSq : q ^ 2 ≤ alpha ^ 2 :=
    pow_le_pow_left₀ hq0 (le_of_lt hfront) 2
  have hfactor0 : 0 ≤ q - 481 / 1000 := by
    dsimp [q] at *
    linarith
  have hfactor1 : 0 ≤ 2 * q - 19 / 500 := by
    dsimp [q] at *
    linarith
  have hproduct : 0 ≤ (q - 481 / 1000) * (2 * q - 19 / 500) :=
    mul_nonneg hfactor0 hfactor1
  have hsafeSq : L ^ 2 ≤ (7 / 50 : ℝ) ^ 2 := by
    norm_num at hproduct ⊢
    nlinarith
  nlinarith [sq_nonneg (L - 7 / 50)]

lemma inner_c13KrylovVector_frontier
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW)
    (v : krylovSubspace (centeredGraphonOp (isGraphon_compl hW))
      (c13SafeVector hW i) 13) :
    inner ℝ (v : Lp ℝ 2 μ) (centeredEigenmode hW i) = 0 := by
  have hv := v.property
  unfold krylovSubspace at hv
  refine Submodule.span_induction
    (s := Set.range fun j : Fin (13 + 1) =>
      linearIter (centeredGraphonOp (isGraphon_compl hW)).toLinearMap j
        (c13SafeVector hW i)) ?gen ?zero ?add ?smul hv
  · rintro z ⟨j, rfl⟩
    exact inner_linearIter_c13SafeVector_frontier hW i j
  · simp
  · intro x y hx hy hix hiy
    simp [inner_add_left, hix, hiy]
  · intro a x hx hix
    simp [real_inner_smul_left, hix]

theorem c13SafeAtomEigenvalue_mem_halfInterval
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW)
    (k : C13SafeIndex hW i) :
    c13SafeAtomEigenvalue hW i k ∈
      Set.Icc (-(1 : ℝ) / 2) (1 / 2) := by
  exact krylovAtomEigenvalue_mem_halfInterval
    (centeredGraphonOp (isGraphon_compl hW)) (c13SafeVector hW i) 13
    (centeredGraphonOp_isSymmetric (isGraphon_compl hW))
    (norm_centeredGraphonOp_le_half (isGraphon_compl hW)) k

private theorem krylovAtomEigenvalue_le_of_quadratic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (g : E) (d : ℕ)
    (hT : T.toLinearMap.IsSymmetric) (L : ℝ)
    (hquad : ∀ v : krylovSubspace T g d,
      inner ℝ (v : E) (T (v : E)) ≤ L * inner ℝ (v : E) (v : E))
    (k : Fin (Module.finrank ℝ (krylovSubspace T g d))) :
    finiteAtomEigenvalue (krylovCompression T g d).toLinearMap
      (krylovCompression_isSymmetric T g d hT) k ≤ L := by
  let C := krylovCompression T g d
  let hC := krylovCompression_isSymmetric T g d hT
  let b := hC.eigenvectorBasis rfl k
  let lambda := finiteAtomEigenvalue C.toLinearMap hC k
  have hbNorm : ‖b‖ = 1 := (hC.eigenvectorBasis rfl).orthonormal.norm_eq_one k
  have hbNormE : ‖(b : E)‖ = 1 := hbNorm
  have heigen : C b = lambda • b := by
    change C.toLinearMap (hC.eigenvectorBasis rfl k) =
      hC.eigenvalues rfl k • hC.eigenvectorBasis rfl k
    exact hC.apply_eigenvectorBasis rfl k
  have hcompressionPair : inner ℝ b (C b) = lambda := by
    rw [heigen, real_inner_smul_right, real_inner_self_eq_norm_sq, hbNorm]
    ring
  have horiginalPair : inner ℝ (b : E) (T (b : E)) = lambda := by
    calc
      inner ℝ (b : E) (T (b : E)) =
          inner ℝ (b : E)
            ((krylovSubspace T g d).orthogonalProjectionOnto (T (b : E))) := by
              exact ((krylovSubspace T g d).inner_orthogonalProjectionOnto_eq_of_mem_left
                b (T (b : E))).symm
      _ = inner ℝ b (C b) := rfl
      _ = lambda := hcompressionPair
  calc
    finiteAtomEigenvalue (krylovCompression T g d).toLinearMap
        (krylovCompression_isSymmetric T g d hT) k = lambda := rfl
    _ = inner ℝ (b : E) (T (b : E)) := horiginalPair.symm
    _ ≤ L * inner ℝ (b : E) (b : E) := hquad b
    _ = L := by rw [real_inner_self_eq_norm_sq, hbNormE]; ring

theorem c13SafeAtomEigenvalue_le_safeRadius
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW)
    (k : C13SafeIndex hW i) :
    c13SafeAtomEigenvalue hW i k ≤ frontierSafeRadius hW i := by
  apply krylovAtomEigenvalue_le_of_quadratic
    (centeredGraphonOp (isGraphon_compl hW)) (c13SafeVector hW i) 13
    (centeredGraphonOp_isSymmetric (isGraphon_compl hW))
    (frontierSafeRadius hW i) _ k
  intro v
  have horth : inner ℝ (v : Lp ℝ 2 μ) (centeredEigenmode hW i) = 0 :=
    inner_c13KrylovVector_frontier hW i v
  have hsafe := complementCompression_quadratic_le_safeRadius hW i horth
  have haction : centeredGraphonOp (isGraphon_compl hW) (v : Lp ℝ 2 μ) =
      -centeredGraphonOp hW (v : Lp ℝ 2 μ) := by
    simpa using congrArg (fun T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => T (v : Lp ℝ 2 μ))
      (centeredGraphonOp_compl_eq_neg hW)
  rw [haction]
  simpa [inner_neg_right] using hsafe

theorem c13SafeAtomEigenvalue_mem_safeInterval
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW)
    (hqlo : 481 / 1000 ≤ 1 - edgeDensity W μ)
    (hfront : 1 - edgeDensity W μ < complementEigenvalue hW i)
    (k : C13SafeIndex hW i) :
    c13SafeAtomEigenvalue hW i k ∈
      Set.Icc (-(1 : ℝ) / 2) (7 / 50) := by
  exact ⟨(c13SafeAtomEigenvalue_mem_halfInterval hW i k).1,
    (c13SafeAtomEigenvalue_le_safeRadius hW i k).trans
      (frontierSafeRadius_le_seven_fiftieth hW i hqlo hfront)⟩

/-- Every atom in the frontier-plus-Krylov representation is either the
distinguished frontier atom or lies in the certified safe interval. -/
theorem c13FrontierAtomEigenvalue_frontier_or_safe
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW)
    (hqlo : 481 / 1000 ≤ 1 - edgeDensity W μ)
    (hfront : 1 - edgeDensity W μ < complementEigenvalue hW i)
    (k : Option (C13SafeIndex hW i)) :
    c13FrontierAtomEigenvalue hW i k = complementEigenvalue hW i ∨
      c13FrontierAtomEigenvalue hW i k ∈ Set.Icc (-(1 : ℝ) / 2) (7 / 50) := by
  cases k with
  | none => exact Or.inl rfl
  | some k => exact Or.inr (c13SafeAtomEigenvalue_mem_safeInterval hW i hqlo hfront k)

/-- All frontier-plus-Krylov atoms remain in the universal centered-operator
spectral interval. -/
theorem c13FrontierAtomEigenvalue_mem_halfInterval
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW)
    (k : Option (C13SafeIndex hW i)) :
    c13FrontierAtomEigenvalue hW i k ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) := by
  cases k with
  | none =>
      have habs := abs_complementEigenvalue_le_half hW i
      change complementEigenvalue hW i ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)
      rw [abs_le] at habs
      constructor <;> linarith
  | some k => exact c13SafeAtomEigenvalue_mem_halfInterval hW i k

end OddCycleBound.RegionII
