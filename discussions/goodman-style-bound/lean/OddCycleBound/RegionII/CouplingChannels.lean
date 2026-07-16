import OddCycleBound.RegionII.SafeFrontier

/-!
# Frontier eigenfunction coupling channels

This file develops the exact complement-graphon block equation used by both
the direct and safe coupling channels in the corrected Region-II proof.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace OddCycleBound.RegionII

open OddCycleBound.HighDensity
open OddCycleBound.LowBand.L2Kernel

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega -> Omega -> Real}

/-- Positive part written algebraically, avoiding any representative-level
case split. -/
def frontierPos (phi : Omega -> Real) (x : Omega) : Real :=
  (|phi x| + phi x) / 2

noncomputable def frontierAbsMean (mu : Measure Omega)
    (phi : Omega -> Real) : Real :=
  ∫ x, |phi x| ∂mu

noncomputable def frontierShapeZ (mu : Measure Omega)
    (phi : Omega -> Real) : Real :=
  frontierAbsMean mu phi ^ 2

noncomputable def frontierShapeB (mu : Measure Omega)
    (phi : Omega -> Real) : Real :=
  ∫ x, |phi x| * phi x ∂mu

/-- Component of `|phi|` orthogonal to the constant and frontier modes. -/
def frontierResidual (a b : Real) (phi : Omega -> Real) : Omega -> Real :=
  (fun x => |phi x|) - (fun _ => a) - b • phi

lemma good_frontierPos {phi : Omega -> Real} (hphi : Good phi) :
    Good (frontierPos phi) := by
  let h := good_smul ((2 : Real)⁻¹)
    (good_add (good_abs hphi) hphi)
  convert h using 1
  funext x
  simp [frontierPos, Pi.smul_apply, div_eq_mul_inv]
  ring

lemma frontierPos_nonneg (phi : Omega -> Real) (x : Omega) :
    0 <= frontierPos phi x := by
  unfold frontierPos
  nlinarith [neg_le_abs (phi x)]

lemma le_frontierPos (phi : Omega -> Real) (x : Omega) :
    phi x <= frontierPos phi x := by
  unfold frontierPos
  nlinarith [le_abs_self (phi x)]

lemma good_frontierResidual {phi : Omega -> Real} (hphi : Good phi)
    (a b : Real) :
    Good (frontierResidual a b phi) := by
  unfold frontierResidual
  exact good_sub
    (good_sub (good_abs hphi) (good_const (Omega := Omega) a))
    (good_smul b hphi)

/-- Testing a graphon transform against the positive part gives the sharp
rank-one upper bound used in the direct channel. -/
lemma integral_frontierPos_mul_kernelOp_le_sq
    (hU : IsGraphon W mu) {phi : Omega -> Real} (hphi : Good phi) :
    (∫ x, frontierPos phi x * kernelOp W mu phi x ∂mu) <=
      (∫ x, frontierPos phi x ∂mu) ^ 2 := by
  let hpos := good_frontierPos hphi
  have hrow : ∀ x : Omega,
      kernelOp W mu phi x <= ∫ y, frontierPos phi y ∂mu := by
    intro x
    calc
      kernelOp W mu phi x <=
          kernelOp W mu (frontierPos phi) x := by
        unfold kernelOp
        refine integral_mono (integrable_Uf hU hphi x)
          (integrable_Uf hU hpos x) ?_
        intro y
        exact mul_le_mul_of_nonneg_left
          (le_frontierPos phi y) (hU.nonneg x y)
      _ <= ∫ y, frontierPos phi y ∂mu := by
        unfold kernelOp
        refine integral_mono (integrable_Uf hU hpos x)
          hpos.integrable ?_
        intro y
        exact mul_le_of_le_one_left
          (frontierPos_nonneg phi y) (hU.le_one x y)
  have hintegrableLeft :
      Integrable (fun x => frontierPos phi x * kernelOp W mu phi x) mu :=
    (hpos.mul (good_kernelOp hU hphi)).integrable
  have hintegrableRight :
      Integrable
        (fun x => (∫ y, frontierPos phi y ∂mu) * frontierPos phi x) mu :=
    ((good_const (Omega := Omega) (∫ y, frontierPos phi y ∂mu)).mul
      hpos).integrable
  calc
    (∫ x, frontierPos phi x * kernelOp W mu phi x ∂mu) <=
        ∫ x, (∫ y, frontierPos phi y ∂mu) *
          frontierPos phi x ∂mu := by
      refine integral_mono hintegrableLeft hintegrableRight ?_
      intro x
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_left (hrow x)
          (frontierPos_nonneg phi x))
    _ = (∫ x, frontierPos phi x ∂mu) ^ 2 := by
      rw [integral_const_mul]
      ring

/-- Complementation negates the centered operator on a bounded mean-zero
representative. -/
theorem centeredGraphonOp_compl_goodL2_eq_neg
    (hW : IsGraphon W mu) {f : Omega -> Real} (hf : Good f)
    (hmean : mean mu f = 0) :
    centeredGraphonOp (isGraphon_compl hW) (goodL2 (mu := mu) hf) =
      -centeredGraphonOp hW (goodL2 (mu := mu) hf) := by
  let P := centerProjection (Omega := Omega) (mu := mu)
  have hcenter : P (goodL2 (mu := mu) hf) = goodL2 (mu := mu) hf :=
    centerProjection_apply_of_mean_zero hf hmean
  have hkernel :
      kernelOpCLM (mu := mu) (isGraphon_compl hW)
          (goodL2 (mu := mu) hf) =
        -kernelOpCLM (mu := mu) hW (goodL2 (mu := mu) hf) := by
    rw [kernelOpCLM_goodL2_eq_goodL2, kernelOpCLM_goodL2_eq_goodL2]
    let hU := good_kernelOp (isGraphon_compl hW) hf
    let hneg := good_smul (-1 : Real) (good_kernelOp hW hf)
    have heq :
        goodL2 (mu := mu) hU = goodL2 (mu := mu) hneg := by
      apply MemLp.toLp_congr
        (good_memLp_two hU) (good_memLp_two hneg)
      exact ae_of_all _ fun x => by
        change kernelOp (compl W) mu f x =
          (-1 : Real) * kernelOp W mu f x
        rw [kernelOp_compl hW hf x, hmean]
        ring
    rw [heq, goodL2_smul (-1 : Real) (good_kernelOp hW hf)]
    simp
  unfold centeredGraphonOp
  change P
      (kernelOpCLM (mu := mu) (isGraphon_compl hW)
        (P (goodL2 (mu := mu) hf))) =
    -P
      (kernelOpCLM (mu := mu) hW
        (P (goodL2 (mu := mu) hf)))
  rw [hcenter, hkernel, map_neg]

/-- Exact block equation
`T_(1-W) phi = c 1 + alpha phi` for a centered frontier eigenmode. -/
theorem kernelOpCLM_compl_frontier_eq_hub_add
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    {phi : Omega -> Real} (hphi : Good phi)
    (hrep : centeredEigenmode hW i = goodL2 (mu := mu) hphi)
    (hmean : mean mu phi = 0) :
    let hU := isGraphon_compl hW
    let c := inner Real (centeredDegreeL2 hU) (centeredEigenmode hW i)
    kernelOpCLM (mu := mu) hU (centeredEigenmode hW i) =
      c • oneL2 (Omega := Omega) mu +
        complementEigenvalue hW i • centeredEigenmode hW i := by
  dsimp only
  let one := oneL2 (Omega := Omega) mu
  let P := centerProjection (Omega := Omega) (mu := mu)
  let T := kernelOpCLM (mu := mu) (isGraphon_compl hW)
  let v := centeredEigenmode hW i
  let c := inner Real (centeredDegreeL2 (isGraphon_compl hW)) v
  have hvcenter : P v = v := by
    dsimp [P, v]
    rw [hrep]
    exact centerProjection_apply_of_mean_zero hphi hmean
  have hcoefficient : inner Real one (T v) = c := by
    have hT : T.toLinearMap.IsSymmetric :=
      kernelOpCLM_isSymmetric (isGraphon_compl hW)
    have hP : P.toLinearMap.IsSymmetric :=
      centerProjection_isSymmetric
    calc
      inner Real one (T v) = inner Real (T one) v :=
        (hT.apply_clm one v).symm
      _ = inner Real (P (T one)) v := by
        rw [hP.apply_clm, hvcenter]
      _ = inner Real (centeredDegreeL2 (isGraphon_compl hW)) v := by
        dsimp [one, T, P]
        rw [centerProjection_kernelOpCLM_one_eq_centeredDegreeL2]
      _ = c := rfl
  have hbody : P (T v) = complementEigenvalue hW i • v := by
    have hcomp :
        centeredGraphonOp (isGraphon_compl hW) v =
          -centeredGraphonOp hW v := by
      dsimp [v]
      rw [hrep]
      exact centeredGraphonOp_compl_goodL2_eq_neg hW hphi hmean
    calc
      P (T v) = centeredGraphonOp (isGraphon_compl hW) v := by
        unfold centeredGraphonOp
        change P (T v) = P (T (P v))
        rw [hvcenter]
      _ = -centeredGraphonOp hW v := hcomp
      _ = complementEigenvalue hW i • v := by
        rw [centeredEigenmode_diagonal]
        simp [complementEigenvalue, v]
  have hdecomp : T v = inner Real one (T v) • one + P (T v) := by
    dsimp [P]
    unfold centerProjection
    simp only [sub_apply, one_apply_eq_self,
      InnerProductSpace.rankOne_apply]
    abel
  simpa [one, T, v, c, hcoefficient, hbody] using hdecomp

/-- Direct frontier coupling channel, in denominator-free form:
`2 c sqrt(z) + 2 alpha b <= z - 2 alpha`. -/
theorem frontier_direct_channel
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    {phi : Omega -> Real} (hphi : Good phi)
    (hrep : centeredEigenmode hW i = goodL2 (mu := mu) hphi)
    (hmean : mean mu phi = 0)
    (hnorm : (∫ x, phi x * phi x ∂mu) = 1) :
    let hU := isGraphon_compl hW
    let alpha := complementEigenvalue hW i
    let z := frontierShapeZ mu phi
    let b := frontierShapeB mu phi
    let c := inner Real (centeredDegreeL2 hU) (centeredEigenmode hW i)
    2 * c * Real.sqrt z + 2 * alpha * b <= z - 2 * alpha := by
  dsimp only
  let hU := isGraphon_compl hW
  let alpha := complementEigenvalue hW i
  let a := frontierAbsMean mu phi
  let z := frontierShapeZ mu phi
  let b := frontierShapeB mu phi
  let c := inner Real (centeredDegreeL2 hU) (centeredEigenmode hW i)
  let hpos : Good (frontierPos phi) := good_frontierPos hphi
  let posVec := goodL2 (mu := mu) hpos
  have ha0 : 0 <= a := by
    dsimp [a, frontierAbsMean]
    exact integral_nonneg fun x => abs_nonneg (phi x)
  have hz : z = a ^ 2 := rfl
  have hsqrtZ : Real.sqrt z = a := by
    rw [hz, Real.sqrt_sq ha0]
  have hmeanPos : mean mu (frontierPos phi) = a / 2 := by
    unfold mean frontierPos
    rw [integral_div, integral_add (good_abs hphi).integrable hphi.integrable]
    change ((∫ x, |phi x| ∂mu) + ∫ x, phi x ∂mu) / 2 = a / 2
    rw [show (∫ x, phi x ∂mu) = 0 by simpa [mean] using hmean]
    simp [a, frontierAbsMean]
  have hinnerPosPhi :
      inner Real posVec (centeredEigenmode hW i) = (b + 1) / 2 := by
    rw [hrep]
    dsimp [posVec]
    rw [inner_goodL2_eq_integral_mul]
    unfold frontierPos
    have hpoint :
        (fun x : Omega => (|phi x| + phi x) / 2 * phi x) =
          fun x => (|phi x| * phi x + phi x * phi x) / 2 := by
      funext x
      ring
    rw [hpoint, integral_div]
    rw [integral_add
      ((good_abs hphi).mul hphi).integrable
      (hphi.mul hphi).integrable, hnorm]
    simp [b, frontierShapeB]
  have hinnerPosOne :
      inner Real posVec (oneL2 (Omega := Omega) mu) = a / 2 := by
    rw [real_inner_comm]
    dsimp [posVec]
    rw [inner_oneL2_goodL2_eq_mean]
    exact hmeanPos
  have hblock := kernelOpCLM_compl_frontier_eq_hub_add
    hW i hphi hrep hmean
  have hpairBlock := congrArg (fun v => inner Real posVec v) hblock
  have hpairEq :
      (∫ x, frontierPos phi x *
          kernelOp (compl W) mu phi x ∂mu) =
        c * (a / 2) + alpha * ((b + 1) / 2) := by
    rw [hrep, kernelOpCLM_goodL2_eq_goodL2] at hpairBlock
    change inner Real posVec
        (goodL2 (mu := mu) (good_kernelOp (isGraphon_compl hW) hphi)) =
      _ at hpairBlock
    rw [inner_goodL2_eq_integral_mul] at hpairBlock
    simp only [inner_add_right, real_inner_smul_right] at hpairBlock
    rw [← hrep] at hpairBlock
    rw [hinnerPosOne, hinnerPosPhi] at hpairBlock
    simpa [c, alpha] using hpairBlock
  have hdom := integral_frontierPos_mul_kernelOp_le_sq
    (isGraphon_compl hW) hphi
  rw [hpairEq] at hdom
  have hposIntegral :
      (∫ x, frontierPos phi x ∂mu) = a / 2 := by
    simpa [mean] using hmeanPos
  rw [hposIntegral] at hdom
  change 2 * c * Real.sqrt z + 2 * alpha * b <= z - 2 * alpha
  rw [hsqrtZ, hz]
  nlinarith [hdom]

/-- The direct channel for the opposite frontier orientation.  Together with
`frontier_direct_channel`, this permits choosing the sign for which the cubic
shape coefficient is nonnegative. -/
theorem frontier_direct_channel_neg
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    {phi : Omega -> Real} (hphi : Good phi)
    (hrep : centeredEigenmode hW i = goodL2 (mu := mu) hphi)
    (hmean : mean mu phi = 0)
    (hnorm : (∫ x, phi x * phi x ∂mu) = 1) :
    let hU := isGraphon_compl hW
    let alpha := complementEigenvalue hW i
    let z := frontierShapeZ mu phi
    let b := frontierShapeB mu phi
    let c := inner Real (centeredDegreeL2 hU) (centeredEigenmode hW i)
    (-2 * c * Real.sqrt z - 2 * alpha * b <= z - 2 * alpha) := by
  dsimp only
  let hU := isGraphon_compl hW
  let alpha := complementEigenvalue hW i
  let a := frontierAbsMean mu phi
  let z := frontierShapeZ mu phi
  let b := frontierShapeB mu phi
  let c := inner Real (centeredDegreeL2 hU) (centeredEigenmode hW i)
  let psi : Omega -> Real := fun x => -phi x
  let hpsi : Good psi := good_neg hphi
  let hpos : Good (frontierPos psi) := good_frontierPos hpsi
  let posVec := goodL2 (mu := mu) hpos
  have ha0 : 0 <= a := by
    dsimp [a, frontierAbsMean]
    exact integral_nonneg fun x => abs_nonneg (phi x)
  have hz : z = a ^ 2 := rfl
  have hsqrtZ : Real.sqrt z = a := by
    rw [hz, Real.sqrt_sq ha0]
  have hmeanPos : mean mu (frontierPos psi) = a / 2 := by
    unfold mean frontierPos
    have habsPsi : (fun x : Omega => |psi x|) = fun x => |phi x| := by
      funext x
      simp [psi]
    rw [integral_div, integral_add (good_abs hpsi).integrable hpsi.integrable]
    rw [habsPsi]
    have hpsiMean : (∫ x, psi x ∂mu) = 0 := by
      change (∫ x, -phi x ∂mu) = 0
      rw [integral_neg]
      simpa [mean] using congrArg Neg.neg hmean
    rw [hpsiMean]
    simp [a, frontierAbsMean]
  have hinnerPosPhi :
      inner Real posVec (centeredEigenmode hW i) = (b - 1) / 2 := by
    rw [hrep]
    dsimp [posVec]
    rw [inner_goodL2_eq_integral_mul]
    have hpoint :
        (fun x : Omega => frontierPos psi x * phi x) =
          fun x => (|phi x| * phi x - phi x * phi x) / 2 := by
      funext x
      simp [frontierPos, psi]
      ring
    rw [hpoint, integral_div]
    rw [integral_sub
      ((good_abs hphi).mul hphi).integrable
      (hphi.mul hphi).integrable, hnorm]
    simp [b, frontierShapeB]
  have hinnerPosOne :
      inner Real posVec (oneL2 (Omega := Omega) mu) = a / 2 := by
    rw [real_inner_comm]
    dsimp [posVec]
    rw [inner_oneL2_goodL2_eq_mean]
    exact hmeanPos
  have hblock := kernelOpCLM_compl_frontier_eq_hub_add
    hW i hphi hrep hmean
  have hpairBlock := congrArg (fun v => inner Real posVec v) hblock
  have hpairEq :
      (∫ x, frontierPos psi x * kernelOp (compl W) mu phi x ∂mu) =
        c * (a / 2) + alpha * ((b - 1) / 2) := by
    rw [hrep, kernelOpCLM_goodL2_eq_goodL2] at hpairBlock
    change inner Real posVec
        (goodL2 (mu := mu) (good_kernelOp (isGraphon_compl hW) hphi)) =
      _ at hpairBlock
    rw [inner_goodL2_eq_integral_mul] at hpairBlock
    simp only [inner_add_right, real_inner_smul_right] at hpairBlock
    rw [← hrep] at hpairBlock
    rw [hinnerPosOne, hinnerPosPhi] at hpairBlock
    simpa [c, alpha] using hpairBlock
  have hkernelNeg : forall x : Omega,
      kernelOp (compl W) mu psi x = -kernelOp (compl W) mu phi x := by
    intro x
    unfold kernelOp
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp [psi]
  have hleftNeg :
      (∫ x, frontierPos psi x * kernelOp (compl W) mu psi x ∂mu) =
        -(∫ x, frontierPos psi x * kernelOp (compl W) mu phi x ∂mu) := by
    simp_rw [hkernelNeg]
    have hpoint : (fun x : Omega => frontierPos psi x *
        -kernelOp (compl W) mu phi x) =
      fun x => -(frontierPos psi x * kernelOp (compl W) mu phi x) := by
      funext x
      ring
    rw [hpoint, integral_neg]
  have hdom := integral_frontierPos_mul_kernelOp_le_sq
    (isGraphon_compl hW) hpsi
  rw [hleftNeg, hpairEq] at hdom
  have hposIntegral : (∫ x, frontierPos psi x ∂mu) = a / 2 := by
    simpa [mean] using hmeanPos
  rw [hposIntegral] at hdom
  change -2 * c * Real.sqrt z - 2 * alpha * b <= z - 2 * alpha
  rw [hsqrtZ, hz]
  nlinarith [hdom]

/-- Safe frontier coupling channel.  The first conjunct is the exact shape
budget `z+b^2+K=1`; the second is the denominator-free form of
`b c + <g_s,k> >= H`. -/
theorem frontier_safe_channel
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    {phi : Omega -> Real} (hphi : Good phi)
    (hrep : centeredEigenmode hW i = goodL2 (mu := mu) hphi)
    (hmean : mean mu phi = 0)
    (hnorm : (∫ x, phi x * phi x ∂mu) = 1)
    (halpha : 0 < complementEigenvalue hW i)
    (hzalpha : 2 * complementEigenvalue hW i <=
      frontierShapeZ mu phi) :
    let hU := isGraphon_compl hW
    let alpha := complementEigenvalue hW i
    let q := edgeDensity (compl W) mu
    let L := frontierSafeRadius hW i
    let a := frontierAbsMean mu phi
    let z := frontierShapeZ mu phi
    let b := frontierShapeB mu phi
    let kVec := goodL2 (mu := mu)
      (good_frontierResidual hphi a b)
    let K := ‖kVec‖ ^ 2
    let c := inner Real (centeredDegreeL2 hU) (centeredEigenmode hW i)
    let gs := centeredDegreeL2 hU - c • centeredEigenmode hW i
    z + b ^ 2 + K = 1 ∧
      (alpha - q) * z + (alpha - L) * K <=
        2 * Real.sqrt z *
          (b * c + inner Real gs kVec) := by
  dsimp only
  let hU := isGraphon_compl hW
  let alpha := complementEigenvalue hW i
  let q := edgeDensity (compl W) mu
  let L := frontierSafeRadius hW i
  let a := frontierAbsMean mu phi
  let z := frontierShapeZ mu phi
  let b := frontierShapeB mu phi
  let hk : Good (frontierResidual a b phi) :=
    good_frontierResidual hphi a b
  let kVec := goodL2 (mu := mu) hk
  let phiVec := centeredEigenmode hW i
  let absVec := goodL2 (mu := mu) (good_abs hphi)
  let one := oneL2 (Omega := Omega) mu
  let K := ‖kVec‖ ^ 2
  let c := inner Real (centeredDegreeL2 hU) phiVec
  let gs := centeredDegreeL2 hU - c • phiVec
  have ha0 : 0 <= a := by
    dsimp [a, frontierAbsMean]
    exact integral_nonneg fun x => abs_nonneg (phi x)
  have hz : z = a ^ 2 := rfl
  have hsqrtZ : Real.sqrt z = a := by
    rw [hz, Real.sqrt_sq ha0]
  have hphiNorm : ‖phiVec‖ = 1 := by
    dsimp [phiVec]
    exact (centeredEigenmode_orthonormal hW).norm_eq_one i
  have honeNorm : ‖one‖ = 1 := by
    dsimp [one]
    have hs := norm_oneL2_sq (Omega := Omega) (mu := mu)
    nlinarith [norm_nonneg (oneL2 (Omega := Omega) mu)]
  have honePhi : inner Real one phiVec = 0 := by
    dsimp [one, phiVec]
    rw [hrep, inner_oneL2_goodL2_eq_mean, hmean]
  have hphiAbs : inner Real phiVec absVec = b := by
    dsimp [phiVec, absVec]
    rw [hrep, inner_goodL2_eq_integral_mul]
    simpa [b, frontierShapeB, mul_comm]
  have honeAbs : inner Real one absVec = a := by
    dsimp [one, absVec]
    rw [inner_oneL2_goodL2_eq_mean]
    rfl
  have habsNormSq : ‖absVec‖ ^ 2 = 1 := by
    dsimp [absVec]
    rw [norm_goodL2_sq_eq_integral_mul]
    calc
      (∫ x, |phi x| * |phi x| ∂mu) =
          ∫ x, phi x * phi x ∂mu := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        change |phi x| * |phi x| = phi x * phi x
        rw [← pow_two, ← pow_two, sq_abs]
      _ = 1 := hnorm
  have hkVecEq : kVec = absVec - a • one - b • phiVec := by
    let hk' := good_sub
      (good_sub (good_abs hphi) (good_const (Omega := Omega) a))
      (good_smul b hphi)
    have hkToLp :
        goodL2 (mu := mu) hk = goodL2 (mu := mu) hk' := by
      apply MemLp.toLp_congr
        (good_memLp_two hk) (good_memLp_two hk')
      exact ae_of_all _ fun x => by
        simp [frontierResidual, Pi.smul_apply, smul_eq_mul]
    calc
      kVec = goodL2 (mu := mu) hk' := hkToLp
      _ = goodL2 (mu := mu)
            (good_sub (good_abs hphi)
              (good_const (Omega := Omega) a)) -
          goodL2 (mu := mu) (good_smul b hphi) := by
            exact goodL2_sub
              (good_sub (good_abs hphi)
                (good_const (Omega := Omega) a))
              (good_smul b hphi)
      _ = (goodL2 (mu := mu) (good_abs hphi) -
            goodL2 (mu := mu) (good_const (Omega := Omega) a)) -
          goodL2 (mu := mu) (good_smul b hphi) := by
            rw [goodL2_sub (good_abs hphi)
              (good_const (Omega := Omega) a)]
      _ = absVec - a • one - b • phiVec := by
            rw [goodL2_const a, goodL2_smul b hphi, ← hrep]
  have honeK : inner Real one kVec = 0 := by
    rw [hkVecEq]
    simp only [inner_sub_right, inner_smul_right]
    rw [honeAbs, real_inner_self_eq_norm_sq, honeNorm, honePhi]
    simp
  have hphiK : inner Real phiVec kVec = 0 := by
    rw [hkVecEq]
    simp only [inner_sub_right, inner_smul_right]
    rw [hphiAbs, real_inner_comm one phiVec, honePhi,
      real_inner_self_eq_norm_sq, hphiNorm]
    simp
  have habsDecomp : absVec = a • one + b • phiVec + kVec := by
    rw [hkVecEq]
    abel
  have hshape : z + b ^ 2 + K = 1 := by
    have hphiOne : inner Real phiVec one = 0 := by
      rw [real_inner_comm, honePhi]
    have hkOne : inner Real kVec one = 0 := by
      rw [real_inner_comm, honeK]
    have hkPhi : inner Real kVec phiVec = 0 := by
      rw [real_inner_comm, hphiK]
    have hinner := congrArg (fun v => inner Real v v) habsDecomp
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right] at hinner
    rw [real_inner_self_eq_norm_sq, habsNormSq,
      real_inner_self_eq_norm_sq, honeNorm,
      real_inner_self_eq_norm_sq, hphiNorm,
      real_inner_self_eq_norm_sq, honePhi,
      hphiOne, honeK, hkOne, hphiK, hkPhi] at hinner
    dsimp [K]
    rw [hz]
    nlinarith
  have hkMean : mean mu (frontierResidual a b phi) = 0 := by
    have h := honeK
    dsimp [one, kVec] at h
    rw [inner_oneL2_goodL2_eq_mean] at h
    exact h
  have hkCenter :
      centerProjection (Omega := Omega) (mu := mu) kVec = kVec := by
    dsimp [kVec]
    exact centerProjection_apply_of_mean_zero hk hkMean
  have hphiCenter :
      centerProjection (Omega := Omega) (mu := mu) phiVec = phiVec := by
    dsimp [phiVec]
    rw [hrep]
    exact centerProjection_apply_of_mean_zero hphi hmean
  have hhCenter :
      centerProjection (Omega := Omega) (mu := mu)
          (b • phiVec + kVec) = b • phiVec + kVec := by
    rw [map_add, map_smul, hphiCenter, hkCenter]
  have hgsK :
      inner Real (centeredDegreeL2 hU) kVec =
        inner Real gs kVec := by
    dsimp [gs]
    rw [inner_sub_left, real_inner_smul_left, hphiK]
    ring
  have hgBody :
      inner Real (centeredDegreeL2 hU) (b • phiVec + kVec) =
        b * c + inner Real gs kVec := by
    rw [inner_add_right, inner_smul_right, hgsK]
  have hAphi :
      centeredGraphonOp hU phiVec = alpha • phiVec := by
    have hcomp :
        centeredGraphonOp hU phiVec =
          -centeredGraphonOp hW phiVec := by
      dsimp [hU, phiVec]
      rw [hrep]
      exact centeredGraphonOp_compl_goodL2_eq_neg hW hphi hmean
    rw [hcomp, centeredEigenmode_diagonal]
    simp [alpha, complementEigenvalue, phiVec]
  have hbodyExact :
      inner Real (b • phiVec + kVec)
          (centeredGraphonOp hU (b • phiVec + kVec)) =
        alpha * b ^ 2 +
          inner Real kVec (centeredGraphonOp hU kVec) := by
    have hsymm := (centeredGraphonOp_isSymmetric hU).apply_clm
    rw [map_add, map_smul, hAphi]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    have hcross :
        inner Real phiVec (centeredGraphonOp hU kVec) = 0 := by
      calc
        inner Real phiVec (centeredGraphonOp hU kVec) =
            inner Real (centeredGraphonOp hU phiVec) kVec :=
          (hsymm phiVec kVec).symm
        _ = 0 := by rw [hAphi, inner_smul_left, hphiK, mul_zero]
    have hkPhi : inner Real kVec phiVec = 0 := by
      rw [real_inner_comm, hphiK]
    rw [hcross, hkPhi, real_inner_self_eq_norm_sq, hphiNorm]
    ring
  have hbodySafe :
      inner Real kVec (centeredGraphonOp hU kVec) <= L * K := by
    have hcomp :
        inner Real kVec (centeredGraphonOp hU kVec) =
          -inner Real kVec (centeredGraphonOp hW kVec) := by
      dsimp [kVec, hU]
      exact inner_centeredGraphonOp_compl_goodL2_eq_neg
        hW hk hkMean
    rw [hcomp]
    have hsafe := complementCompression_quadratic_le_safeRadius
      hW i (by rw [real_inner_comm, hphiK])
    rw [real_inner_self_eq_norm_sq] at hsafe
    exact hsafe
  have habsDecomp' : absVec = a • one + (b • phiVec + kVec) := by
    rw [habsDecomp]
    abel
  have hquadBlock := graphon_quadratic_block hU
    (v := absVec) (h := b • phiVec + kVec) (a := a)
    habsDecomp' hhCenter
  have hquadUpper :
      inner Real absVec
          (kernelOpCLM (mu := mu) hU absVec) <=
        q * z + 2 * a * (b * c + inner Real gs kVec) +
          alpha * b ^ 2 + L * K := by
    rw [hgBody, hbodyExact] at hquadBlock
    dsimp [q]
    rw [hz]
    linarith
  have hquadLower :
      alpha <= inner Real absVec
          (kernelOpCLM (mu := mu) hU absVec) := by
    have hdom := abs_inner_goodL2_kernelOpCLM_self_le_abs
      (mu := mu) hU hphi
    rw [← goodL2_abs hphi] at hdom
    have heigen := inner_centeredEigenmode_kernelOp_compl_eq
      hW i hphi hrep hmean
    rw [← hrep, heigen, abs_of_pos halpha] at hdom
    simpa [absVec, phiVec] using hdom
  constructor
  · exact hshape
  · rw [hsqrtZ]
    nlinarith [hquadLower, hquadUpper]

/-- Cauchy--Schwarz form of the safe channel.  It is stated without division
by `K`, so it includes the corrected degenerate case `K = 0`. -/
theorem frontier_safe_channel_sq
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    {phi : Omega -> Real} (hphi : Good phi)
    (hrep : centeredEigenmode hW i = goodL2 (mu := mu) hphi)
    (hmean : mean mu phi = 0)
    (hnorm : (∫ x, phi x * phi x ∂mu) = 1)
    (halpha : 0 < complementEigenvalue hW i)
    (hzalpha : 2 * complementEigenvalue hW i <=
      frontierShapeZ mu phi) :
    let hU := isGraphon_compl hW
    let alpha := complementEigenvalue hW i
    let q := edgeDensity (compl W) mu
    let L := frontierSafeRadius hW i
    let a := frontierAbsMean mu phi
    let z := frontierShapeZ mu phi
    let b := frontierShapeB mu phi
    let kVec := goodL2 (mu := mu)
      (good_frontierResidual hphi a b)
    let K := ‖kVec‖ ^ 2
    let c := inner Real (centeredDegreeL2 hU) (centeredEigenmode hW i)
    let gs := centeredDegreeL2 hU - c • centeredEigenmode hW i
    max
        (((alpha - q) * z + (alpha - L) * K) /
          (2 * Real.sqrt z) - b * c) 0 ^ 2 <=
      ‖gs‖ ^ 2 * K := by
  dsimp only
  let hU := isGraphon_compl hW
  let alpha := complementEigenvalue hW i
  let q := edgeDensity (compl W) mu
  let L := frontierSafeRadius hW i
  let a := frontierAbsMean mu phi
  let z := frontierShapeZ mu phi
  let b := frontierShapeB mu phi
  let hk : Good (frontierResidual a b phi) :=
    good_frontierResidual hphi a b
  let kVec := goodL2 (mu := mu) hk
  let K := ‖kVec‖ ^ 2
  let c := inner Real (centeredDegreeL2 hU) (centeredEigenmode hW i)
  let gs := centeredDegreeL2 hU - c • centeredEigenmode hW i
  have hzpos : 0 < z := by
    dsimp [alpha, z] at *
    nlinarith
  have hsqrtPos : 0 < 2 * Real.sqrt z := by positivity
  have hsafe := (frontier_safe_channel hW i hphi hrep hmean hnorm
    halpha hzalpha).2
  change
    (alpha - q) * z + (alpha - L) * K <=
      2 * Real.sqrt z *
        (b * c + inner Real gs kVec) at hsafe
  have hdiv :
      ((alpha - q) * z + (alpha - L) * K) /
          (2 * Real.sqrt z) <=
        b * c + inner Real gs kVec := by
    apply (div_le_iff₀ hsqrtPos).2
    simpa [mul_comm] using hsafe
  have hinner :
      inner Real gs kVec <= ‖gs‖ * ‖kVec‖ :=
    real_inner_le_norm _ _
  have hmax :
      max
          (((alpha - q) * z + (alpha - L) * K) /
            (2 * Real.sqrt z) - b * c) 0 <=
        ‖gs‖ * ‖kVec‖ := by
    apply max_le
    · linarith
    · positivity
  have hsquared := mul_self_le_mul_self (le_max_right _ _) hmax
  simpa [K, pow_two, mul_assoc, mul_comm, mul_left_comm] using hsquared

end OddCycleBound.RegionII
