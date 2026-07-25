import OddCycleBound.IntermediateRegion.LeadingEigenvalue
import OddCycleBound.IntermediateRegion.Scalar.EigenvalueAlgebra

/-!
# Forced variance at a the intermediate region leading_eigenvalue eigenvalue

This file formalizes the eigenfunction geometry used to force degree
variance.  It begins with the sharp `L¹` version of the centered graphon
quadratic-form estimate and applies it to the bounded representative of a
leading_eigenvalue eigenmode.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.DenseRegion
open OddCycleBound.Spectral.L2Kernel

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega -> Omega -> Real}

/-- Sharp `L¹` form of the mean-zero graphon quadratic estimate.

The two positive majorants supplied by `W` and `1-W` add to
`(integral |f|)^2`.  Mean zero makes their signed quadratic forms opposites,
so each has absolute value at most half of that sum. -/
lemma two_mul_abs_integral_mul_kernelOp_le_integral_abs_sq
    (hW : IsGraphon W mu) {f : Omega -> Real} (hf : Good f)
    (hmean : mean mu f = 0) :
    2 * |∫ x, f x * kernelOp W mu f x ∂mu| <=
      (∫ x, |f x| ∂mu) ^ 2 := by
  let U := compl W
  have hU : IsGraphon U mu := isGraphon_compl hW
  have hdomW :
      |∫ x, f x * kernelOp W mu f x ∂mu| <=
        ∫ x, |f x| * kernelOp W mu (fun y => |f y|) x ∂mu := by
    simpa only [inner_goodL2_kernelOpL2OfGood_eq_integral] using
      (abs_inner_goodL2_kernelOpL2OfGood_self_le_abs (mu := mu) hW hf)
  have hdomU :
      |∫ x, f x * kernelOp U mu f x ∂mu| <=
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
      |∫ x, f x * kernelOp W mu f x ∂mu| <=
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
  linarith

/-- Centering both arguments does not change a graphon quadratic pairing
when the input is already centered. -/
lemma inner_kernelOpCLM_eq_centeredGraphonOp_of_centered
    (hW : IsGraphon W mu) {v : Lp Real 2 mu}
    (hv : centerProjection (Omega := Omega) (mu := mu) v = v) :
    inner Real v (kernelOpCLM (mu := mu) hW v) =
      inner Real v (centeredGraphonOp hW v) := by
  have hP := centerProjection_isSymmetric (Omega := Omega) (mu := mu)
  unfold centeredGraphonOp
  change inner Real v (kernelOpCLM (mu := mu) hW v) =
    inner Real v
      (centerProjection (Omega := Omega) (mu := mu)
        (kernelOpCLM (mu := mu) hW
          (centerProjection (Omega := Omega) (mu := mu) v)))
  rw [hv, ← hP.apply_clm, hv]

/-- A positive complement-leading_eigenvalue eigenvalue forces the square of the
`L¹` norm of its normalized eigenfunction to be at least `2 alpha`.

The representative is returned as part of the statement so later geometry
can use pointwise positive/negative parts without making an arbitrary choice
of an `L²` representative. -/
theorem exists_leadingEigenvalueEigenfunction_with_abs_sq_ge
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    (halpha : 0 < complementEigenvalue hW i) :
    ∃ (phi : Omega -> Real), ∃ hphi : Good phi,
      centeredEigenmode hW i = goodL2 (mu := mu) hphi ∧
      mean mu phi = 0 ∧
      (∫ x, phi x * phi x ∂mu) = 1 ∧
      2 * complementEigenvalue hW i <= (∫ x, |phi x| ∂mu) ^ 2 := by
  rcases exists_good_centeredEigenfunction hW i with
    ⟨phi, hphi, hrep, hmean, hnorm⟩
  have hcenter :
      centerProjection (Omega := Omega) (mu := mu)
          (centeredEigenmode hW i) = centeredEigenmode hW i := by
    rw [hrep]
    exact centerProjection_apply_of_mean_zero hphi hmean
  have hpair :
      (∫ x, phi x * kernelOp W mu phi x ∂mu) =
        centeredEigenvalue hW i := by
    calc
      (∫ x, phi x * kernelOp W mu phi x ∂mu) =
          inner Real (goodL2 (mu := mu) hphi)
            (kernelOpL2OfGood (mu := mu) hW hphi) := by
              symm
              exact inner_goodL2_kernelOpL2OfGood_eq_integral hW hphi hphi
      _ = inner Real (centeredEigenmode hW i)
            (kernelOpCLM (mu := mu) hW (centeredEigenmode hW i)) := by
              rw [hrep, kernelOpCLM_goodL2]
      _ = inner Real (centeredEigenmode hW i)
            (centeredGraphonOp hW (centeredEigenmode hW i)) :=
              inner_kernelOpCLM_eq_centeredGraphonOp_of_centered hW hcenter
      _ = centeredEigenvalue hW i := by
              rw [centeredEigenmode_diagonal, inner_smul_right,
                real_inner_self_eq_norm_sq,
                (centeredEigenmode_orthonormal hW).norm_eq_one]
              norm_num
  have hsharp :=
    two_mul_abs_integral_mul_kernelOp_le_integral_abs_sq hW hphi hmean
  have hsign : centeredEigenvalue hW i = -complementEigenvalue hW i := by
    simp [complementEigenvalue]
  rw [hpair, hsign, abs_neg, abs_of_pos halpha] at hsharp
  exact ⟨phi, hphi, hrep, hmean, hnorm, hsharp⟩

/-- The unique leading_eigenvalue eigenvalue is a global upper bound for the quadratic
form of the complement compression `-P T_W P`.

The proof uses the complete nonzero-mode expansion and Bessel's inequality;
the possible residual in the zero eigenspace contributes exactly zero. -/
theorem complementCompression_quadratic_le_leading_eigenvalue
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    (hqthird : (1 : Real) / 3 < 1 - edgeDensity W mu)
    (hfront : 1 - edgeDensity W mu < complementEigenvalue hW i)
    (halpha0 : 0 <= complementEigenvalue hW i)
    (v : Lp Real 2 mu) :
    -inner Real v (centeredGraphonOp hW v) <=
      complementEigenvalue hW i * inner Real v v := by
  have hquadCentered :
      HasSum
        (fun j : CenteredEigenIndex hW =>
          centeredEigenvalue hW j *
            (inner Real v (centeredEigenmode hW j) ^ 2))
        (inner Real v (centeredGraphonOp hW v)) := by
    have haction := (centeredGraphonOp_action_expansion hW v).mapL
      ((innerSL Real) v)
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using haction
  have hquad :
      HasSum
        (fun j : CenteredEigenIndex hW =>
          complementEigenvalue hW j *
            (inner Real v (centeredEigenmode hW j) ^ 2))
        (-inner Real v (centeredGraphonOp hW v)) := by
    have hneg := hquadCentered.mul_left (-1 : Real)
    simpa [complementEigenvalue, mul_assoc] using hneg
  have hle : ∀ j : CenteredEigenIndex hW,
      complementEigenvalue hW j <= complementEigenvalue hW i := by
    intro j
    by_contra hnot
    have hij : complementEigenvalue hW i < complementEigenvalue hW j :=
      lt_of_not_ge hnot
    have hjfront :
        1 - edgeDensity W mu < complementEigenvalue hW j :=
      hfront.trans hij
    have heq := complement_leading_eigenvalue_unique hW hqthird hfront hjfront
    subst j
    exact (lt_irrefl _ hij)
  have hcoord : Summable (fun j : CenteredEigenIndex hW =>
      inner Real v (centeredEigenmode hW j) ^ 2) :=
    OddCycleBound.Spectral.InfiniteSpectral.summable_inner_sq_of_orthonormal
      (centeredEigenmode_orthonormal hW) v
  have htop : Summable (fun j : CenteredEigenIndex hW =>
      complementEigenvalue hW i *
        (inner Real v (centeredEigenmode hW j) ^ 2)) :=
    hcoord.mul_left (complementEigenvalue hW i)
  have hweighted :
      -inner Real v (centeredGraphonOp hW v) <=
        ∑' j : CenteredEigenIndex hW,
          complementEigenvalue hW i *
            (inner Real v (centeredEigenmode hW j) ^ 2) := by
    exact hasSum_le
      (fun j => mul_le_mul_of_nonneg_right (hle j) (sq_nonneg _))
      hquad htop.hasSum
  have htopEq :
      (∑' j : CenteredEigenIndex hW,
          complementEigenvalue hW i *
            (inner Real v (centeredEigenmode hW j) ^ 2)) =
        complementEigenvalue hW i *
          (∑' j : CenteredEigenIndex hW,
            inner Real v (centeredEigenmode hW j) ^ 2) :=
    hcoord.tsum_mul_left (complementEigenvalue hW i)
  have hbessel :
      (∑' j : CenteredEigenIndex hW,
          inner Real v (centeredEigenmode hW j) ^ 2) <= inner Real v v :=
    OddCycleBound.Spectral.InfiniteSpectral.tsum_inner_sq_le_self_of_orthonormal
      (centeredEigenmode_orthonormal hW) v
  rw [htopEq] at hweighted
  exact hweighted.trans (mul_le_mul_of_nonneg_left hbessel halpha0)

/-- Projecting the image of the constant vector extracts exactly the centered
degree vector. -/
lemma centerProjection_kernelOpCLM_one_eq_centeredDegreeL2
    (hW : IsGraphon W mu) :
    centerProjection (Omega := Omega) (mu := mu)
        (kernelOpCLM (mu := mu) hW (oneL2 (Omega := Omega) mu)) =
      centeredDegreeL2 hW := by
  rw [← goodL2_one_eq_oneL2,
    kernelOpCLM_goodL2_eq_goodL2,
    centerProjection_apply_goodL2]
  unfold centeredDegreeL2
  apply MemLp.toLp_congr
    (good_memLp_two
      (good_sub (good_kernelOp hW (good_one (Ω := Omega)))
        (good_const (Omega := Omega)
          (mean mu (kernelOp W mu (fun _ : Omega => 1))))))
    (good_memLp_two (good_degCentered hW))
  exact ae_of_all _ fun x => by
    simp [degCentered, degree, edgeDensity, mean, kernelOp]

/-- Exact Hilbert-space hub/coupling/body decomposition of a graphon
quadratic form.  This is the operator version of the manuscript's block
matrix identity. -/
theorem graphon_quadratic_block
    (hW : IsGraphon W mu) {v h : Lp Real 2 mu} {a : Real}
    (hv : v = a • oneL2 (Omega := Omega) mu + h)
    (hh : centerProjection (Omega := Omega) (mu := mu) h = h) :
    inner Real v (kernelOpCLM (mu := mu) hW v) =
      edgeDensity W mu * a ^ 2 +
        2 * a * inner Real (centeredDegreeL2 hW) h +
        inner Real h (centeredGraphonOp hW h) := by
  let one := oneL2 (Omega := Omega) mu
  let T := kernelOpCLM (mu := mu) hW
  let P := centerProjection (Omega := Omega) (mu := mu)
  have hT : T.toLinearMap.IsSymmetric := kernelOpCLM_isSymmetric hW
  have hP : P.toLinearMap.IsSymmetric := centerProjection_isSymmetric
  have hhub : inner Real one (T one) = edgeDensity W mu := by
    dsimp [one, T]
    rw [kernelOpCLM_one_eq_degreeL2]
    exact inner_oneL2_degreeL2_eq_edgeDensity hW
  have hcross : inner Real one (T h) =
      inner Real (centeredDegreeL2 hW) h := by
    calc
      inner Real one (T h) = inner Real (T one) h :=
        (hT.apply_clm one h).symm
      _ = inner Real (P (T one)) h := by
        rw [hP.apply_clm, hh]
      _ = inner Real (centeredDegreeL2 hW) h := by
        dsimp [one, T, P]
        rw [centerProjection_kernelOpCLM_one_eq_centeredDegreeL2]
  have hcross' : inner Real h (T one) =
      inner Real (centeredDegreeL2 hW) h := by
    rw [real_inner_comm]
    exact (hT.apply_clm one h).trans hcross
  have hbody : inner Real h (T h) =
      inner Real h (centeredGraphonOp hW h) := by
    dsimp [T]
    exact inner_kernelOpCLM_eq_centeredGraphonOp_of_centered hW hh
  rw [hv]
  change inner Real (a • one + h) (T (a • one + h)) = _
  rw [map_add, map_smul]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [hhub, hcross, hcross', hbody]
  ring

/-- Complementation negates the centered degree vector. -/
theorem centeredDegreeL2_compl_eq_neg (hW : IsGraphon W mu) :
    centeredDegreeL2 (isGraphon_compl hW) = -centeredDegreeL2 hW := by
  let hU := good_degCentered (isGraphon_compl hW)
  let hG := good_degCentered hW
  let hneg := good_smul (-1 : Real) hG
  have hpoint : degCentered (compl W) mu =
      fun x => (-1 : Real) * degCentered W mu x := by
    rw [degCentered_compl hW]
    funext x
    ring
  have hL2 : goodL2 (mu := mu) hU = goodL2 (mu := mu) hneg := by
    exact MemLp.toLp_congr
      (good_memLp_two hU) (good_memLp_two hneg)
      (ae_of_all _ fun x => congrFun hpoint x)
  unfold centeredDegreeL2
  rw [hL2, goodL2_smul (-1 : Real) hG]
  simp

/-- On a bounded mean-zero vector, the centered complement quadratic form is
the negative of the original centered quadratic form. -/
theorem inner_centeredGraphonOp_compl_goodL2_eq_neg
    (hW : IsGraphon W mu) {f : Omega -> Real} (hf : Good f)
    (hmean : mean mu f = 0) :
    inner Real (goodL2 (mu := mu) hf)
        (centeredGraphonOp (isGraphon_compl hW) (goodL2 (mu := mu) hf)) =
      -inner Real (goodL2 (mu := mu) hf)
        (centeredGraphonOp hW (goodL2 (mu := mu) hf)) := by
  have hcenter : centerProjection (Omega := Omega) (mu := mu)
      (goodL2 (mu := mu) hf) = goodL2 (mu := mu) hf :=
    centerProjection_apply_of_mean_zero hf hmean
  rw [← inner_kernelOpCLM_eq_centeredGraphonOp_of_centered
      (isGraphon_compl hW) hcenter,
    ← inner_kernelOpCLM_eq_centeredGraphonOp_of_centered hW hcenter]
  rw [kernelOpCLM_goodL2_eq_goodL2,
    kernelOpCLM_goodL2_eq_goodL2,
    inner_goodL2_eq_integral_mul,
    inner_goodL2_eq_integral_mul]
  calc
    (∫ x, f x * kernelOp (compl W) mu f x ∂mu) =
        ∫ x, -(f x * kernelOp W mu f x) ∂mu := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          change f x * kernelOp (compl W) mu f x =
            -(f x * kernelOp W mu f x)
          rw [kernelOp_compl hW hf x, hmean]
          ring
    _ = -(∫ x, f x * kernelOp W mu f x ∂mu) := by rw [integral_neg]

/-- The normalized centered eigenmode has complement-kernel quadratic value
equal to its complement eigenvalue. -/
theorem inner_centeredEigenmode_kernelOp_compl_eq
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    {phi : Omega -> Real} (hphi : Good phi)
    (hrep : centeredEigenmode hW i = goodL2 (mu := mu) hphi)
    (hmean : mean mu phi = 0) :
    inner Real (centeredEigenmode hW i)
        (kernelOpCLM (mu := mu) (isGraphon_compl hW)
          (centeredEigenmode hW i)) = complementEigenvalue hW i := by
  have hcenter : centerProjection (Omega := Omega) (mu := mu)
      (centeredEigenmode hW i) = centeredEigenmode hW i := by
    rw [hrep]
    exact centerProjection_apply_of_mean_zero hphi hmean
  have hWpair :
      inner Real (centeredEigenmode hW i)
          (kernelOpCLM (mu := mu) hW (centeredEigenmode hW i)) =
        centeredEigenvalue hW i := by
    rw [inner_kernelOpCLM_eq_centeredGraphonOp_of_centered hW hcenter,
      centeredEigenmode_diagonal, inner_smul_right,
      real_inner_self_eq_norm_sq,
      (centeredEigenmode_orthonormal hW).norm_eq_one]
    norm_num
  calc
    inner Real (centeredEigenmode hW i)
        (kernelOpCLM (mu := mu) (isGraphon_compl hW)
          (centeredEigenmode hW i)) =
        ∫ x, phi x * kernelOp (compl W) mu phi x ∂mu := by
          rw [hrep, kernelOpCLM_goodL2_eq_goodL2]
          exact inner_goodL2_eq_integral_mul hphi
            (good_kernelOp (isGraphon_compl hW) hphi)
    _ = -(∫ x, phi x * kernelOp W mu phi x ∂mu) := by
          calc
            (∫ x, phi x * kernelOp (compl W) mu phi x ∂mu) =
                ∫ x, -(phi x * kernelOp W mu phi x) ∂mu := by
                  refine integral_congr_ae (ae_of_all _ fun x => ?_)
                  change phi x * kernelOp (compl W) mu phi x =
                    -(phi x * kernelOp W mu phi x)
                  rw [kernelOp_compl hW hphi x, hmean]
                  ring
            _ = _ := by rw [integral_neg]
    _ = -inner Real (centeredEigenmode hW i)
          (kernelOpCLM (mu := mu) hW (centeredEigenmode hW i)) := by
          congr 1
          rw [hrep, kernelOpCLM_goodL2_eq_goodL2]
          exact (inner_goodL2_eq_integral_mul hphi
            (good_kernelOp hW hphi)).symm
    _ = complementEigenvalue hW i := by
          rw [hWpair]
          rfl

/-- Scalar core of forced variance.  This isolates the final squaring and
denominator-clearing argument from the graphon block expansion. -/
lemma variance_lower_bound_of_coupling
    {q alpha a G : Real}
    (hqalpha : q < alpha) (halphaPos : 0 < alpha)
    (ha0 : 0 <= a) (haSq : 2 * alpha <= a ^ 2)
    (haSqOne : a ^ 2 < 1)
    (hcoupling : (alpha - q) * a ^ 2 <=
      2 * a * G * Real.sqrt (1 - a ^ 2)) :
    alpha * (alpha - q) ^ 2 / (2 * (1 - 2 * alpha)) <= G ^ 2 := by
  have hdiff0 : 0 <= alpha - q := by linarith
  have halphaHalf : alpha < (1 : Real) / 2 := by nlinarith
  have hden : 0 < 2 * (1 - 2 * alpha) := by nlinarith
  have haPos : 0 < a := by
    by_contra hnot
    have haZero : a = 0 := le_antisymm (le_of_not_gt hnot) ha0
    rw [haZero] at haSq
    norm_num at haSq
    linarith
  have hcoupling' : (alpha - q) * a <=
      2 * G * Real.sqrt (1 - a ^ 2) := by
    apply le_of_mul_le_mul_left ?_ haPos
    calc
      a * ((alpha - q) * a) = (alpha - q) * a ^ 2 := by ring
      _ <= 2 * a * G * Real.sqrt (1 - a ^ 2) := hcoupling
      _ = a * (2 * G * Real.sqrt (1 - a ^ 2)) := by ring
  have hleft0 : 0 <= (alpha - q) * a := mul_nonneg hdiff0 ha0
  have hsquared := mul_self_le_mul_self hleft0 hcoupling'
  have hsqrtSq : (Real.sqrt (1 - a ^ 2)) ^ 2 = 1 - a ^ 2 := by
    rw [Real.sq_sqrt]
    linarith
  have hcore : (alpha - q) ^ 2 * a ^ 2 <=
      4 * G ^ 2 * (1 - a ^ 2) := by
    nlinarith [hsquared, hsqrtSq]
  apply (div_le_iff₀ hden).2
  have hGsq0 : 0 <= G ^ 2 := sq_nonneg G
  have hleftCompare : 2 * alpha * (alpha - q) ^ 2 <=
      (alpha - q) ^ 2 * a ^ 2 := by
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left haSq (sq_nonneg (alpha - q)))
  have hrightCompare : 4 * G ^ 2 * (1 - a ^ 2) <=
      4 * G ^ 2 * (1 - 2 * alpha) := by
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith

/-- Graphon forced variance at a the intermediate region leading_eigenvalue eigenvalue, together
with the strict upper bound needed to clear its denominator. -/
theorem leading_eigenvalue_variance_lower_bound_and_lt_half
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    (hqthird : (1 : Real) / 3 < 1 - edgeDensity W mu)
    (hfront : 1 - edgeDensity W mu < complementEigenvalue hW i) :
    complementEigenvalue hW i *
          (complementEigenvalue hW i - (1 - edgeDensity W mu)) ^ 2 /
        (2 * (1 - 2 * complementEigenvalue hW i)) <=
        ‖centeredDegreeL2 hW‖ ^ 2 ∧
      complementEigenvalue hW i < (1 : Real) / 2 := by
  let alpha := complementEigenvalue hW i
  let q := 1 - edgeDensity W mu
  have halphaPos : 0 < alpha := by dsimp [alpha, q] at *; linarith
  rcases exists_leadingEigenvalueEigenfunction_with_abs_sq_ge hW i halphaPos with
    ⟨phi, hphi, hrep, hmean, hnormPhi, haSqRaw⟩
  let a : Real := ∫ x, |phi x| ∂mu
  let hfabs : Good (fun x : Omega => |phi x|) := good_abs hphi
  let hconst : Good (fun _ : Omega => a) := good_const (Omega := Omega) a
  let hh : Good (fun x : Omega => |phi x| - a) := good_sub hfabs hconst
  let vabs : Lp Real 2 mu := goodL2 (mu := mu) hfabs
  let hvec : Lp Real 2 mu := goodL2 (mu := mu) hh
  have ha0 : 0 <= a := by
    dsimp [a]
    exact integral_nonneg fun x => abs_nonneg (phi x)
  have haSq : 2 * alpha <= a ^ 2 := by
    simpa [alpha, a] using haSqRaw
  have hmeanH : mean mu (fun x : Omega => |phi x| - a) = 0 := by
    unfold mean
    rw [integral_sub hfabs.integrable hconst.integrable]
    simp [a]
  have hvecEq : hvec = vabs - a • oneL2 (Omega := Omega) mu := by
    dsimp [hvec, vabs, hh]
    rw [goodL2_sub hfabs hconst, goodL2_const]
  have hvdecomp : vabs = a • oneL2 (Omega := Omega) mu + hvec := by
    rw [hvecEq]
    abel
  have hcenterH : centerProjection (Omega := Omega) (mu := mu) hvec = hvec := by
    dsimp [hvec]
    exact centerProjection_apply_of_mean_zero hh hmeanH
  have hvabsNormSq : ‖vabs‖ ^ 2 = 1 := by
    dsimp [vabs]
    rw [norm_goodL2_sq_eq_integral_mul]
    calc
      (∫ x, |phi x| * |phi x| ∂mu) =
          ∫ x, phi x * phi x ∂mu := by
            refine integral_congr_ae (ae_of_all _ fun x => ?_)
            change |phi x| * |phi x| = phi x * phi x
            rw [← pow_two, ← pow_two, sq_abs]
      _ = 1 := hnormPhi
  have honeNorm : ‖oneL2 (Omega := Omega) mu‖ = 1 := by
    have hs := norm_oneL2_sq (Omega := Omega) (mu := mu)
    nlinarith [norm_nonneg (oneL2 (Omega := Omega) mu)]
  have hinnerAbsConst :
      inner Real vabs (a • oneL2 (Omega := Omega) mu) = a ^ 2 := by
    dsimp [vabs]
    rw [real_inner_smul_right, real_inner_comm,
      inner_oneL2_goodL2_eq_mean]
    change a * a = a ^ 2
    ring
  have hnormH : ‖hvec‖ ^ 2 = 1 - a ^ 2 := by
    rw [hvecEq, norm_sub_sq_real, hvabsNormSq, hinnerAbsConst,
      norm_smul, honeNorm, mul_one, Real.norm_eq_abs, sq_abs]
    ring
  have haSqLeOne : a ^ 2 <= 1 := by
    have hL1 := integral_abs_sq_le_integral_mul_self (mu := mu) hphi
    simpa [a, hnormPhi] using hL1
  let hU : IsGraphon (compl W) mu := isGraphon_compl hW
  have heigenPair :
      inner Real (centeredEigenmode hW i)
        (kernelOpCLM (mu := mu) hU (centeredEigenmode hW i)) = alpha := by
    simpa [alpha, hU] using
      inner_centeredEigenmode_kernelOp_compl_eq hW i hphi hrep hmean
  have hquadDom : alpha <=
      inner Real vabs (kernelOpCLM (mu := mu) hU vabs) := by
    have hdom := abs_inner_goodL2_kernelOpCLM_self_le_abs
      (mu := mu) hU hphi
    rw [← goodL2_abs hphi] at hdom
    rw [← hrep, heigenPair, abs_of_pos halphaPos] at hdom
    simpa [vabs, hfabs] using hdom
  have hblock := graphon_quadratic_block hU hvdecomp hcenterH
  have haSqOne : a ^ 2 < 1 := by
    by_contra hnot
    have haEq : a ^ 2 = 1 := le_antisymm haSqLeOne (le_of_not_gt hnot)
    have hnormZero : ‖hvec‖ = 0 := by
      have : ‖hvec‖ ^ 2 = 0 := by rw [hnormH, haEq]; ring
      nlinarith [norm_nonneg hvec]
    have hvecZero : hvec = 0 := norm_eq_zero.mp hnormZero
    have hquadEq :
        inner Real vabs (kernelOpCLM (mu := mu) hU vabs) = q := by
      rw [hvecZero] at hblock
      simpa [q, hU, haEq, edgeDensity_compl hW] using hblock
    rw [hquadEq] at hquadDom
    exact (not_lt_of_ge hquadDom hfront)
  have halphaHalf : alpha < (1 : Real) / 2 := by nlinarith
  have hbodySign :
      inner Real hvec (centeredGraphonOp hU hvec) =
        -inner Real hvec (centeredGraphonOp hW hvec) := by
    simpa [hU, hvec] using
      inner_centeredGraphonOp_compl_goodL2_eq_neg hW hh hmeanH
  have hbodyUpper :
      inner Real hvec (centeredGraphonOp hU hvec) <=
        alpha * (1 - a ^ 2) := by
    have htop := complementCompression_quadratic_le_leading_eigenvalue
      hW i hqthird hfront (le_of_lt halphaPos) hvec
    rw [hbodySign]
    rw [real_inner_self_eq_norm_sq, hnormH] at htop
    exact htop
  have hsqrtNorm : Real.sqrt (1 - a ^ 2) = ‖hvec‖ := by
    rw [← hnormH, Real.sqrt_sq (norm_nonneg hvec)]
  have hcrossUpper :
      inner Real (centeredDegreeL2 hU) hvec <=
        ‖centeredDegreeL2 hW‖ * Real.sqrt (1 - a ^ 2) := by
    calc
      inner Real (centeredDegreeL2 hU) hvec <=
          ‖centeredDegreeL2 hU‖ * ‖hvec‖ := real_inner_le_norm _ _
      _ = ‖centeredDegreeL2 hW‖ * ‖hvec‖ := by
          rw [centeredDegreeL2_compl_eq_neg hW, norm_neg]
      _ = ‖centeredDegreeL2 hW‖ * Real.sqrt (1 - a ^ 2) := by
          rw [hsqrtNorm]
  have hcrossMul :
      2 * a * inner Real (centeredDegreeL2 hU) hvec <=
        2 * a * (‖centeredDegreeL2 hW‖ * Real.sqrt (1 - a ^ 2)) :=
    mul_le_mul_of_nonneg_left hcrossUpper (mul_nonneg (by norm_num) ha0)
  have hcoupling : (alpha - q) * a ^ 2 <=
      2 * a * ‖centeredDegreeL2 hW‖ * Real.sqrt (1 - a ^ 2) := by
    rw [edgeDensity_compl hW] at hblock
    nlinarith
  constructor
  · exact variance_lower_bound_of_coupling hfront halphaPos ha0 haSq haSqOne hcoupling
  · simpa [alpha] using halphaHalf

/-- The forced degree-variance lower bound at a the intermediate region leading_eigenvalue
eigenvalue. -/
theorem leading_eigenvalue_variance_lower_bound
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    (hqthird : (1 : Real) / 3 < 1 - edgeDensity W mu)
    (hfront : 1 - edgeDensity W mu < complementEigenvalue hW i) :
    complementEigenvalue hW i *
          (complementEigenvalue hW i - (1 - edgeDensity W mu)) ^ 2 /
        (2 * (1 - 2 * complementEigenvalue hW i)) <=
      ‖centeredDegreeL2 hW‖ ^ 2 :=
  (leading_eigenvalue_variance_lower_bound_and_lt_half hW i hqthird hfront).1

/-- A leading_eigenvalue eigenvalue is strictly smaller than (1/2). -/
theorem complement_leading_eigenvalue_lt_half
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    (hqthird : (1 : Real) / 3 < 1 - edgeDensity W mu)
    (hfront : 1 - edgeDensity W mu < complementEigenvalue hW i) :
    complementEigenvalue hW i < (1 : Real) / 2 :=
  (leading_eigenvalue_variance_lower_bound_and_lt_half hW i hqthird hfront).2

/-- A single leading_eigenvalue atom and the centered degree vector obey the global
Hilbert--Schmidt bound. -/
theorem leading_eigenvalue_spectral_bound
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW) :
    complementEigenvalue hW i ^ 2 + 2 * ‖centeredDegreeL2 hW‖ ^ 2 <=
      edgeDensity W mu * (1 - edgeDensity W mu) := by
  classical
  have heigen := centeredEigenvalue_finite_square_bound hW
    ({i} : Finset (CenteredEigenIndex hW))
  have hsingle :
      complementEigenvalue hW i ^ 2 <=
        kernelSqNorm mu (centeredKernel W mu) := by
    simpa [complementEigenvalue] using heigen
  have hkernel := centeredKernel_hilbertSchmidt_bound hW
  linarith

/-- Forced variance and the Hilbert--Schmidt bound give the quadratic
leading_eigenvalue ceiling. -/
theorem leading_eigenvalue_quadratic_ceiling
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    (hqthird : (1 : Real) / 3 < 1 - edgeDensity W mu)
    (hfront : 1 - edgeDensity W mu < complementEigenvalue hW i) :
    complementEigenvalue hW i ^ 2 +
          (1 - edgeDensity W mu) * complementEigenvalue hW i -
        (1 - edgeDensity W mu) <= 0 := by
  apply Scalar.quadratic_ceiling_of_variance_lower_bound
    hqthird hfront
    (complement_leading_eigenvalue_lt_half hW i hqthird hfront)
    (leading_eigenvalue_variance_lower_bound hW i hqthird hfront)
  have hbound := leading_eigenvalue_spectral_bound hW i
  convert hbound using 1 <;> ring

/-- Explicit square-root form of the leading_eigenvalue ceiling. -/
theorem leading_eigenvalue_radius_ceiling
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    (hqthird : (1 : Real) / 3 < 1 - edgeDensity W mu)
    (hfront : 1 - edgeDensity W mu < complementEigenvalue hW i) :
    complementEigenvalue hW i <=
      Scalar.leadingEigenvalueRadius (1 - edgeDensity W mu) := by
  apply Scalar.leadingEigenvalueRadius_of_variance_lower_bound
    hqthird hfront
    (complement_leading_eigenvalue_lt_half hW i hqthird hfront)
    (leading_eigenvalue_variance_lower_bound hW i hqthird hfront)
  have hbound := leading_eigenvalue_spectral_bound hW i
  convert hbound using 1 <;> ring

end OddCycleBound.IntermediateRegion
