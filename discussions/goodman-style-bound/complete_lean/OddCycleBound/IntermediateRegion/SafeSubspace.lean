import OddCycleBound.IntermediateRegion.VarianceLowerBound

/-!
# The safe spectrum below a the intermediate region leading_eigenvalue

After a leading_eigenvalue atom `alpha` is removed, the Hilbert--Schmidt bound puts
every remaining complement-compression eigenvalue in the interval
`[-L,L]`, where `L^2 = p(1-p)-alpha^2`.  This file also packages the
corresponding quadratic-form estimate on vectors orthogonal to the leading_eigenvalue
mode.
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

/-- Radius available to the spectrum after one leading_eigenvalue square is charged
against the Hilbert--Schmidt bound. -/
noncomputable def leadingEigenvalueSafeRadius (hW : IsGraphon W mu)
    (i : CenteredEigenIndex hW) : Real :=
  Real.sqrt
    (edgeDensity W mu * (1 - edgeDensity W mu) -
      complementEigenvalue hW i ^ 2)

theorem leadingEigenvalueSafeRadius_radicand_nonneg
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW) :
    0 <= edgeDensity W mu * (1 - edgeDensity W mu) -
      complementEigenvalue hW i ^ 2 := by
  have hbound := leading_eigenvalue_spectral_bound hW i
  nlinarith [sq_nonneg ‖centeredDegreeL2 hW‖]

theorem leadingEigenvalueSafeRadius_nonneg
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW) :
    0 <= leadingEigenvalueSafeRadius hW i :=
  Real.sqrt_nonneg _

theorem leadingEigenvalueSafeRadius_sq
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW) :
    leadingEigenvalueSafeRadius hW i ^ 2 =
      edgeDensity W mu * (1 - edgeDensity W mu) -
        complementEigenvalue hW i ^ 2 := by
  unfold leadingEigenvalueSafeRadius
  exact Real.sq_sqrt (leadingEigenvalueSafeRadius_radicand_nonneg hW i)

/-- In the intermediate region the residual safe radius is strictly below the leading_eigenvalue.
This is the positivity of the manuscript gap `f = alpha - L`. -/
theorem leadingEigenvalueSafeRadius_lt_complementEigenvalue
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    (hqthird : (1 : Real) / 3 < 1 - edgeDensity W mu)
    (hfront : 1 - edgeDensity W mu < complementEigenvalue hW i) :
    leadingEigenvalueSafeRadius hW i < complementEigenvalue hW i := by
  let p := edgeDensity W mu
  let q := 1 - p
  let alpha := complementEigenvalue hW i
  let L := leadingEigenvalueSafeRadius hW i
  have hqpos : 0 < q := by dsimp [q, p] at *; linarith
  have halpha : 0 < alpha := by dsimp [alpha, q, p] at *; linarith
  have hL0 : 0 <= L := leadingEigenvalueSafeRadius_nonneg hW i
  have hLsq : L ^ 2 = p * q - alpha ^ 2 := by
    simpa [L, p, q, alpha] using leadingEigenvalueSafeRadius_sq hW i
  have hpq : p * q < 2 * alpha ^ 2 := by
    dsimp [p, q, alpha] at *
    nlinarith [sq_nonneg (complementEigenvalue hW i -
      (1 - edgeDensity W mu))]
  have hsq : L ^ 2 < alpha ^ 2 := by nlinarith
  by_contra hnot
  have hale : alpha <= L := le_of_not_gt hnot
  have hsquareLe : alpha ^ 2 <= L ^ 2 :=
    pow_le_pow_left₀ (le_of_lt halpha) hale 2
  exact (not_lt_of_ge hsquareLe) hsq

/-- Every non-leading_eigenvalue complement eigenvalue is bounded by the safe radius. -/
theorem abs_complementEigenvalue_le_leadingEigenvalueSafeRadius
    (hW : IsGraphon W mu) {i j : CenteredEigenIndex hW}
    (hij : j ≠ i) :
    |complementEigenvalue hW j| <= leadingEigenvalueSafeRadius hW i := by
  classical
  have heigen := centeredEigenvalue_finite_square_bound hW
    ({i, j} : Finset (CenteredEigenIndex hW))
  have hkernel := centeredKernel_hilbertSchmidt_bound hW
  have hsquares :
      complementEigenvalue hW i ^ 2 +
          complementEigenvalue hW j ^ 2 <=
        edgeDensity W mu * (1 - edgeDensity W mu) := by
    have hij' : i ≠ j := Ne.symm hij
    simp [hij', complementEigenvalue] at heigen
    have hkernel' :
        kernelSqNorm mu (centeredKernel W mu) <=
          edgeDensity W mu * (1 - edgeDensity W mu) := by
      nlinarith [sq_nonneg ‖centeredDegreeL2 hW‖]
    have hs := heigen.trans hkernel'
    simpa [complementEigenvalue] using hs
  have hsafeSq :
      complementEigenvalue hW j ^ 2 <=
        leadingEigenvalueSafeRadius hW i ^ 2 := by
    rw [leadingEigenvalueSafeRadius_sq hW i]
    linarith
  nlinarith [sq_abs (complementEigenvalue hW j),
    abs_nonneg (complementEigenvalue hW j),
    leadingEigenvalueSafeRadius_nonneg hW i]

/-- Quadratic-form domination by the safe radius on the orthogonal complement
of the leading_eigenvalue eigenmode.  A possible zero-eigenspace residual contributes
zero and is harmless because the radius is nonnegative. -/
theorem complementCompression_quadratic_le_safeRadius
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    {v : Lp Real 2 mu}
    (horth : inner Real v (centeredEigenmode hW i) = 0) :
    -inner Real v (centeredGraphonOp hW v) <=
      leadingEigenvalueSafeRadius hW i * inner Real v v := by
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
  have hpoint : ∀ j : CenteredEigenIndex hW,
      complementEigenvalue hW j *
          (inner Real v (centeredEigenmode hW j) ^ 2) <=
        leadingEigenvalueSafeRadius hW i *
          (inner Real v (centeredEigenmode hW j) ^ 2) := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [horth]
    · exact mul_le_mul_of_nonneg_right
        ((le_abs_self _).trans
          (abs_complementEigenvalue_le_leadingEigenvalueSafeRadius hW hji))
        (sq_nonneg _)
  have hcoord : Summable (fun j : CenteredEigenIndex hW =>
      inner Real v (centeredEigenmode hW j) ^ 2) :=
    OddCycleBound.Spectral.InfiniteSpectral.summable_inner_sq_of_orthonormal
      (centeredEigenmode_orthonormal hW) v
  have htop : Summable (fun j : CenteredEigenIndex hW =>
      leadingEigenvalueSafeRadius hW i *
        (inner Real v (centeredEigenmode hW j) ^ 2)) :=
    hcoord.mul_left (leadingEigenvalueSafeRadius hW i)
  have hweighted :
      -inner Real v (centeredGraphonOp hW v) <=
        ∑' j : CenteredEigenIndex hW,
          leadingEigenvalueSafeRadius hW i *
            (inner Real v (centeredEigenmode hW j) ^ 2) :=
    hasSum_le hpoint hquad htop.hasSum
  have htopEq :
      (∑' j : CenteredEigenIndex hW,
          leadingEigenvalueSafeRadius hW i *
            (inner Real v (centeredEigenmode hW j) ^ 2)) =
        leadingEigenvalueSafeRadius hW i *
          (∑' j : CenteredEigenIndex hW,
            inner Real v (centeredEigenmode hW j) ^ 2) :=
    hcoord.tsum_mul_left (leadingEigenvalueSafeRadius hW i)
  have hbessel :
      (∑' j : CenteredEigenIndex hW,
          inner Real v (centeredEigenmode hW j) ^ 2) <= inner Real v v :=
    OddCycleBound.Spectral.InfiniteSpectral.tsum_inner_sq_le_self_of_orthonormal
      (centeredEigenmode_orthonormal hW) v
  rw [htopEq] at hweighted
  exact hweighted.trans
    (mul_le_mul_of_nonneg_left hbessel (leadingEigenvalueSafeRadius_nonneg hW i))

end OddCycleBound.IntermediateRegion
