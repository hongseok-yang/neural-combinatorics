import OddCycleBound.RegionII.CouplingChannels
import OddCycleBound.RegionII.Scalar.ShapeElimination

/-!
# Graphon interface for exact Huber elimination

This module connects the representative-level direct and safe channels to the
abstract scalar shape theorem.  The first theorem keeps the harmless frontier
sign orientation (`b >= 0`) explicit; a subsequent wrapper chooses that
orientation automatically.
-/

open MeasureTheory

noncomputable section

namespace OddCycleBound.RegionII

open OddCycleBound.HighDensity
open OddCycleBound.LowBand.L2Kernel

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega -> Omega -> Real}

/-- Exact Huber payment for a frontier representative whose sign has been
oriented so that the cubic shape coefficient is nonnegative. -/
theorem graphon_huber_shape_elimination_oriented
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    {phi : Omega -> Real} (hphi : Good phi)
    (hrep : centeredEigenmode hW i = goodL2 (mu := mu) hphi)
    (hmean : mean mu phi = 0)
    (hnorm : (∫ x, phi x * phi x ∂mu) = 1)
    (halpha : 0 < complementEigenvalue hW i)
    (halphaHalf : complementEigenvalue hW i < 1 / 2)
    (hfront : edgeDensity (compl W) mu < complementEigenvalue hW i)
    (hLalpha : frontierSafeRadius hW i < complementEigenvalue hW i)
    (hzalpha : 2 * complementEigenvalue hW i <= frontierShapeZ mu phi)
    (hb : 0 <= frontierShapeB mu phi)
    {A B : Real} (hA : 0 <= A) (hB : 0 < B) :
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
    let e := 1 - 2 * alpha
    let d := alpha - q
    let f := alpha - L
    let C := B * f * Real.sqrt (2 * alpha) * e ^ 2 / (4 * alpha ^ 2)
    let xi := 4 * alpha ^ 2 * d / e ^ 2
    let rho := (A / B) *
      (Real.sqrt alpha / (2 * Real.sqrt 2 * f))
    C * Scalar.psi xi rho <= A * c ^ 2 + B * ‖gs‖ ^ 2 := by
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
  have hdirect := frontier_direct_channel hW i hphi hrep hmean hnorm
  have hsafeData := frontier_safe_channel hW i hphi hrep hmean hnorm
    halpha hzalpha
  have hsafeSq := frontier_safe_channel_sq hW i hphi hrep hmean hnorm
    halpha hzalpha
  dsimp only at hdirect hsafeData hsafeSq
  have hK0 : 0 <= K := sq_nonneg ‖kVec‖
  have hgs0 : 0 <= ‖gs‖ ^ 2 := sq_nonneg ‖gs‖
  have hshape : z + b ^ 2 + K = 1 := by
    simpa [hU, alpha, q, L, a, z, b, kVec, hk, K, c, gs] using hsafeData.1
  have hdirect' : 2 * c * Real.sqrt z + 2 * alpha * b <= z - 2 * alpha := by
    simpa [hU, alpha, q, L, a, z, b, kVec, hk, K, c, gs] using hdirect
  have hsafe' : max (Scalar.shapeThreshold alpha q L z K - b * c) 0 ^ 2 <=
      ‖gs‖ ^ 2 * K := by
    simpa [Scalar.shapeThreshold, hU, alpha, q, L, a, z, b, kVec, hk, K, c, gs]
      using hsafeSq
  simpa [hU, alpha, q, L, a, z, b, kVec, hk, K, c, gs] using
    (Scalar.exact_huber_shape_elimination
      (alpha := alpha) (q := q) (L := L) (A := A) (B := B)
      (c := c) (gsSq := ‖gs‖ ^ 2) (z := z) (b := b) (K := K)
      halpha halphaHalf hfront hLalpha hA hB hb hK0 hgs0 hzalpha
      hshape hdirect' hsafe')

/-- Sign-free graphon Huber payment.  Both positive-part orientations are
proved in `CouplingChannels`, so no convention on the spectral basis is
required. -/
theorem graphon_huber_shape_elimination
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    {phi : Omega -> Real} (hphi : Good phi)
    (hrep : centeredEigenmode hW i = goodL2 (mu := mu) hphi)
    (hmean : mean mu phi = 0)
    (hnorm : (∫ x, phi x * phi x ∂mu) = 1)
    (halpha : 0 < complementEigenvalue hW i)
    (halphaHalf : complementEigenvalue hW i < 1 / 2)
    (hfront : edgeDensity (compl W) mu < complementEigenvalue hW i)
    (hLalpha : frontierSafeRadius hW i < complementEigenvalue hW i)
    (hzalpha : 2 * complementEigenvalue hW i <= frontierShapeZ mu phi)
    {A B : Real} (hA : 0 <= A) (hB : 0 < B) :
    let hU := isGraphon_compl hW
    let alpha := complementEigenvalue hW i
    let q := edgeDensity (compl W) mu
    let L := frontierSafeRadius hW i
    let c := inner Real (centeredDegreeL2 hU) (centeredEigenmode hW i)
    let gs := centeredDegreeL2 hU - c • centeredEigenmode hW i
    let e := 1 - 2 * alpha
    let d := alpha - q
    let f := alpha - L
    let C := B * f * Real.sqrt (2 * alpha) * e ^ 2 / (4 * alpha ^ 2)
    let xi := 4 * alpha ^ 2 * d / e ^ 2
    let rho := (A / B) *
      (Real.sqrt alpha / (2 * Real.sqrt 2 * f))
    C * Scalar.psi xi rho <= A * c ^ 2 + B * ‖gs‖ ^ 2 := by
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
  have hdirect := frontier_direct_channel hW i hphi hrep hmean hnorm
  have hdirectNeg := frontier_direct_channel_neg hW i hphi hrep hmean hnorm
  have hsafeData := frontier_safe_channel hW i hphi hrep hmean hnorm
    halpha hzalpha
  have hsafeSq := frontier_safe_channel_sq hW i hphi hrep hmean hnorm
    halpha hzalpha
  dsimp only at hdirect hdirectNeg hsafeData hsafeSq
  have hK0 : 0 <= K := sq_nonneg ‖kVec‖
  have hgs0 : 0 <= ‖gs‖ ^ 2 := sq_nonneg ‖gs‖
  have hshape : z + b ^ 2 + K = 1 := by
    simpa [hU, alpha, q, L, a, z, b, kVec, hk, K, c, gs] using hsafeData.1
  have hdirect' : 2 * c * Real.sqrt z + 2 * alpha * b <= z - 2 * alpha := by
    simpa [hU, alpha, q, L, a, z, b, kVec, hk, K, c, gs] using hdirect
  have hdirectNeg' : -2 * c * Real.sqrt z - 2 * alpha * b <=
      z - 2 * alpha := by
    simpa [hU, alpha, q, L, a, z, b, kVec, hk, K, c, gs] using hdirectNeg
  have hsafe' : max (Scalar.shapeThreshold alpha q L z K - b * c) 0 ^ 2 <=
      ‖gs‖ ^ 2 * K := by
    simpa [Scalar.shapeThreshold, hU, alpha, q, L, a, z, b, kVec, hk, K, c, gs]
      using hsafeSq
  simpa [hU, alpha, q, L, a, z, b, kVec, hk, K, c, gs] using
    (Scalar.exact_huber_shape_elimination_two_sided
      (alpha := alpha) (q := q) (L := L) (A := A) (B := B)
      (c := c) (gsSq := ‖gs‖ ^ 2) (z := z) (b := b) (K := K)
      halpha halphaHalf hfront hLalpha hA hB hK0 hgs0 hzalpha hshape
      hdirect' hdirectNeg' hsafe')

/-- Representative-free graphon Huber payment.  The normalized bounded
frontier representative and its forced `L¹` mass are constructed internally. -/
theorem graphon_huber_payment
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    (hqpos : 0 < edgeDensity (compl W) mu)
    (hfront : edgeDensity (compl W) mu < complementEigenvalue hW i)
    (halphaHalf : complementEigenvalue hW i < 1 / 2)
    (hLalpha : frontierSafeRadius hW i < complementEigenvalue hW i)
    {A B : Real} (hA : 0 <= A) (hB : 0 < B) :
    let hU := isGraphon_compl hW
    let alpha := complementEigenvalue hW i
    let q := edgeDensity (compl W) mu
    let L := frontierSafeRadius hW i
    let c := inner Real (centeredDegreeL2 hU) (centeredEigenmode hW i)
    let gs := centeredDegreeL2 hU - c • centeredEigenmode hW i
    let e := 1 - 2 * alpha
    let d := alpha - q
    let f := alpha - L
    let C := B * f * Real.sqrt (2 * alpha) * e ^ 2 / (4 * alpha ^ 2)
    let xi := 4 * alpha ^ 2 * d / e ^ 2
    let rho := (A / B) *
      (Real.sqrt alpha / (2 * Real.sqrt 2 * f))
    C * Scalar.psi xi rho <= A * c ^ 2 + B * ‖gs‖ ^ 2 := by
  dsimp only
  have halpha : 0 < complementEigenvalue hW i := by linarith
  rcases exists_frontierEigenfunction_with_abs_sq_ge hW i halpha with
    ⟨phi, hphi, hrep, hmean, hnorm, hzalpha⟩
  exact graphon_huber_shape_elimination hW i hphi hrep hmean hnorm
    halpha halphaHalf hfront hLalpha hzalpha hA hB

end OddCycleBound.RegionII
