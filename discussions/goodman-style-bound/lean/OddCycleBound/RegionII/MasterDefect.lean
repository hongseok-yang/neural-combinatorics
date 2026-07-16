import OddCycleBound.RegionII.ShiftSpectral
import OddCycleBound.RegionII.Scalar.Definitions

/-!
# Region-II master defect

This file combines the refined centered trace estimate with the one-sided
spectral shift.  It is the operator-to-scalar handoff in the corrected
Region-II proof: all remaining obligations concern the scalar coefficients
and the Huber/zone estimates.
-/

open MeasureTheory

noncomputable section

namespace OddCycleBound.RegionII

open OddCycleBound.HighDensity

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega -> Omega -> Real}

/-- The corrected master-defect inequality in denominator-free form.  The
frontier mode is retained exactly and its orthogonal complement pays at the
safe spectral endpoint. -/
theorem graphon_frontier_master_defect_directed
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    {m : Nat} (hp : 1 / 2 < edgeDensity W mu)
    (hm : Odd m) (hm3 : 3 <= m) :
    let p := edgeDensity W mu
    let q := 1 - p
    let alpha := complementEigenvalue hW i
    let L := frontierSafeRadius hW i
    let phi := centeredEigenmode hW i
    let g := centeredDegreeL2 hW
    let c := inner Real g phi
    let gs := g - c • phi
    (-(alpha ^ m + L ^ m - p * q ^ (m - 1)) +
        (2 * L ^ (m - 2) +
          (m : Real) * directedKernel p m alpha) * c ^ 2 +
        (2 * L ^ (m - 2) +
          (m : Real) * directedKernel p m L) * ‖gs‖ ^ 2 <=
      cycleDensity mu W m - (p ^ m - p * q ^ (m - 1))) := by
  dsimp only
  let p := edgeDensity W mu
  let q := 1 - p
  let alpha := complementEigenvalue hW i
  let L := frontierSafeRadius hW i
  let phi := centeredEigenmode hW i
  let g := centeredDegreeL2 hW
  let c := inner Real g phi
  let gs := g - c • phi
  have hphiNorm : ‖phi‖ = 1 :=
    (centeredEigenmode_orthonormal hW).norm_eq_one i
  have horthGS : inner Real gs phi = 0 := by
    dsimp [gs, c]
    rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq,
      hphiNorm]
    simp
  have horth : inner Real (c • phi) gs = 0 := by
    rw [real_inner_smul_left, real_inner_comm, horthGS]
    simp
  have hdecomp : g = c • phi + gs := by
    dsimp [gs]
    abel
  have hnorm : ‖g‖ ^ 2 = c ^ 2 + ‖gs‖ ^ 2 := by
    calc
      ‖g‖ ^ 2 = ‖c • phi + gs‖ ^ 2 := by rw [hdecomp]
      _ = ‖c • phi‖ ^ 2 + ‖gs‖ ^ 2 :=
        by simpa [pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_real horth
      _ = c ^ 2 + ‖gs‖ ^ 2 := by
        simp [norm_smul, Real.norm_eq_abs, hphiNorm, sq_abs]
  have htrace := centered_trace_frontier_defect_lower_bound
    hW i hm hm3
  have hshift := graphonOneSidedShift_frontier_lower_bound
    hW i hp hm (by omega)
  have hid := graphon_oneSidedShift_identity hW (by omega : 0 < m)
  dsimp only at htrace hshift hid
  calc
    -(alpha ^ m + L ^ m - p * q ^ (m - 1)) +
          (2 * L ^ (m - 2) +
            (m : Real) * directedKernel p m alpha) * c ^ 2 +
          (2 * L ^ (m - 2) +
            (m : Real) * directedKernel p m L) * ‖gs‖ ^ 2 =
        (-alpha ^ m - L ^ m +
            2 * L ^ (m - 2) * ‖g‖ ^ 2) +
          (m : Real) *
            (directedKernel p m alpha * c ^ 2 +
              directedKernel p m L * ‖gs‖ ^ 2) +
          p * q ^ (m - 1) := by
            rw [hnorm]
            ring
    _ <= trace mu (compPow mu (centeredKernel W mu) (m - 1)) +
          graphonOneSidedShift hW m + p * q ^ (m - 1) := by
            linarith
    _ = cycleDensity mu W m - (p ^ m - p * q ^ (m - 1)) := by
          rw [hid]
          dsimp [p]
          ring

end OddCycleBound.RegionII
