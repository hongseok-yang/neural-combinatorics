import OddCycleBound.RegionII.MasterDefect
import OddCycleBound.RegionII.HuberGraphon
import OddCycleBound.RegionII.Scalar.Assembly
import OddCycleBound.BasicBounds

/-!
# Public Region II bound for large odd cycles

This file is the final graphon/scalar assembly for odd `m ≥ 15`.  The
no-frontier case is already spectral.  In the frontier case, the graphon
master defect is paid by the representative-free Huber estimate, while the
scalar zone theorem shows that this payment covers the entire scalar defect.
-/

open MeasureTheory

noncomputable section

namespace OddCycleBound.RegionII

open OddCycleBound.HighDensity

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}
variable {m : ℕ}

/-- The unconditional Region II theorem for every odd cycle of length at
least fifteen. -/
theorem regionII_large_odd_bound
    (hW : IsGraphon W μ)
    (hm : Odd m) (hm15 : 15 ≤ m)
    (hp_lo : 1 / 2 < edgeDensity W μ)
    (hp_hi : edgeDensity W μ < 2 / 3) :
    trace μ (compPow μ W (m - 1)) ≥
      edgeDensity W μ ^ m -
        edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) := by
  classical
  let p := edgeDensity W μ
  let q := 1 - p
  by_cases hno : ∀ i : CenteredEigenIndex hW,
      complementEigenvalue hW i ≤ q
  · simpa [p, q, cycleDensity] using
      (no_frontier_odd_cycle_bound hW hm (by omega) hp_lo hno)
  · simp only [not_forall, not_le] at hno
    obtain ⟨i, hfront⟩ := hno
    let alpha := complementEigenvalue hW i
    let L := frontierSafeRadius hW i
    let phi := centeredEigenmode hW i
    let g := centeredDegreeL2 hW
    let c := inner ℝ g phi
    let gs := g - c • phi
    have hqthird : (1 : ℝ) / 3 < q := by
      dsimp [q, p]
      linarith
    have hqhalf : q < (1 : ℝ) / 2 := by
      dsimp [q, p]
      linarith
    have halphaHalf : alpha < (1 : ℝ) / 2 :=
      complement_frontier_lt_half hW i hqthird hfront
    have hLalpha : L < alpha :=
      frontierSafeRadius_lt_complementEigenvalue hW i hqthird hfront
    let P : Scalar.AdmissibleParams :=
      { q := q
        alpha := alpha
        m := m
        q_gt_third := hqthird
        q_lt_half := hqhalf
        alpha_gt_q := hfront
        alpha_le_radius := frontier_radius_ceiling hW i hqthird hfront
        m_odd := hm
        m_ge_fifteen := hm15 }
    have hPp : P.p = p := by
      simp [P, Scalar.AdmissibleParams.p, q]
    have hPL : P.L = L := by
      dsimp [Scalar.AdmissibleParams.L, Scalar.AdmissibleParams.p, P, L]
      unfold frontierSafeRadius
      congr 1
      dsimp [q, p, alpha]
      ring
    have hkAlpha : P.k P.alpha = directedKernel p m alpha := by
      calc
        P.k P.alpha = directedKernel P.p P.m P.alpha :=
          P.k_eq_directedKernel P.alpha
            ((neg_nonpos.mpr P.p_pos.le).trans P.alpha_nonneg)
            (ne_of_gt (add_pos P.p_pos P.alpha_pos))
        _ = directedKernel p m alpha := by rw [hPp]
    have hkL : P.k P.L = directedKernel p m L := by
      calc
        P.k P.L = directedKernel P.p P.m P.L :=
          P.k_eq_directedKernel P.L
            ((neg_nonpos.mpr P.p_pos.le).trans P.L_nonneg)
            (ne_of_gt (add_pos_of_pos_of_nonneg P.p_pos P.L_nonneg))
        _ = directedKernel p m L := by rw [hPp, hPL]
    have hAeq : P.A =
        2 * L ^ (m - 2) + (m : ℝ) * directedKernel p m alpha := by
      unfold Scalar.AdmissibleParams.A
      rw [hPL, hkAlpha]
    have hBeq : P.B =
        2 * L ^ (m - 2) + (m : ℝ) * directedKernel p m L := by
      unfold Scalar.AdmissibleParams.B
      rw [hkL, hPL]
    have hReq : P.R = alpha ^ m + L ^ m - p * q ^ (m - 1) := by
      unfold Scalar.AdmissibleParams.R
      rw [hPL, hPp]
    let hU := isGraphon_compl hW
    let cU := inner ℝ (centeredDegreeL2 hU) phi
    let gsU := centeredDegreeL2 hU - cU • phi
    have hcU : cU = -c := by
      dsimp [cU, c, g, hU]
      rw [centeredDegreeL2_compl_eq_neg hW, inner_neg_left]
    have hgsU : gsU = -gs := by
      dsimp [gsU, gs, cU, c, g, hU]
      rw [centeredDegreeL2_compl_eq_neg hW, inner_neg_left]
      module
    have hqposU : 0 < edgeDensity (compl W) μ := by
      rw [OddCycleBound.edgeDensity_compl hW]
      linarith [hqthird]
    have hfrontU : edgeDensity (compl W) μ < alpha := by
      rw [OddCycleBound.edgeDensity_compl hW]
      exact hfront
    have hpay := graphon_huber_payment hW i hqposU hfrontU
      halphaHalf hLalpha P.A_nonneg P.B_pos
    dsimp only at hpay
    rw [OddCycleBound.edgeDensity_compl hW] at hpay
    have hpayP : P.C * Scalar.psi P.xi P.rho ≤
        P.A * cU ^ 2 + P.B * ‖gsU‖ ^ 2 := by
      simpa [Scalar.AdmissibleParams.C, Scalar.AdmissibleParams.f,
        Scalar.AdmissibleParams.e, Scalar.AdmissibleParams.d,
        Scalar.AdmissibleParams.xi, Scalar.AdmissibleParams.rho,
        P, hPL, L, alpha, q, cU, gsU, hU, phi] using hpay
    have hscalar := P.scalar_huber_bound
    have hpayment : P.R ≤ P.A * c ^ 2 + P.B * ‖gs‖ ^ 2 := by
      calc
        P.R ≤ P.C * Scalar.psi P.xi P.rho := hscalar
        _ ≤ P.A * cU ^ 2 + P.B * ‖gsU‖ ^ 2 := hpayP
        _ = P.A * c ^ 2 + P.B * ‖gs‖ ^ 2 := by
          rw [hcU, hgsU, neg_sq, norm_neg]
    have hmaster := graphon_frontier_master_defect_directed
      hW i hp_lo hm (by omega)
    dsimp only at hmaster
    have hdefect : 0 ≤
        cycleDensity μ W m - (p ^ m - p * q ^ (m - 1)) := by
      rw [← hReq, ← hAeq, ← hBeq] at hmaster
      dsimp [alpha, L, phi, g, c, gs, p, q] at hmaster hpayment ⊢
      linarith
    simpa [cycleDensity, p, q] using hdefect

end OddCycleBound.RegionII
