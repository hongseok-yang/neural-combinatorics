import OddCycleBound.IntermediateRegion.DefectLowerBound
import OddCycleBound.IntermediateRegion.EnvelopeBound
import OddCycleBound.IntermediateRegion.VarianceLowerBound
import OddCycleBound.IntermediateRegion.SafeSubspace
import OddCycleBound.IntermediateRegion.ScalarTarget

/-!
# Intermediate-region assembly (paper §10, lines 3550–3573)

This file closes the intermediate region `1/2 < p < 2/3`, odd `m ≥ 9`, by wiring the operator-side
lemmas to the scalar target `R ≤ C·ψ`.  Everything consumed here is already proven:

* `graphon_leading_eigenvalue_defect_lower_bound_directed` — the master defect (`prop:master-defect`,
  `DefectLowerBound.lean`).
* `graphon_envelope_bound` — the envelope elimination (`thm:huber-elim`, `EnvelopeBound.lean`).
* `Scalar.AdmissibleParams.scalar_target` — the scalar inequality `R ≤ C·ψ` (`ScalarTarget.lean`).
* `cycle_bound_of_eigenvalues_le_q` — the no-frontier branch (`lem:no-frontier`,
  `LeadingEigenvalue.lean`).
* the forced-variance ceiling and the safe-radius gap (`VarianceLowerBound.lean`, `SafeSubspace.lean`).

The frontier dichotomy is a classical case split: either no complement eigenvalue exceeds `q = 1 − p`
(no-frontier branch), or one does, giving a `CenteredEigenIndex` at which the master defect, the
envelope bound instantiated with the master-defect coefficients `A, B`, and the scalar target chain to
the conclusion.
-/

open MeasureTheory

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.DenseRegion
open OddCycleBound.Spectral.L2Kernel

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega -> Omega -> Real}

/-- **Intermediate region** (`1/2 < p < 2/3`, odd `m ≥ 9`).  The odd-cycle Goodman bound holds. -/
theorem intermediateRegion_odd_cycle_bound
    (hW : IsGraphon W mu) {m : Nat} (hm : Odd m) (hm9 : 9 <= m)
    (hp1 : (1 : Real) / 2 < edgeDensity W mu)
    (hp2 : edgeDensity W mu < 2 / 3) :
    edgeDensity W mu ^ m -
        edgeDensity W mu * (1 - edgeDensity W mu) ^ (m - 1) <=
      cycleDensity mu W m := by
  have hm3 : 3 <= m := by omega
  have hqthird : (1 : Real) / 3 < 1 - edgeDensity W mu := by linarith
  by_cases hfrontier :
      ∃ i : CenteredEigenIndex hW, 1 - edgeDensity W mu < complementEigenvalue hW i
  · -- Frontier branch: a unique complement eigenvalue exceeds `q`.
    obtain ⟨i, hfront⟩ := hfrontier
    -- Package the admissible scalar parameters at this frontier index.
    let P : Scalar.AdmissibleParams :=
      { q := 1 - edgeDensity W mu
        alpha := complementEigenvalue hW i
        m := m
        q_gt_third := by linarith
        q_lt_half := by linarith
        alpha_gt_q := hfront
        alpha_le_radius := leading_eigenvalue_radius_ceiling hW i hqthird hfront
        m_odd := hm
        m_ge_nine := hm9 }
    -- Bridge equalities between the scalar record and the operator quantities.
    have hPp : P.p = edgeDensity W mu := by
      show (1 : Real) - (1 - edgeDensity W mu) = edgeDensity W mu
      ring
    have hPL : P.L = leadingEigenvalueSafeRadius hW i := by
      show Real.sqrt (P.p * P.q - P.alpha ^ 2) =
        Real.sqrt (edgeDensity W mu * (1 - edgeDensity W mu) -
          complementEigenvalue hW i ^ 2)
      congr 1
      show (1 - (1 - edgeDensity W mu)) * (1 - edgeDensity W mu) -
          complementEigenvalue hW i ^ 2 = _
      ring
    -- The master-defect coefficients equal `P.A`, `P.B`, and its baseline defect equals `P.R`.
    have hAeq :
        2 * leadingEigenvalueSafeRadius hW i ^ (m - 2) +
          (m : Real) * directedKernel (edgeDensity W mu) m (complementEigenvalue hW i) = P.A := by
      show _ = 2 * P.L ^ (P.m - 2) + (P.m : Real) * P.k P.alpha
      rw [P.k_eq_directedKernel P.alpha
            ((neg_nonpos.mpr P.p_pos.le).trans P.alpha_nonneg)
            (ne_of_gt (add_pos P.p_pos P.alpha_pos)),
        hPL, hPp]
    have hBeq :
        2 * leadingEigenvalueSafeRadius hW i ^ (m - 2) +
          (m : Real) * directedKernel (edgeDensity W mu) m
            (leadingEigenvalueSafeRadius hW i) = P.B := by
      show _ = 2 * P.L ^ (P.m - 2) + (P.m : Real) * P.k P.L
      rw [P.k_eq_directedKernel P.L
            ((neg_nonpos.mpr P.p_pos.le).trans P.L_nonneg)
            (ne_of_gt (add_pos_of_pos_of_nonneg P.p_pos P.L_nonneg)),
        hPL, hPp]
    have hReq :
        complementEigenvalue hW i ^ m + leadingEigenvalueSafeRadius hW i ^ m -
          edgeDensity W mu * (1 - edgeDensity W mu) ^ (m - 1) = P.R := by
      show _ = P.alpha ^ P.m + P.L ^ P.m - P.p * P.q ^ (P.m - 1)
      rw [hPL, hPp]
    -- Vector alignment between the two couplings (complement vs. original centered degree).
    have hc2 :
        inner Real (centeredDegreeL2 (isGraphon_compl hW)) (centeredEigenmode hW i) ^ 2 =
          inner Real (centeredDegreeL2 hW) (centeredEigenmode hW i) ^ 2 := by
      rw [centeredDegreeL2_compl_eq_neg hW, inner_neg_left]; ring
    have hgs2 :
        ‖centeredDegreeL2 (isGraphon_compl hW) -
            inner Real (centeredDegreeL2 (isGraphon_compl hW)) (centeredEigenmode hW i) •
              centeredEigenmode hW i‖ ^ 2 =
          ‖centeredDegreeL2 hW -
            inner Real (centeredDegreeL2 hW) (centeredEigenmode hW i) •
              centeredEigenmode hW i‖ ^ 2 := by
      have hv :
          centeredDegreeL2 (isGraphon_compl hW) -
              inner Real (centeredDegreeL2 (isGraphon_compl hW)) (centeredEigenmode hW i) •
                centeredEigenmode hW i =
            -(centeredDegreeL2 hW -
              inner Real (centeredDegreeL2 hW) (centeredEigenmode hW i) •
                centeredEigenmode hW i) := by
        rw [centeredDegreeL2_compl_eq_neg hW, inner_neg_left, neg_smul]; abel
      rw [hv, norm_neg]
    -- The master defect.
    have hmaster :=
      graphon_leading_eigenvalue_defect_lower_bound_directed hW i hp1 hm hm3
    dsimp only at hmaster
    rw [hAeq, hBeq, hReq] at hmaster
    -- The envelope bound at the master-defect coefficients.
    have hqposC : 0 < edgeDensity (compl W) mu := by
      rw [edgeDensity_compl hW]; linarith
    have hfrontC : edgeDensity (compl W) mu < complementEigenvalue hW i := by
      rw [edgeDensity_compl hW]; exact hfront
    have halphaHalf : complementEigenvalue hW i < 1 / 2 :=
      complement_leading_eigenvalue_lt_half hW i hqthird hfront
    have hLalpha : leadingEigenvalueSafeRadius hW i < complementEigenvalue hW i :=
      leadingEigenvalueSafeRadius_lt_complementEigenvalue hW i hqthird hfront
    have henv :=
      graphon_envelope_bound hW i hqposC hfrontC halphaHalf hLalpha
        (A := P.A) (B := P.B) P.A_nonneg P.B_pos
    dsimp only at henv
    rw [← hPL, edgeDensity_compl hW, hc2, hgs2] at henv
    change
      P.C * Scalar.psi P.xi P.rho <=
        P.A * inner Real (centeredDegreeL2 hW) (centeredEigenmode hW i) ^ 2 +
          P.B * ‖centeredDegreeL2 hW -
            inner Real (centeredDegreeL2 hW) (centeredEigenmode hW i) •
              centeredEigenmode hW i‖ ^ 2 at henv
    -- The scalar target.
    have hst : P.R <= P.C * Scalar.psi P.xi P.rho := P.scalar_target
    linarith [hmaster, henv, hst]
  · -- No-frontier branch: every complement eigenvalue is at most `q`.
    simp only [not_exists, not_lt] at hfrontier
    exact cycle_bound_of_eigenvalues_le_q hW hm hm3 hp1 hfrontier

end OddCycleBound.IntermediateRegion
