import OddCycleBound.IntermediateRegion.LinearLowZeta
import OddCycleBound.IntermediateRegion.LinearN7Mid
import OddCycleBound.IntermediateRegion.LinearHighZeta
import OddCycleBound.IntermediateRegion.LinearBroad
import OddCycleBound.IntermediateRegion.QuadraticBranch

/-!
# The scalar target `R ≤ C·ψ` (paper §9–§10, `prop:linear-branch` line 3527, `thm:scalar-target`)

`linear_core` dispatches `eq:linear-core` across the branch lemmas (`prop:linear-branch`), and
`scalar_target` combines the quadratic (`2ρξ ≤ 1`) and linear (`2ρξ > 1`) branches into the single
scalar inequality `R ≤ C·ψ(ξ,ρ)` that discharges the whole intermediate region.
-/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

namespace AdmissibleParams

variable (P : AdmissibleParams)

/-- **Paper `prop:linear-branch` (line 3527):** `eq:linear-core` holds for every odd `N ≥ 7`, by
dispatching on `v`, `N`, and `ζ` across the five branch lemmas. -/
theorem linear_core :
    P.chartTN ≤ ((P.chartN : ℝ) + 2) * P.chartCxi * (1 - P.ell) * (P.chartSigma - P.ell)
      * P.chartSigma ^ (P.chartN - 1) := by
  by_cases hv : 5 / 8 ≤ P.chartV
  · exact P.linear_large_v hv
  · push_neg at hv
    by_cases hN9 : 9 ≤ P.chartN
    · by_cases hζ : (P.chartN : ℝ) ≤ P.chartZeta
      · exact P.linear_high_zeta hζ (le_of_lt hv)
      · exact P.linear_low_zeta hN9 (le_of_lt (not_le.mp hζ))
    · have hN7 : P.chartN = 7 := by
        obtain ⟨t, ht⟩ := P.m_odd
        have hm := P.m_ge_nine
        have hlt : P.chartN < 9 := not_le.mp hN9
        unfold chartN at hlt ⊢; omega
      by_cases hζ7 : P.chartZeta ≤ 7
      · by_cases hv14 : P.chartV ≤ 1 / 4
        · exact P.linear_N7_small_v hN7 hζ7 hv14
        · exact P.linear_N7_middle_v hN7 hζ7 (le_of_lt (not_le.mp hv14)) (le_of_lt hv)
      · exact P.linear_high_zeta (by rw [hN7]; push_cast; linarith [not_le.mp hζ7]) (le_of_lt hv)

/-- **Paper `thm:scalar-target` (eq:scalar-target, line 2216):** `R ≤ C·ψ(ξ,ρ)` — the single scalar
inequality to which the whole intermediate region reduces.  Trichotomy on `2ρξ ≤ 1` (quadratic branch)
vs `2ρξ > 1` (linear branch). -/
theorem scalar_target : P.R ≤ P.C * psi P.xi P.rho := by
  by_cases h : 2 * P.rho * P.xi ≤ 1
  · exact P.quadratic_branch h
  · exact P.scalar_target_of_linear_core (not_le.mp h) P.linear_core

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
