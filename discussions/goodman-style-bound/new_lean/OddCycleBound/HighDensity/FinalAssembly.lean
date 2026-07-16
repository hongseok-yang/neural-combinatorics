/-
# High-density theorem — integration of Stage A with diagonal-kernel case assembly

This module joins the public Stage A endpoint to the existing `StripAssembly.diagKernel_nonneg`
case split.  Consequently the only remaining inputs to the graphon cycle bound are precisely the
two residual certificate families already exposed by `diagKernel_nonneg`.
-/

import OddCycleBound.HighDensity.ExpansionAssembly
import OddCycleBound.HighDensity.StripAssembly

open MeasureTheory

namespace OddCycleBound.HighDensity

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

/-- **Integrated Stage A/diagonal-kernel assembly.**  For a graphon of density at least `2/3`,
the existing diagonal-kernel case split and the completed Stage A expansion reduce the odd-cycle
bound exactly to the finite and left-strip certificate families `Hfin` and `Hleft`. -/
theorem cycle_bound_of_diagKernel_certificates {m : ℕ} (hW : IsGraphon W μ)
    (hp : 2 / 3 ≤ edgeDensity W μ) (hm : Odd m) (hm3 : 3 ≤ m)
    (Hfin : ∀ r ell, 2 ≤ r → m ≤ 61 → 2 * r < m - 2 * r →
      0 < ell → ell < 1 - edgeDensity W μ + (r : ℝ) / (m : ℝ) →
        0 ≤ diagKernel m r (1 - edgeDensity W μ) ell)
    (Hleft : ∀ r ell, 2 ≤ r → 2 * r < m - 2 * r →
      0 < ell → ell < 1 - edgeDensity W μ + (r : ℝ) / (m : ℝ) →
      (6 * r < m ∨ ell ≤ 2 / 5) →
        0 ≤ diagKernel m r (1 - edgeDensity W μ) ell) :
    edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) ≤
      cycleDensity μ W m := by
  apply cycle_bound_of_diagKernel_nonneg hW hm hm3
  intro r hr ell hell
  apply diagKernel_nonneg hm hm3 hr.1 hr.2
  · linarith [edgeDensity_le_one hW]
  · linarith
  · linarith [hell.1]
  · exact hell.2
  · exact Hfin r ell
  · exact Hleft r ell

end OddCycleBound.HighDensity
