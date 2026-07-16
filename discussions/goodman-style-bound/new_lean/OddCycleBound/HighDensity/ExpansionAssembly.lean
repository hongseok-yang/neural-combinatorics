/-
# High-density theorem — assembly after the finite-atomic expansion (E6)

This module is the public Stage A endpoint.  It composes the graphon reduction, the E5b defect
identity, the finite Krylov/atomic representation, and the expansion positivity theorem.  Thus a
pointwise proof of diagonal-kernel nonnegativity can be consumed directly by the existing graphon
cycle-bound API.

Keeping this theorem separate makes P/E1/E2/E5b's target explicit and prevents the operator layer
from depending on the analytic strip implementation.
-/

import OddCycleBound.HighDensity.Expansion
import OddCycleBound.HighDensity.GraphonReduction
import OddCycleBound.HighDensity.GraphonKrylovBridge
import OddCycleBound.HighDensity.DefectPowerSeries

open MeasureTheory

namespace OddCycleBound.HighDensity

variable {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega → Omega → ℝ}
variable {ι : Type*} [Fintype ι]

/-- **E6, generic finite-atomic assembly.**  This compatibility endpoint accepts an externally
supplied atomic expansion identity.  The graphon-specific route below now constructs and identifies
the required atoms internally. -/
theorem cycle_bound_of_atomic_expansion {m : ℕ} (hW : IsGraphon W mu)
    (hm : Odd m) (hm3 : 3 ≤ m) (w lam : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hlam : ∀ i, lam i ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2))
    (hdiag : ∀ r, 1 ≤ r → 2 * r < m →
      ∀ ell ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2), 0 ≤ diagKernel m r (1 - edgeDensity W mu) ell)
    (hexp : neckSum W mu m =
      edgeDensity W mu ^ m - edgeDensity W mu * (1 - edgeDensity W mu) ^ (m - 1) +
        momentPhi m (1 - edgeDensity W mu) (atomicMoment w lam)) :
    edgeDensity W mu ^ m - edgeDensity W mu * (1 - edgeDensity W mu) ^ (m - 1) ≤
      cycleDensity mu W m := by
  apply cycle_bound_of_neckSum hW hm hm3
  rw [hexp]
  linarith [momentPhi_nonneg_of_atomic hm hm3 (1 - edgeDensity W mu) w lam hw hlam hdiag]

/-- **Stage A capstone.**  Pointwise diagonal-kernel nonnegativity implies the required lower bound
for the actual graphon necklace sum.  E5b and the finite Krylov representation are discharged
internally. -/
theorem neckSum_ge_baseline_of_diagKernel_nonneg {m : ℕ} (hW : IsGraphon W mu)
    (hm : Odd m) (hm3 : 3 ≤ m)
    (hdiag : ∀ r, 1 ≤ r ∧ 2 * r < m →
      ∀ ell ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2),
        0 ≤ diagKernel m r (1 - edgeDensity W mu) ell) :
    edgeDensity W mu ^ m - edgeDensity W mu * (1 - edgeDensity W mu) ^ (m - 1) ≤
      neckSum W mu m := by
  rw [neckSum_eq_baseline_add_momentPhi hW hm hm3]
  linarith [momentPhi_specMoment_nonneg hm hm3 (isGraphon_compl hW)
    (1 - edgeDensity W mu) hdiag]

/-- **Integrated Stage A endpoint.**  Pointwise diagonal-kernel nonnegativity implies the graphon
odd-cycle lower bound through the existing `cycle_bound_of_neckSum` reduction. -/
theorem cycle_bound_of_diagKernel_nonneg {m : ℕ} (hW : IsGraphon W mu)
    (hm : Odd m) (hm3 : 3 ≤ m)
    (hdiag : ∀ r, 1 ≤ r ∧ 2 * r < m →
      ∀ ell ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2),
        0 ≤ diagKernel m r (1 - edgeDensity W mu) ell) :
    edgeDensity W mu ^ m - edgeDensity W mu * (1 - edgeDensity W mu) ^ (m - 1) ≤
      cycleDensity mu W m :=
  cycle_bound_of_neckSum hW hm hm3
    (neckSum_ge_baseline_of_diagKernel_nonneg hW hm hm3 hdiag)

/-- Compatibility name for the original E6 endpoint. -/
theorem cycle_bound_of_momentPhi_identity {m : ℕ} (hW : IsGraphon W mu)
    (hm : Odd m) (hm3 : 3 ≤ m)
    (hdiag : ∀ r, 1 ≤ r ∧ 2 * r < m →
      ∀ ell ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2),
        0 ≤ diagKernel m r (1 - edgeDensity W mu) ell) :
    edgeDensity W mu ^ m - edgeDensity W mu * (1 - edgeDensity W mu) ^ (m - 1) ≤
      cycleDensity mu W m :=
  cycle_bound_of_diagKernel_nonneg hW hm hm3 hdiag

end OddCycleBound.HighDensity
