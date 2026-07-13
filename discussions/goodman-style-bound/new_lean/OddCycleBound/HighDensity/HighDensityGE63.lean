/-
# High-density odd-cycle bound — the `m ≥ 63` milestone

This is the assembled high-density theorem for **every odd `m ≥ 63`**, unconditional and axiom-clean.
It composes:

* the Stage A expansion capstone `cycle_bound_of_diagKernel_certificates` (`FinalAssembly`), which
  reduces the graphon cycle bound to the two residual certificate families `Hfin` (`prop:finite`,
  `m ≤ 61`) and `Hleft` (`app:constants`, the residual strip-left);
* the residual strip-left provider `diagKernel_nonneg_strip_left_ab` (`M6StripLeftA`), which
  discharges `Hleft` outright for `m ≥ 63` (A-branch via the `eq:constant-A` finite sweep +
  `constA_m500`; B-branch via `constB_m63`).

For `m ≥ 63` the finite family `Hfin` is **vacuous** (its `m ≤ 61` guard is false), so no
finite-Bernstein certificates are needed: the whole bound follows.  The remaining gap to *all* odd
`m ≥ 3` is exactly the finite range `3 ≤ m ≤ 61` (`Hfin`, `prop:finite`).
-/

import OddCycleBound.HighDensity.FinalAssembly
import OddCycleBound.HighDensity.M6StripLeftA

open MeasureTheory

namespace OddCycleBound.HighDensity

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

/-- **High-density odd-cycle bound, all odd `m ≥ 63`.**  For a graphon `W` of edge density at least
`2/3` and every odd `m ≥ 63`,
`p^m − p(1−p)^{m-1} ≤ cycleDensity μ W m`  (`p = edgeDensity W μ`).
Unconditional and axiom-clean; the only remaining range for the full theorem is `3 ≤ m ≤ 61`. -/
theorem odd_cycle_bound_ge63 {m : ℕ} (hW : IsGraphon W μ)
    (hp : 2 / 3 ≤ edgeDensity W μ) (hm : Odd m) (hm63 : 63 ≤ m) :
    edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) ≤
      cycleDensity μ W m := by
  refine cycle_bound_of_diagKernel_certificates hW hp hm (by omega) ?_ ?_
  · -- `Hfin` is vacuous for `m ≥ 63` (its `m ≤ 61` hypothesis is false)
    intro r ell _ hm61 _ _ _; omega
  · -- `Hleft` via the residual strip-left both-branch provider
    intro r ell hr2 hres hℓ0 hℓr hcase
    obtain ⟨t, ht⟩ : ∃ t, m - 2 * r = 2 * t + 1 := ⟨(m - 2 * r - 1) / 2, by
      rcases hm with ⟨k, hk⟩; omega⟩
    have hq0 : (0 : ℝ) ≤ 1 - edgeDensity W μ := by linarith [edgeDensity_le_one hW]
    have hq : (1 : ℝ) - edgeDensity W μ ≤ 1 / 3 := by linarith
    exact diagKernel_nonneg_strip_left_ab hr2 (by omega) (by omega) ht hm63 hq0 hq hℓ0 hℓr hcase

end OddCycleBound.HighDensity
