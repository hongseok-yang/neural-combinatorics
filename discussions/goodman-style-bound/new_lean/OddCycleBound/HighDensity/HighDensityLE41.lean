/-
# High-density odd-cycle bound — the finite band `m ≤ 41`

The `m ≤ 41` capstone: the Stage A expansion reduction
(`FinalAssembly.cycle_bound_of_diagKernel_certificates`) plus the generated `Hfin`
certificate family (`Hfin.Aggregate.finKernel_all`, the `prop:finite` exact Handelman
certificates for the residual-strip pairs with odd `9 ≤ m ≤ 41`).

**Range note.**  The certificate family is proven, for *every* odd `9 ≤ m ≤ 61`, by an exact
depth-0 Bernstein reflection identity (`hfin_certs.py` + `HfinPolyReflect`).  For `m ≥ 43`
the cleared identity has >~500-bit integer coefficients and its in-kernel `decide +kernel`
exceeds ~16 GB, so those families are *deferred* (build them serially at higher `-M`); the
band assembled here is the axiom-clean `m ≤ 41` part.  (`m ≤ 7` is vacuous: no residual pair.)

On this range `finKernel_all` discharges **both** residual families: `Hfin` directly, and
`Hleft` because for `m ≤ 41` the strip-left obligation is the *same* diagonal-kernel
positivity on the same strip.
-/

import OddCycleBound.HighDensity.FinalAssembly
import OddCycleBound.HighDensity.Hfin.Aggregate

open MeasureTheory

namespace OddCycleBound.HighDensity

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

/-- **High-density odd-cycle bound, all odd `3 ≤ m ≤ 41`.**  For a graphon `W` of edge
density at least `2/3` and every odd `m` with `3 ≤ m ≤ 41`,
`p^m − p(1−p)^{m-1} ≤ cycleDensity μ W m`  (`p = edgeDensity W μ`). -/
theorem odd_cycle_bound_le41 {m : ℕ} (hW : IsGraphon W μ)
    (hp : 2 / 3 ≤ edgeDensity W μ) (hm : Odd m) (hm3 : 3 ≤ m) (hm41 : m ≤ 41) :
    edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) ≤
      cycleDensity μ W m := by
  have hq0 : (0 : ℝ) ≤ 1 - edgeDensity W μ := by linarith [edgeDensity_le_one hW]
  have hq : (1 : ℝ) - edgeDensity W μ ≤ 1 / 3 := by linarith
  refine cycle_bound_of_diagKernel_certificates hW hp hm hm3 ?_ ?_
  · -- `Hfin` via the generated certificate family
    intro r ell hr2 _ hres hl0 hlr
    exact finKernel_all hm (by omega) hm41 hr2 hres hq0 hq hl0 hlr
  · -- `Hleft` via the same family (`m ≤ 41` here, so the strip is covered by `Hfin`)
    intro r ell hr2 hres hl0 hlr _
    exact finKernel_all hm (by omega) hm41 hr2 hres hq0 hq hl0 hlr

end OddCycleBound.HighDensity
