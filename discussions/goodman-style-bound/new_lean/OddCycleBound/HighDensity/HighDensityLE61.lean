/-
# High-density odd-cycle bound — the finite band `m ≤ 61`

The `m ≤ 61` capstone: the Stage A expansion reduction
(`FinalAssembly.cycle_bound_of_diagKernel_certificates`) plus the generated `Hfin`
certificate family (`Hfin.Aggregate.finKernel_all`, the `prop:finite` exact Bernstein/
Handelman certificates for all 196 residual-strip pairs with odd `9 ≤ m ≤ 61`), each verified
in-kernel by `decide +kernel` over the reflection infrastructure `HfinPolyReflect`.

On this range `finKernel_all` discharges **both** residual families: `Hfin` directly, and
`Hleft` because for `m ≤ 61` the strip-left obligation is the *same* diagonal-kernel
positivity on the same strip.  (`m ≤ 7` is vacuous: no residual pair.)
-/

import OddCycleBound.HighDensity.FinalAssembly
import OddCycleBound.HighDensity.Hfin.Aggregate

open MeasureTheory

namespace OddCycleBound.HighDensity

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

/-- **High-density odd-cycle bound, all odd `3 ≤ m ≤ 61`.**  For a graphon `W` of edge
density at least `2/3` and every odd `m` with `3 ≤ m ≤ 61`,
`p^m − p(1−p)^{m-1} ≤ cycleDensity μ W m`  (`p = edgeDensity W μ`). -/
theorem odd_cycle_bound_le61 {m : ℕ} (hW : IsGraphon W μ)
    (hp : 2 / 3 ≤ edgeDensity W μ) (hm : Odd m) (hm3 : 3 ≤ m) (hm61 : m ≤ 61) :
    edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) ≤
      cycleDensity μ W m := by
  have hq0 : (0 : ℝ) ≤ 1 - edgeDensity W μ := by linarith [edgeDensity_le_one hW]
  have hq : (1 : ℝ) - edgeDensity W μ ≤ 1 / 3 := by linarith
  refine cycle_bound_of_diagKernel_certificates hW hp hm hm3 ?_ ?_
  · -- `Hfin` via the generated certificate family
    intro r ell hr2 _ hres hl0 hlr
    exact finKernel_all hm (by omega) hm61 hr2 hres hq0 hq hl0 hlr
  · -- `Hleft` via the same family (`m ≤ 61` here, so the strip is covered by `Hfin`)
    intro r ell hr2 hres hl0 hlr _
    exact finKernel_all hm (by omega) hm61 hr2 hres hq0 hq hl0 hlr

end OddCycleBound.HighDensity
