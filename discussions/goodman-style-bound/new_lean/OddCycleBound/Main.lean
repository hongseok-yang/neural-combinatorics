/-
# High-density odd-cycle bound — the assembled theorem (`Main`)

The target (`paper_new.tex` §`sec:high-density-theorem`, project form):

> for every graphon `W` with `edgeDensity W μ ≥ 2/3` and every odd `m ≥ 3`,
> `p^m − p(1−p)^{m-1} ≤ cycleDensity μ W m`   (`p = edgeDensity W μ`).

**Currently proved, axiom-clean, for odd `m ≤ 41` and odd `m ≥ 63`.**  The two halves:

* `m ≤ 41` — `HighDensityLE41.odd_cycle_bound_le41`: the Stage A expansion reduction plus the
  generated `Hfin` family (`Hfin.Aggregate.finKernel_all`, `prop:finite`): exact
  degree-`(m−2r−1)` Bernstein/Handelman certificates for the residual-strip pairs with odd
  `9 ≤ m ≤ 41`, verified in-kernel by `decide +kernel`, discharging both `Hfin` and (on this
  range) `Hleft`;
* `m ≥ 63` — `HighDensityGE63.odd_cycle_bound_ge63`: the analytic milestone (`eq:constant-A`
  finite sweep + `constA_m500` + `constB_m63`, `Hfin` vacuous).

The band `43 ≤ m ≤ 61` is **deferred**: the `Hfin` certificates for those `m` are proven
valid (Python) and pass Lean's `decide +kernel` at higher `-M`, but their cleared identities
have >~500-bit integer coefficients whose in-kernel check exceeds ~16 GB.  Building them
(serially, at higher `-M`) removes the range hypothesis and recovers the full odd `m ≥ 3`
theorem; the infrastructure (`HfinPolyReflect`, the emitter) is already in place.
-/

import OddCycleBound.HighDensity.HighDensityGE63
import OddCycleBound.HighDensity.HighDensityLE41

open MeasureTheory

namespace OddCycleBound.HighDensity

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

/-- **High-density odd-cycle bound (currently-provable band).**  For a graphon `W` with
`edgeDensity W μ ≥ 2/3` and every odd `m` with `3 ≤ m` satisfying `m ≤ 41 ∨ 63 ≤ m`,
`p^m − p(1−p)^{m-1} ≤ cycleDensity μ W m`  (`p = edgeDensity W μ`).
Unconditional on `W` within this band, and axiom-clean.  (The excluded band `43 ≤ m ≤ 61`
is a memory-budget deferral, not a mathematical gap — see the module docstring.) -/
theorem odd_cycle_bound_main {m : ℕ} (hW : IsGraphon W μ)
    (hp : 2 / 3 ≤ edgeDensity W μ) (hm : Odd m) (hm3 : 3 ≤ m)
    (hrange : m ≤ 41 ∨ 63 ≤ m) :
    edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) ≤
      cycleDensity μ W m := by
  rcases hrange with hle | hge
  · exact odd_cycle_bound_le41 hW hp hm hm3 hle
  · exact odd_cycle_bound_ge63 hW hp hm hge

end OddCycleBound.HighDensity
