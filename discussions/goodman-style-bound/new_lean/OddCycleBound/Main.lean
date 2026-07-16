/-
# High-density odd-cycle bound — the complete theorem (`Main`)

The target (`paper_new.tex` §`sec:high-density-theorem`, project form):

> for every graphon `W` with `edgeDensity W μ ≥ 2/3` and every odd `m ≥ 3`,
> `p^m − p(1−p)^{m-1} ≤ cycleDensity μ W m`   (`p = edgeDensity W μ`).

**Now proved for all odd `m ≥ 3`, axiom-clean.**  The two halves:

* `m ≤ 61` — `HighDensityLE61.odd_cycle_bound_le61`: the Stage A expansion reduction plus the
  generated `Hfin` family (`Hfin.Aggregate.finKernel_all`, `prop:finite`): exact
  degree-`(m−2r−1)` Bernstein/Handelman certificates for all 196 residual-strip pairs with odd
  `9 ≤ m ≤ 61`, verified in-kernel by `decide +kernel` over the reflection infrastructure
  `HfinPolyReflect`, discharging both `Hfin` and (on this range) `Hleft`;
* `m ≥ 63` — `HighDensityGE63.odd_cycle_bound_ge63`: the analytic milestone (`eq:constant-A`
  finite sweep + `constA_m500` + `constB_m63`, `Hfin` vacuous).

Odd `m` skips `62`, so the two halves cover everything.
-/

import OddCycleBound.HighDensity.HighDensityGE63
import OddCycleBound.HighDensity.HighDensityLE61

open MeasureTheory

namespace OddCycleBound.HighDensity

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

/-- **High-density odd-cycle bound.**  For a graphon `W` with `edgeDensity W μ ≥ 2/3` and
every odd `m ≥ 3`,
`p^m − p(1−p)^{m-1} ≤ cycleDensity μ W m`  (`p = edgeDensity W μ`).
Unconditional and axiom-clean. -/
theorem odd_cycle_bound {m : ℕ} (hW : IsGraphon W μ)
    (hp : 2 / 3 ≤ edgeDensity W μ) (hm : Odd m) (hm3 : 3 ≤ m) :
    edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) ≤
      cycleDensity μ W m := by
  rcases le_or_lt m 61 with hle | hgt
  · exact odd_cycle_bound_le61 hW hp hm hm3 hle
  · -- odd `m > 61` means `m ≥ 63`
    have hm63 : 63 ≤ m := by rcases hm with ⟨k, hk⟩; omega
    exact odd_cycle_bound_ge63 hW hp hm hm63

/-- The previous milestone form (kept for compatibility): the bound on
`m ≤ 7 ∨ m ≥ 63`, now an instance of `odd_cycle_bound`. -/
theorem odd_cycle_bound_main {m : ℕ} (hW : IsGraphon W μ)
    (hp : 2 / 3 ≤ edgeDensity W μ) (hm : Odd m) (hm3 : 3 ≤ m)
    (_hrange : m ≤ 7 ∨ 63 ≤ m) :
    edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) ≤
      cycleDensity μ W m :=
  odd_cycle_bound hW hp hm hm3

end OddCycleBound.HighDensity
