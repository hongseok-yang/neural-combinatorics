/-
# High-density odd-cycle bound — the currently provable theorem (`Main`)

The target (`paper_new.tex` §`sec:high-density-theorem`, project form) is:

> for every graphon `W` with `edgeDensity W μ ≥ 2/3` and every odd `m ≥ 3`,
> `p^m − p(1−p)^{m-1} ≤ cycleDensity μ W m`   (`p = edgeDensity W μ`).

**What is proven now (axiom-clean).**  The diagonal-kernel case assembly
(`StripAssembly.diagKernel_nonneg`) reduces the bound, for each `m`, to two residual certificate
families on the strip `r ≥ 2`, `n = m−2r > 2r`, `0 < ℓ < q + r/m`:

* `Hleft` (`app:constants`, the analytic tail) — fully discharged for **`m ≥ 63`**
  (`M6StripLeftA.diagKernel_nonneg_strip_left_ab`; A-branch via the `eq:constant-A` finite sweep +
  `constA_m500`, B-branch via `constB_m63`);
* `Hfin` (`prop:finite`, the finite-Bernstein certificates for `m ≤ 61`) — **not yet formalised**.

For `m ≤ 7` the residual strip is *empty* (`2r < m−2r` with `r ≥ 2` forces `4r < m`, i.e. `m ≥ 9`),
so both `Hfin` and `Hleft` are vacuous and the bound holds unconditionally.  Hence the currently
provable range is exactly

> **`m ∈ {3, 5, 7}`  or  `m ≥ 63`.**

The open gap is the finite band `9 ≤ m ≤ 61`, which needs the `Hfin` finite-Bernstein certificates
(each pair certifies at Bernstein subdivision depth 0, but the degree-`(m−2r)` polynomial identity
is beyond a single `ring` for the higher-degree pairs — see the project notes).
-/

import OddCycleBound.HighDensity.HighDensityGE63

open MeasureTheory

namespace OddCycleBound.HighDensity

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

/-- **High-density odd-cycle bound — currently provable range.**  For a graphon `W` with
`edgeDensity W μ ≥ 2/3` and odd `m` with `m ≤ 7` or `m ≥ 63`,
`p^m − p(1−p)^{m-1} ≤ cycleDensity μ W m`  (`p = edgeDensity W μ`).  Unconditional and axiom-clean.
The remaining band `9 ≤ m ≤ 61` awaits the `Hfin` finite-Bernstein certificates. -/
theorem odd_cycle_bound_main {m : ℕ} (hW : IsGraphon W μ)
    (hp : 2 / 3 ≤ edgeDensity W μ) (hm : Odd m) (hm3 : 3 ≤ m)
    (hrange : m ≤ 7 ∨ 63 ≤ m) :
    edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) ≤
      cycleDensity μ W m := by
  rcases hrange with hlo | hhi
  · -- `m ∈ {3,5,7}`: the residual strip is empty, so `Hfin` and `Hleft` are vacuous
    refine cycle_bound_of_diagKernel_certificates hW hp hm hm3 ?_ ?_
    · intro r _ hr2 _ hres _ _; omega
    · intro r _ hr2 hres _ _ _; omega
  · -- `m ≥ 63`: the assembled analytic milestone
    exact odd_cycle_bound_ge63 hW hp hm hhi

end OddCycleBound.HighDensity
