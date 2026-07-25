/-
# Dense region (Phase D) — uniform diagonal-kernel positivity and the `p ≥ 2/3` cycle bound
  (paper §4, `thm:dense-region`, lines 1774–1799)

Assembles the three regimes of `eq:dense-diagonal-target` into the uniform statement
`0 ≤ diagKernel m r q ℓ` for all odd `m ≥ 3`, `1 ≤ r`, `2r < m`, `q ∈ [0,1/3]`, `ℓ ∈ [−½,½]`:

* `2r ≥ n` — `diagKernel_nonneg_two_r_ge` (empty negative window, D3, already proven);
* `ℓ ≤ 0` — `diagKernel_nonneg_le_zero` (`q ≤ 1/2`, D2, already proven);
* `ℓ > 0` — the beta-integral + gamma-smoothing route, whose positivity is the single remaining
  analytic input `hpos` (`= kernel_form` + `ShiftedGammaPositive` (D7) + the gamma moment
  inequality (D6)).  It is threaded as a hypothesis so this file is complete and certificate-free.

Feeding the uniform positivity to `cycle_bound_of_diagKernel_nonneg` yields the dense-region
odd-cycle bound for `edgeDensity ≥ 2/3`.
-/
import OddCycleBound.DenseRegion.KernelForm
import OddCycleBound.DenseRegion.ExpansionAssembly

open MeasureTheory
open scoped BigOperators

namespace OddCycleBound.DenseRegion

/-- The `ℓ > 0` diagonal positivity, packaged as a reusable hypothesis: for odd `n = 2t+1`,
`0 ≤ q ≤ 1/3` and `ℓ > 0`, `0 ≤ diagKernel m r q ℓ`.  Discharged by the beta/gamma route. -/
abbrev DiagKernelPosEll : Prop :=
  ∀ {m r t : ℕ}, 1 ≤ r → m - 2 * r = 2 * t + 1 → ∀ {q ℓ : ℝ},
    0 ≤ q → q ≤ 1 / 3 → 0 < ℓ → 0 ≤ diagKernel m r q ℓ

/-- **Uniform diagonal-kernel positivity** (`eq:dense-diagonal-target`), given the `ℓ>0` input. -/
theorem diagKernel_nonneg_uniform (hpos : DiagKernelPosEll)
    {m r : ℕ} (hm : Odd m) (hr : 1 ≤ r) (hres : 2 * r < m) {q ℓ : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 3) (hℓ : ℓ ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) :
    0 ≤ diagKernel m r q ℓ := by
  obtain ⟨t, ht⟩ : ∃ t, m - 2 * r = 2 * t + 1 := by
    rcases hm with ⟨k, hk⟩; exact ⟨k - r, by omega⟩
  by_cases hn2r : 2 * t + 1 ≤ 2 * r
  · exact diagKernel_nonneg_two_r_ge (by omega) ht hn2r q ℓ
  · by_cases hℓ0 : ℓ ≤ 0
    · exact diagKernel_nonneg_le_zero (by omega) ht q ℓ (by linarith) hℓ0
    · exact hpos hr ht hq0 hq (not_le.mp hℓ0)

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

/-- **Dense-region odd-cycle bound** (`thm:dense-region`), given the `ℓ>0` diagonal positivity.
For `edgeDensity ≥ 2/3` and odd `m ≥ 3`,
`edgeDensity^m − edgeDensity·(1−edgeDensity)^{m-1} ≤ cycleDensity μ W m`. -/
theorem dense_region_cycle_bound (hpos : DiagKernelPosEll)
    {m : ℕ} (hW : IsGraphon W μ) (hp : 2 / 3 ≤ edgeDensity W μ) (hm : Odd m) (hm3 : 3 ≤ m) :
    edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) ≤
      cycleDensity μ W m := by
  refine cycle_bound_of_diagKernel_nonneg hW hm hm3 (fun r hr ell hell => ?_)
  exact diagKernel_nonneg_uniform hpos hm hr.1 hr.2
    (by linarith [edgeDensity_le_one hW]) (by linarith) hell

end OddCycleBound.DenseRegion
