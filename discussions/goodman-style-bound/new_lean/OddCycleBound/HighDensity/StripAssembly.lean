/-
# High-density theorem — diagonal-kernel case assembly (`prop:remaining` / `thm:main` case split)

The mixture theorem reduces the whole target to `0 ≤ diagKernel m r q ℓ` for odd `m ≥ 3`,
`1 ≤ r`, `2r < m`, `q ∈ [0,1/3]`, `ℓ ∈ [−1/2,1/2]`.  The paper's case partition
(`odd_cycle_lower_bound_clean.tex`, proof of `thm:main`) is:

* `r = 1`                          → `diagKernel_nonneg_r1`      (fully proved),
* `ℓ ≤ 0`                          → `diagKernel_nonneg_le_zero`,
* `2r ≥ n` (`n = m−2r`)            → `diagKernel_nonneg_two_r_ge`,
* `ℓ ≥ q + r/m`                    → `diagKernel_nonneg_ibp`,
* residual (`r≥2`, `n>2r`, `0<ℓ<q+r/m`):
    * `m ≥ 63`, `θ = r/m ≥ 1/6`, `ℓ > 2/5` → `diagKernel_nonneg_strip_right` (fully proved),
    * else `m ≥ 63`                          → `diagKernel_nonneg_strip_left` (needs `app:constants`),
    * `m ≤ 61`                               → `prop:finite`.

`diagKernel_nonneg` below assembles all of this: every non-residual case and the
`m ≥ 63`/right-reflection residual sub-case are discharged unconditionally; the two remaining
certificate families enter as the hypotheses `Hfin` (`prop:finite`, `m ≤ 61`) and `Hleft`
(`app:constants` via `diagKernel_nonneg_strip_left`).  This file also proves the two purely-polynomial
`app:constants` lower bounds `P(θ) ≥ 51` (`eq:constant-A`, `0 < θ ≤ 1/6`) and `P(θ) ≥ 72`
(`eq:constant-B`, `1/6 ≤ θ < 1/4`) — the scalar `P`-factor bounds feeding the `m ≥ 500` tail.
-/

import OddCycleBound.HighDensity.M6LeftEstimate
import OddCycleBound.HighDensity.KernelIBP

open scoped BigOperators

namespace OddCycleBound.HighDensity

/-- **`app:constants`: `P(θ) ≥ 51` for `0 < θ ≤ 1/6`** (`eq:constant-A`, the `m ≥ 500` tail).
`P(θ) = (2/3 − 2θ)/(θ(1/2 − 2θ)²)`; clears to `2/3 − 2θ − 51θ(1/2 − 2θ)² ≥ 0` (near-tight: interior
minimum `≈ 0.0065`; certified by `nlinarith` with double-root square hints near `θ ≈ 0.106`). -/
lemma P_ge_51 {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 6) :
    (2 / 3 - 2 * θ) / (θ * (1 / 2 - 2 * θ) ^ 2) ≥ 51 := by
  have hden : 0 < θ * (1 / 2 - 2 * θ) ^ 2 := by
    have : (0 : ℝ) < 1 / 2 - 2 * θ := by linarith
    positivity
  rw [ge_iff_le, le_div_iff₀ hden]
  nlinarith [hθ0, hθ, mul_nonneg hθ0.le (by linarith : (0:ℝ) ≤ 1 / 6 - θ),
    mul_nonneg (mul_nonneg hθ0.le hθ0.le) (by linarith : (0:ℝ) ≤ 1 / 6 - θ),
    mul_nonneg hθ0.le (mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 6 - θ) (by linarith : (0:ℝ) ≤ 1 / 6 - θ)),
    mul_nonneg hθ0.le (sq_nonneg (10 * θ - 1)),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 6 - θ) (sq_nonneg (10 * θ - 1)),
    mul_nonneg hθ0.le (sq_nonneg (17 * θ - 2))]

/-- **`app:constants`: `P(θ) ≥ 72` for `1/6 ≤ θ < 1/4`** (`eq:constant-B`).  Uses the factorization
`2/3 − 2θ − 72θ(1/2 − 2θ)² = −(2/3)(6θ − 1)(72θ² − 24θ + 1)`, whose sign is `≥ 0` on `[1/6, 1/4)`. -/
lemma P_ge_72 {θ : ℝ} (hθ0 : 1 / 6 ≤ θ) (hθ : θ < 1 / 4) :
    (2 / 3 - 2 * θ) / (θ * (1 / 2 - 2 * θ) ^ 2) ≥ 72 := by
  have hθpos : 0 < θ := by linarith
  have hden : 0 < θ * (1 / 2 - 2 * θ) ^ 2 := by
    have : (0 : ℝ) < 1 / 2 - 2 * θ := by linarith
    positivity
  rw [ge_iff_le, le_div_iff₀ hden]
  nlinarith [hθ0, hθ, mul_nonneg (by linarith : (0:ℝ) ≤ 6 * θ - 1)
    (by nlinarith [hθ0, hθ] : (0:ℝ) ≤ -(72 * θ ^ 2 - 24 * θ + 1))]

/-- **`prop:remaining` / `thm:main` case assembly.**  For odd `m ≥ 3`, `1 ≤ r`, `2r < m`,
`q ∈ [0,1/3]`, `ℓ ∈ [−1/2,1/2]`, the diagonal kernel is nonnegative — given the residual-strip
certificate families `Hfin` (`prop:finite`, `m ≤ 61`) and `Hleft` (`app:constants` via
`diagKernel_nonneg_strip_left`, the `θ ≤ 1/6` or `ℓ ≤ 2/5` residual sub-cases).  Every other case,
including the `m ≥ 63` right-reflection sub-case (`θ ≥ 1/6`, `ℓ > 2/5`), is discharged here. -/
theorem diagKernel_nonneg {m r : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) (hr : 1 ≤ r) (hrn : 2 * r < m)
    {q ℓ : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 3) (hℓl : -(1 / 2) ≤ ℓ) (hℓu : ℓ ≤ 1 / 2)
    (Hfin : 2 ≤ r → m ≤ 61 → 2 * r < m - 2 * r → 0 < ℓ → ℓ < q + (r : ℝ) / (m : ℝ) →
        0 ≤ diagKernel m r q ℓ)
    (Hleft : 2 ≤ r → 2 * r < m - 2 * r → 0 < ℓ → ℓ < q + (r : ℝ) / (m : ℝ) →
        (6 * r < m ∨ ℓ ≤ 2 / 5) → 0 ≤ diagKernel m r q ℓ) :
    0 ≤ diagKernel m r q ℓ := by
  have hmodd : m % 2 = 1 := Nat.odd_iff.mp hm
  rcases Nat.lt_or_ge r 2 with hr1 | hr2
  · -- `r = 1`
    have : r = 1 := by omega
    subst this
    exact diagKernel_nonneg_r1 hm hm3 hq0 hq hℓl hℓu
  -- `r ≥ 2`
  obtain ⟨t, ht⟩ : ∃ t, m - 2 * r = 2 * t + 1 := ⟨(m - 2 * r - 1) / 2, by omega⟩
  rcases le_or_gt ℓ 0 with hℓ0 | hℓ0
  · exact diagKernel_nonneg_le_zero (by omega) ht q ℓ (by linarith) hℓ0
  rcases le_or_gt (2 * t + 1) (2 * r) with h2r | h2r
  · exact diagKernel_nonneg_two_r_ge (by omega) ht h2r q ℓ
  rcases le_or_gt (q + (r : ℝ) / (m : ℝ)) ℓ with hib | hib
  · exact diagKernel_nonneg_ibp hr2 ht hq0 (by linarith) (by linarith) hib
  -- residual range: `n = m−2r > 2r`, `0 < ℓ < q + r/m`
  have hres_n : 2 * r < m - 2 * r := by omega
  rcases le_or_gt m 61 with hle61 | hgt61
  · exact Hfin hr2 hle61 hres_n hℓ0 hib
  -- `m ≥ 63`
  have hm63 : 63 ≤ m := by omega
  by_cases hcase : 6 * r < m ∨ ℓ ≤ 2 / 5
  · exact Hleft hr2 hres_n hℓ0 hib hcase
  · push_neg at hcase
    obtain ⟨h6r, hℓ25⟩ := hcase
    exact diagKernel_nonneg_strip_right (n := m - 2 * r) hm63 hmodd (by omega)
      (by omega) hres_n ht hq0 hq hℓ25

end OddCycleBound.HighDensity
