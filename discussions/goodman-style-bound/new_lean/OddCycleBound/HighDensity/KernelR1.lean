/-
# High-density theorem — the `r = 1` diagonal positivity (M5, `thm:r1`, the repaired proof)

`thm:r1` (`sec:r1`): for `r = 1`, `m = n+2`, `n ≥ 3` odd, `q ∈ [0,1/3]`, `ℓ ∈ [−1/2,1/2]`,
`P̃_{m,1}(q,ℓ) ≥ 0`.  This is the case the paper explicitly *corrected* (`rmk:r1-history`), so it is the
highest-value target for trust.

Structure (paper): the `ℓ ≤ 0` and `ℓ ≥ q+1/m` sub-cases are `thm:pointwise`/`thm:ibp`.  For
`0 < ℓ < q+1/m`, `prop:kernel` reduces to `∫₀^∞ ρ(q+s)/(ℓ+s)^m ds ≥ 0` (`r = 1` ⇒ `s^{r-1}=1`).  The
case `m = 5` is elementary (`diagKernel_five_one`); `m ≥ 7` uses the reflection + deficit/surplus
argument.

This file: the `m = 5` base case and the `prop:kernel`-reduction scaffold; the `m ≥ 7` analytic core
is the remaining piece.
-/

import OddCycleBound.HighDensity.KernelImproper

open MeasureTheory Set
open scoped BigOperators

namespace OddCycleBound.HighDensity

/-- **`thm:r1`, base case `m = 5` (`n = 3`).**  Directly from the explicit quadratic
`P̃_{5,1}(q,ℓ) = 4ℓ² + (8q−5)ℓ + 12q² − 15q + 5`, which is nonnegative for *all* real `q, ℓ`
(its `ℓ`-discriminant `−128q²+160q−55 < 0`): `= (8ℓ+8q−5)²/16 + (8q−5)²/8 + 5/16 ≥ 5/16`. -/
theorem diagKernel_nonneg_r1_five (q ℓ : ℝ) : 0 ≤ diagKernel 5 1 q ℓ := by
  rw [diagKernel_five_one]
  nlinarith [sq_nonneg (8 * ℓ + 8 * q - 5), sq_nonneg (8 * q - 5)]

/-- **`prop:kernel` reduction for `r = 1`.**  For `ℓ > 0`, since `C_{m,1}·ℓ^{m-1} > 0`, the diagonal
kernel is nonnegative iff the improper integral `∫₀^∞ (ℓ+s)^{-m} ρ_{m-2,m}(q+s) ds` is.  (`r = 1` makes
the `s^{r-1}` weight equal to `1`.) -/
theorem diagKernel_nonneg_r1_of_integral {m : ℕ} (hn : 1 ≤ m - 2 * 1) (q ℓ : ℝ) (hl : 0 < ℓ)
    (hI : 0 ≤ ∫ s in Set.Ioi (0:ℝ), s ^ (1 - 1) / (ℓ + s) ^ m * rho (m - 2 * 1) m (q + s)) :
    0 ≤ diagKernel m 1 q ℓ := by
  rw [kernel_form (by norm_num) hn q ℓ hl]
  exact mul_nonneg (mul_nonneg (Cmr_pos (by norm_num) hn).le (by positivity)) hI

end OddCycleBound.HighDensity
