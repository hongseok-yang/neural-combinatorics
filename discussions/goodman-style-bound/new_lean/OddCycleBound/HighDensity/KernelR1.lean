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
import OddCycleBound.HighDensity.KernelReflect

open MeasureTheory Set
open scoped BigOperators

namespace OddCycleBound.HighDensity

/-- The kernel weight `κ(s) = (ℓ+s)^{-m}` is nonincreasing on `s > −ℓ`. -/
lemma kappa_antitone {ℓ : ℝ} (m : ℕ) {s₁ s₂ : ℝ} (h1 : 0 < ℓ + s₁) (h12 : s₁ ≤ s₂) :
    1 / (ℓ + s₂) ^ m ≤ 1 / (ℓ + s₁) ^ m := by
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ h1.le (by linarith) m

/-- The `r=1` kernel integrand `s ↦ (ℓ+s)^{-m}·ρ(q+s)` is interval-integrable on `[a,b]` when the
endpoints are `≥ 0` (so `ℓ+s > 0` throughout): it is continuous there. -/
lemma kernel_intervalIntegrable {ℓ : ℝ} (hℓ : 0 < ℓ) (m t : ℕ) (q a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun s => 1 / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.mul
  · refine ContinuousOn.div continuousOn_const (by fun_prop) (fun s hs => ?_)
    have hs0 : 0 ≤ s := by
      rcases le_total a b with h | h
      · rw [Set.uIcc_of_le h] at hs; linarith [hs.1]
      · rw [Set.uIcc_of_ge h] at hs; linarith [hs.1]
    positivity
  · exact (by unfold rho; fun_prop : Continuous fun s => rho (2 * t + 1) m (q + s)).continuousOn

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

/-- **Surplus bound (F, `eq:r1-S`).**  On `(0,ε)` the kernel integral is at least `ε·(ℓ+ε)^{-m}·ρ0`,
where `ρ0 = (m/n)(1−(q+ε))ⁿ − (q+ε)^{n-1}` (`n = 2t+1`) is the constant lower bound of `ρ(q+s)` there
(via `rho_left_surplus` + power monotonicity) and `κ = (ℓ+s)^{-m}` is decreasing. -/
lemma surplus_bound {ℓ : ℝ} (hℓ : 0 < ℓ) {m t : ℕ} (q ε : ℝ) (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (hpε : 0 ≤ 1 - (q + ε))
    (hρ0 : 0 ≤ (m : ℝ) / (2 * (t : ℝ) + 1) * (1 - (q + ε)) ^ (2 * t + 1) - (q + ε) ^ (2 * t)) :
    ε * (1 / (ℓ + ε) ^ m
        * ((m : ℝ) / (2 * (t : ℝ) + 1) * (1 - (q + ε)) ^ (2 * t + 1) - (q + ε) ^ (2 * t)))
      ≤ ∫ s in (0:ℝ)..ε, 1 / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s) := by
  set ρ0 := (m : ℝ) / (2 * (t : ℝ) + 1) * (1 - (q + ε)) ^ (2 * t + 1) - (q + ε) ^ (2 * t) with hρ0def
  have key : ∀ s ∈ Set.Icc (0:ℝ) ε,
      1 / (ℓ + ε) ^ m * ρ0 ≤ 1 / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s) := by
    intro s hs
    obtain ⟨hs0, hsε⟩ := hs
    have hρ : ρ0 ≤ rho (2 * t + 1) m (q + s) := by
      have h1 := rho_left_surplus t m (q + s) (by linarith)
      have hp : (1 - (q + ε)) ^ (2 * t + 1) ≤ (1 - (q + s)) ^ (2 * t + 1) :=
        pow_le_pow_left₀ hpε (by linarith) _
      have hq2 : (q + s) ^ (2 * t) ≤ (q + ε) ^ (2 * t) :=
        pow_le_pow_left₀ (by linarith) (by linarith) _
      have hmn : (0 : ℝ) ≤ (m : ℝ) / (2 * (t : ℝ) + 1) := by positivity
      have hstep : ρ0
          ≤ (m : ℝ) / (2 * (t : ℝ) + 1) * (1 - (q + s)) ^ (2 * t + 1) - (q + s) ^ (2 * t) := by
        rw [hρ0def]; nlinarith [mul_le_mul_of_nonneg_left hp hmn, hq2]
      linarith [h1, hstep]
    have hκ : 1 / (ℓ + ε) ^ m ≤ 1 / (ℓ + s) ^ m := kappa_antitone m (by linarith) hsε
    calc 1 / (ℓ + ε) ^ m * ρ0
        ≤ 1 / (ℓ + ε) ^ m * rho (2 * t + 1) m (q + s) :=
          mul_le_mul_of_nonneg_left hρ (by positivity)
      _ ≤ 1 / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s) :=
          mul_le_mul_of_nonneg_right hκ (le_trans hρ0 hρ)
  have hint := kernel_intervalIntegrable hℓ m t q 0 ε le_rfl hε
  simpa using region_lower_bound hε hint key

end OddCycleBound.HighDensity
