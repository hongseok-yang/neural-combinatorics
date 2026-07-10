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
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory Set
open scoped BigOperators

namespace OddCycleBound.HighDensity

/-- **Deficit factor monotonicity (E).**  The factor `A(s) = (q+s)^{2t}/(ℓ+s)^m` is antitone on
`[s₀,b]` whenever `2t·(ℓ+s) ≤ m·(q+s)` there (`= (n-1)(ℓ-q) ≤ (2r+1)(q+s)` in the paper's form).  Via
the sign of the logarithmic derivative. -/
lemma deficit_factor_antitone {ℓ : ℝ} (hℓ : 0 < ℓ) {m t : ℕ} (ht : t ≠ 0) (hm : m ≠ 0)
    (q s₀ b : ℝ) (hs₀ : 0 ≤ s₀) (hq : 0 ≤ q)
    (hsign : ∀ s ∈ Set.Icc s₀ b, 2 * (t : ℝ) * (ℓ + s) ≤ (m : ℝ) * (q + s)) :
    AntitoneOn (fun s => (q + s) ^ (2 * t) / (ℓ + s) ^ m) (Set.Icc s₀ b) := by
  have hcont : ContinuousOn (fun s => (q + s) ^ (2 * t) / (ℓ + s) ^ m) (Set.Icc s₀ b) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun s hs => ?_)
    have : 0 < ℓ + s := by have := hs.1; linarith
    positivity
  refine antitoneOn_of_deriv_nonpos (convex_Icc s₀ b) hcont (fun s hs => ?_) (fun s hs => ?_)
  · rw [interior_Icc, Set.mem_Ioo] at hs
    have hℓs : 0 < ℓ + s := by linarith [hs.1]
    exact ((by fun_prop : DifferentiableAt ℝ (fun s => (q + s) ^ (2 * t)) s).div
      (by fun_prop) (by positivity)).differentiableWithinAt
  · rw [interior_Icc, Set.mem_Ioo] at hs
    have hs0 : 0 ≤ s := le_trans hs₀ hs.1.le
    have hℓs : 0 < ℓ + s := by linarith
    have hqs : 0 ≤ q + s := by linarith
    have hne : (ℓ + s) ^ m ≠ 0 := by positivity
    have hn : HasDerivAt (fun s => (q + s) ^ (2 * t)) (2 * (t : ℝ) * (q + s) ^ (2 * t - 1)) s := by
      have h := ((hasDerivAt_id s).const_add q).pow (2 * t)
      simp only [mul_one] at h
      exact_mod_cast h
    have hd : HasDerivAt (fun s => (ℓ + s) ^ m) ((m : ℝ) * (ℓ + s) ^ (m - 1)) s := by
      have h := ((hasDerivAt_id s).const_add ℓ).pow m
      simp only [mul_one] at h
      exact_mod_cast h
    have hderiv : HasDerivAt (fun s => (q + s) ^ (2 * t) / (ℓ + s) ^ m)
        ((2 * (t : ℝ) * (q + s) ^ (2 * t - 1) * (ℓ + s) ^ m
          - (q + s) ^ (2 * t) * ((m : ℝ) * (ℓ + s) ^ (m - 1))) / ((ℓ + s) ^ m) ^ 2) s :=
      hn.div hd hne
    rw [hderiv.deriv]
    have e1 : (q + s) ^ (2 * t) = (q + s) * (q + s) ^ (2 * t - 1) := by
      conv_lhs => rw [show 2 * t = (2 * t - 1) + 1 from by omega]
      rw [pow_succ']
    have e2 : (ℓ + s) ^ m = (ℓ + s) * (ℓ + s) ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 from by omega]
      rw [pow_succ']
    have hN : 2 * (t : ℝ) * (q + s) ^ (2 * t - 1) * (ℓ + s) ^ m
        - (q + s) ^ (2 * t) * ((m : ℝ) * (ℓ + s) ^ (m - 1))
        = (q + s) ^ (2 * t - 1) * (ℓ + s) ^ (m - 1)
          * (2 * (t : ℝ) * (ℓ + s) - (m : ℝ) * (q + s)) := by
      rw [e1, e2]; ring
    rw [div_nonpos_iff]
    right
    refine ⟨?_, by positivity⟩
    rw [hN]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (by linarith [hsign s ⟨hs.1.le, hs.2.le⟩])

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

/-- Interval-integrability of the deficit integrand `(q+s)^{2t}/(ℓ+s)^m·(1−(m/n)(q+s))` on `[a,b]`
(endpoints `≥ 0`). -/
lemma deficit_integrand_intervalIntegrable {ℓ : ℝ} (hℓ : 0 < ℓ) (m t : ℕ) (q a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun s => (q + s) ^ (2 * t) / (ℓ + s) ^ m
      * (1 - (m : ℝ) / (2 * (t : ℝ) + 1) * (q + s))) volume a b := by
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop) (fun s hs => ?_)) (by fun_prop)
  have hs0 : 0 ≤ s := by
    rcases le_total a b with h | h
    · rw [Set.uIcc_of_le h] at hs; linarith [hs.1]
    · rw [Set.uIcc_of_ge h] at hs; linarith [hs.1]
  positivity

/-- **Deficit bound (E, `eq:r1-D`).**  On `(3ε,b)` the kernel integral is at least
`−(b−3ε)·A(3ε)·B(3ε)`, where `A(s)=(q+s)^{2t}/(ℓ+s)^m` (antitone, `deficit_factor_antitone`) and
`B(s)=1−(m/n)(q+s) ≥ 0` (antitone): the negative part is bounded by the length times the left-endpoint
value. -/
lemma deficit_bound {ℓ : ℝ} (hℓ : 0 < ℓ) {m t : ℕ} (ht : t ≠ 0) (hm : m ≠ 0) (q ε b : ℝ)
    (hε0 : 0 ≤ ε) (h3εb : 3 * ε ≤ b) (hq : 0 ≤ q)
    (hsign : ∀ s ∈ Set.Icc (3 * ε) b, 2 * (t : ℝ) * (ℓ + s) ≤ (m : ℝ) * (q + s))
    (hB0 : ∀ s ∈ Set.Icc (3 * ε) b, 0 ≤ 1 - (m : ℝ) / (2 * (t : ℝ) + 1) * (q + s))
    (hu1 : ∀ s ∈ Set.Icc (3 * ε) b, q + s ≤ 1) :
    -((b - 3 * ε) * ((q + 3 * ε) ^ (2 * t) / (ℓ + 3 * ε) ^ m
        * (1 - (m : ℝ) / (2 * (t : ℝ) + 1) * (q + 3 * ε))))
      ≤ ∫ s in (3 * ε)..b, 1 / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s) := by
  have h3ε0 : 0 ≤ 3 * ε := by linarith
  have hAanti := deficit_factor_antitone hℓ ht hm q (3 * ε) b h3ε0 hq hsign
  have hmono : ∀ s ∈ Set.Icc (3 * ε) b,
      (q + s) ^ (2 * t) / (ℓ + s) ^ m * (1 - (m : ℝ) / (2 * (t : ℝ) + 1) * (q + s))
        ≤ (q + 3 * ε) ^ (2 * t) / (ℓ + 3 * ε) ^ m
          * (1 - (m : ℝ) / (2 * (t : ℝ) + 1) * (q + 3 * ε)) := by
    intro s hs
    have hAs := hAanti ⟨le_refl _, h3εb⟩ hs hs.1
    have hBs : 1 - (m : ℝ) / (2 * (t : ℝ) + 1) * (q + s)
        ≤ 1 - (m : ℝ) / (2 * (t : ℝ) + 1) * (q + 3 * ε) := by
      have : (0 : ℝ) ≤ (m : ℝ) / (2 * (t : ℝ) + 1) := by positivity
      nlinarith [hs.1]
    exact mul_le_mul hAs hBs (hB0 s hs) (by positivity)
  have hpt : ∀ s ∈ Set.Icc (3 * ε) b,
      -((q + s) ^ (2 * t) / (ℓ + s) ^ m * (1 - (m : ℝ) / (2 * (t : ℝ) + 1) * (q + s)))
        ≤ 1 / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s) := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans h3ε0 hs.1
    have hℓs : 0 < ℓ + s := by linarith
    have hrn := rho_neg t m (q + s) (hu1 s hs)
    have hκ0 : (0 : ℝ) ≤ 1 / (ℓ + s) ^ m := by positivity
    rw [show -((q + s) ^ (2 * t) / (ℓ + s) ^ m * (1 - (m : ℝ) / (2 * (t : ℝ) + 1) * (q + s)))
          = 1 / (ℓ + s) ^ m
            * (-((q + s) ^ (2 * t) * (1 - (m : ℝ) / (2 * (t : ℝ) + 1) * (q + s)))) from by ring]
    exact mul_le_mul_of_nonneg_left (by linarith [hrn]) hκ0
  have hint_κρ := kernel_intervalIntegrable hℓ m t q (3 * ε) b h3ε0 (by linarith)
  have hint_d := deficit_integrand_intervalIntegrable hℓ m t q (3 * ε) b h3ε0 (by linarith)
  have h3 : (∫ s in (3 * ε)..b,
        -((q + s) ^ (2 * t) / (ℓ + s) ^ m * (1 - (m : ℝ) / (2 * (t : ℝ) + 1) * (q + s))))
      ≤ ∫ s in (3 * ε)..b, 1 / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s) :=
    intervalIntegral.integral_mono_on (by linarith) hint_d.neg hint_κρ hpt
  have h5 := region_upper_bound (by linarith : (3 * ε : ℝ) ≤ b) hint_d hmono
  rw [intervalIntegral.integral_neg] at h3
  linarith [h3, h5]

/-- **Ratio bound (G building block).**  For `q ∈ [0,1/3]`, `m ≥ 7`, `0 < ℓ < q + 1/m`
(`ε = (1-2q)/4`):  `(ℓ+3ε)/(ℓ+ε) ≥ 61/47`.  Reduces (cross-multiplying) to `40ε ≥ 7ℓ`, which follows
from `7ℓ < 7q + 7/m ≤ 7q + 1 ≤ 10 − 20q = 40ε`. -/
lemma ratio_bound {ℓ q : ℝ} {m : ℕ} (hm : 7 ≤ m) (hq : q ≤ 1 / 3) (hℓ0 : 0 < ℓ)
    (hℓ : ℓ < q + 1 / m) :
    (61 : ℝ) / 47 ≤ (ℓ + 3 * ((1 - 2 * q) / 4)) / (ℓ + (1 - 2 * q) / 4) := by
  have hm7 : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m := by linarith
  have hεpos : (0 : ℝ) < (1 - 2 * q) / 4 := by nlinarith [hq]
  have hden : (0 : ℝ) < ℓ + (1 - 2 * q) / 4 := by linarith
  have h7m : (7 : ℝ) / m ≤ 1 := by rw [div_le_one hmp]; exact_mod_cast hm
  have h7ℓ : 7 * ℓ < 7 * q + 7 / m := by
    have h := mul_lt_mul_of_pos_left hℓ (show (0:ℝ) < 7 from by norm_num)
    rw [show (7:ℝ) * (q + 1 / m) = 7 * q + 7 / m from by ring] at h; exact h
  rw [le_div_iff₀ hden]
  nlinarith [h7ℓ, h7m, hq]

end OddCycleBound.HighDensity
