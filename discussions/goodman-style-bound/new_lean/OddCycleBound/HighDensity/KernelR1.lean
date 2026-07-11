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
import OddCycleBound.HighDensity.KernelIntegrable
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

/-- Interval-integrability of the *reflected* kernel integrand `x ↦ (ℓ+(2c−x))^{-m}·ρ(q+(2c−x))` on
`[a,b]`, when `2c−x ≥ 0` throughout. -/
lemma kernel_refl_intervalIntegrable {ℓ : ℝ} (hℓ : 0 < ℓ) (m t : ℕ) (q c a b : ℝ)
    (hpos : ∀ x ∈ Set.uIcc a b, 0 ≤ 2 * c - x) :
    IntervalIntegrable
      (fun x => 1 / (ℓ + (2 * c - x)) ^ m * rho (2 * t + 1) m (q + (2 * c - x))) volume a b := by
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.mul (ContinuousOn.div continuousOn_const (by fun_prop) (fun x hx => ?_)) ?_
  · have := hpos x hx; positivity
  · exact (by unfold rho; fun_prop : Continuous fun x => rho (2 * t + 1) m (q + (2 * c - x))).continuousOn

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

/-- **`cₙ > 1/2` bound (G building block).**  For `q ∈ [0,1/3]`, `t ≥ 2` (`n = 2t+1 ≥ 5`),
`(q+ε)^{2t} ≤ ½(p−ε)^{2t+1}` (`ε=(1-2q)/4`, `p=1-q`).  Uses `(q+ε)/(p−ε) ≤ 5/7`, `(5/7)^{2t} ≤ (5/7)^4`,
and `(5/7)^4 ≤ ½(p−ε)` (`p−ε ≥ 7/12`).  This gives `ρ0 = (m/n)(p−ε)^n − (q+ε)^{2t} ≥ ½(m/n)(p−ε)^n`. -/
lemma cn_bound {t : ℕ} (ht : 2 ≤ t) {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 3) :
    (q + (1 - 2 * q) / 4) ^ (2 * t) ≤ 1 / 2 * (1 - (q + (1 - 2 * q) / 4)) ^ (2 * t + 1) := by
  set ε := (1 - 2 * q) / 4 with hε
  have hqε : 0 ≤ q + ε := by rw [hε]; linarith
  have hpε : (7 : ℝ) / 12 ≤ 1 - (q + ε) := by rw [hε]; nlinarith [hq]
  have hratio : q + ε ≤ 5 / 7 * (1 - (q + ε)) := by rw [hε]; nlinarith [hq]
  calc (q + ε) ^ (2 * t)
      ≤ (5 / 7 * (1 - (q + ε))) ^ (2 * t) := pow_le_pow_left₀ hqε hratio _
    _ = (5 / 7) ^ (2 * t) * (1 - (q + ε)) ^ (2 * t) := by rw [mul_pow]
    _ ≤ (5 / 7) ^ 4 * (1 - (q + ε)) ^ (2 * t) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ ≤ 1 / 2 * (1 - (q + ε)) ^ (2 * t + 1) := by
        have h1 : (5 / 7 : ℝ) ^ 4 ≤ 1 / 2 * (1 - (q + ε)) := by nlinarith [hpε]
        calc (5 / 7) ^ 4 * (1 - (q + ε)) ^ (2 * t)
            ≤ 1 / 2 * (1 - (q + ε)) * (1 - (q + ε)) ^ (2 * t) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = 1 / 2 * (1 - (q + ε)) ^ (2 * t + 1) := by rw [pow_succ]; ring

/-- Numeric check for `m = 7`: `(11/84)² ≤ (7/288)(61/47)⁷`. -/
lemma const_seven : (11 / 84 : ℝ) ^ 2 ≤ 7 / 288 * (61 / 47) ^ 7 := by norm_num

/-- Numeric check for `m ≥ 9` (at `m = 9`): `(5/12)² ≤ (7/288)(61/47)⁹`. -/
lemma const_nine : (5 / 12 : ℝ) ^ 2 ≤ 7 / 288 * (61 / 47) ^ 9 := by norm_num

/-- **The `η²` bound (G).**  `η² ≤ (7/288)(61/47)^m` (`m = 2t+3`), using `η ≤ 11/84` for `m=7`
(`t=2`) and `η ≤ 5/12` for `m≥9` (`t≥3`), plus `(61/47)^m` monotonicity. -/
lemma const_final {η : ℝ} {t : ℕ} (ht : 2 ≤ t) (hη0 : 0 ≤ η)
    (hη7 : t = 2 → η ≤ 11 / 84) (hη9 : 3 ≤ t → η ≤ 5 / 12) :
    η ^ 2 ≤ 7 / 288 * (61 / 47) ^ (2 * t + 3) := by
  rcases Nat.lt_or_ge t 3 with h | h
  · have ht2 : t = 2 := by omega
    subst ht2
    have hb : η ≤ 11 / 84 := hη7 rfl
    calc η ^ 2 ≤ (11 / 84) ^ 2 := by nlinarith [hη0]
      _ ≤ 7 / 288 * (61 / 47) ^ (2 * 2 + 3) := by norm_num
  · have hb : η ≤ 5 / 12 := hη9 h
    calc η ^ 2 ≤ (5 / 12) ^ 2 := by nlinarith [hη0]
      _ ≤ 7 / 288 * (61 / 47) ^ 9 := const_nine
      _ ≤ 7 / 288 * (61 / 47) ^ (2 * t + 3) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (by norm_num)

/-- **`η² ≤ ½·ε·(p−ε)·((ℓ+3ε)/(ℓ+ε))^m` (G, combined).**  The constant comparison `eq:r1-compare`,
combining `const_final`, `ratio_bound`, and `ε ≥ 1/12`, `p−ε ≥ 7/12`. -/
lemma eta_sq_le {ℓ q η : ℝ} {t : ℕ} (ht : 2 ≤ t) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 3) (hℓ0 : 0 < ℓ)
    (hℓ : ℓ < q + 1 / ((2 * t + 3 : ℕ) : ℝ)) (hη0 : 0 ≤ η)
    (hη7 : t = 2 → η ≤ 11 / 84) (hη9 : 3 ≤ t → η ≤ 5 / 12) :
    η ^ 2 ≤ 1 / 2 * ((1 - 2 * q) / 4) * (1 - (q + (1 - 2 * q) / 4))
      * ((ℓ + 3 * ((1 - 2 * q) / 4)) / (ℓ + (1 - 2 * q) / 4)) ^ (2 * t + 3) := by
  have hm7 : (7 : ℕ) ≤ 2 * t + 3 := by omega
  have hεb : (1 : ℝ) / 12 ≤ (1 - 2 * q) / 4 := by linarith
  have hpεb : (7 : ℝ) / 12 ≤ 1 - (q + (1 - 2 * q) / 4) := by nlinarith
  have hratio : (61 : ℝ) / 47 ≤ (ℓ + 3 * ((1 - 2 * q) / 4)) / (ℓ + (1 - 2 * q) / 4) :=
    ratio_bound hm7 hq hℓ0 hℓ
  have hratiopow : (61 / 47 : ℝ) ^ (2 * t + 3)
      ≤ ((ℓ + 3 * ((1 - 2 * q) / 4)) / (ℓ + (1 - 2 * q) / 4)) ^ (2 * t + 3) :=
    pow_le_pow_left₀ (by norm_num) hratio _
  calc η ^ 2 ≤ 7 / 288 * (61 / 47) ^ (2 * t + 3) := const_final ht hη0 hη7 hη9
    _ = 1 / 2 * (1 / 12) * (7 / 12) * (61 / 47) ^ (2 * t + 3) := by ring
    _ ≤ 1 / 2 * ((1 - 2 * q) / 4) * (1 - (q + (1 - 2 * q) / 4))
          * ((ℓ + 3 * ((1 - 2 * q) / 4)) / (ℓ + (1 - 2 * q) / 4)) ^ (2 * t + 3) := by
        apply mul_le_mul _ hratiopow (by positivity) (by positivity)
        nlinarith [hεb, hpεb]

/-- **Surplus ≥ deficit (G, algebraic core).**  `D_upper ≤ Σ_lower` (`n = 2t+1`, `m = 2t+3`,
`ε=(1-2q)/4`, `b = n/m − q`, `η = b − 3ε ≥ 0`), combining `cn_bound` (`ρ0 ≥ ½(m/n)(p−ε)^n`), the
identity `1 − (m/n)(q+3ε) = (m/n)η`, and `eta_sq_le`. -/
lemma surplus_ge_deficit {ℓ q b : ℝ} {t : ℕ} (ht : 2 ≤ t) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 3)
    (hℓ0 : 0 < ℓ) (hℓ : ℓ < q + 1 / ((2 * t + 3 : ℕ) : ℝ))
    (hb : b = (2 * (t : ℝ) + 1) / ((2 * t + 3 : ℕ) : ℝ) - q)
    (hη0 : 0 ≤ b - 3 * ((1 - 2 * q) / 4))
    (hη7 : t = 2 → b - 3 * ((1 - 2 * q) / 4) ≤ 11 / 84)
    (hη9 : 3 ≤ t → b - 3 * ((1 - 2 * q) / 4) ≤ 5 / 12) :
    (b - 3 * ((1 - 2 * q) / 4))
        * ((q + 3 * ((1 - 2 * q) / 4)) ^ (2 * t) / (ℓ + 3 * ((1 - 2 * q) / 4)) ^ (2 * t + 3)
          * (1 - ((2 * t + 3 : ℕ) : ℝ) / (2 * (t : ℝ) + 1) * (q + 3 * ((1 - 2 * q) / 4))))
      ≤ (1 - 2 * q) / 4 * (1 / (ℓ + (1 - 2 * q) / 4) ^ (2 * t + 3)
          * (((2 * t + 3 : ℕ) : ℝ) / (2 * (t : ℝ) + 1) * (1 - (q + (1 - 2 * q) / 4)) ^ (2 * t + 1)
            - (q + (1 - 2 * q) / 4) ^ (2 * t))) := by
  set ε := (1 - 2 * q) / 4 with hε
  set n : ℝ := (2 * (t : ℝ) + 1) with hn
  set m : ℝ := ((2 * t + 3 : ℕ) : ℝ) with hm
  set η := b - 3 * ε with hηdef
  have hnpos : 0 < n := by rw [hn]; positivity
  have hmpos : 0 < m := by rw [hm]; positivity
  have hmn : n ≤ m := by rw [hn, hm]; push_cast; linarith
  have hR1 : 1 ≤ m / n := by rw [le_div_iff₀ hnpos]; linarith
  have hP : q + 3 * ε = 1 - (q + ε) := by rw [hε]; ring
  have hPnn : 0 ≤ 1 - (q + ε) := by rw [hε]; linarith
  have hPpos : 0 < 1 - (q + ε) := by rw [hε]; nlinarith
  have hℓε : 0 < ℓ + ε := by rw [hε]; nlinarith [hℓ0, hq]
  have hℓ3ε : 0 < ℓ + 3 * ε := by rw [hε]; nlinarith [hℓ0, hq]
  have hEpos : (0 : ℝ) < (ℓ + ε) ^ (2 * t + 3) := pow_pos hℓε _
  have hDpos : (0 : ℝ) < (ℓ + 3 * ε) ^ (2 * t + 3) := pow_pos hℓ3ε _
  -- identity B3 = (m/n)η
  have hB3 : 1 - m / n * (q + 3 * ε) = m / n * η := by
    rw [hηdef, hb]; field_simp; ring
  -- ρ0 ≥ ½(m/n)P^{n}
  have hcn := cn_bound ht hq0 hq
  rw [← hε] at hcn
  have hρ0 : 1 / 2 * (m / n) * (1 - (q + ε)) ^ (2 * t + 1)
      ≤ m / n * (1 - (q + ε)) ^ (2 * t + 1) - (q + ε) ^ (2 * t) := by
    nlinarith [hcn, mul_le_mul_of_nonneg_right (sub_nonneg.mpr hR1)
      (pow_nonneg hPnn (2 * t + 1)), pow_nonneg hPnn (2 * t + 1)]
  -- η² comparison
  have hηsq := eta_sq_le ht hq0 hq hℓ0 hℓ hη0 hη7 hη9
  rw [← hε] at hηsq
  -- cleared core: η²(ℓ+ε)^m ≤ ½εP(ℓ+3ε)^m
  have hcore : η ^ 2 * (ℓ + ε) ^ (2 * t + 3)
      ≤ 1 / 2 * ε * (1 - (q + ε)) * (ℓ + 3 * ε) ^ (2 * t + 3) := by
    have hexp : ((ℓ + 3 * ε) / (ℓ + ε)) ^ (2 * t + 3) * (ℓ + ε) ^ (2 * t + 3)
        = (ℓ + 3 * ε) ^ (2 * t + 3) := by
      rw [div_pow, div_mul_cancel₀ _ (ne_of_gt hEpos)]
    calc η ^ 2 * (ℓ + ε) ^ (2 * t + 3)
        ≤ 1 / 2 * ε * (1 - (q + ε)) * ((ℓ + 3 * ε) / (ℓ + ε)) ^ (2 * t + 3) * (ℓ + ε) ^ (2 * t + 3) :=
          mul_le_mul_of_nonneg_right hηsq hEpos.le
      _ = 1 / 2 * ε * (1 - (q + ε)) * (ℓ + 3 * ε) ^ (2 * t + 3) := by rw [mul_assoc, hexp]
  -- assemble
  rw [hB3, hP,
    show η * ((1 - (q + ε)) ^ (2 * t) / (ℓ + 3 * ε) ^ (2 * t + 3) * (m / n * η))
        = m / n * η ^ 2 * (1 - (q + ε)) ^ (2 * t) / (ℓ + 3 * ε) ^ (2 * t + 3) from by ring,
    show ε * (1 / (ℓ + ε) ^ (2 * t + 3)
          * (m / n * (1 - (q + ε)) ^ (2 * t + 1) - (q + ε) ^ (2 * t)))
        = ε * (m / n * (1 - (q + ε)) ^ (2 * t + 1) - (q + ε) ^ (2 * t)) / (ℓ + ε) ^ (2 * t + 3)
        from by ring,
    div_le_div_iff₀ hDpos hEpos]
  have hεnn : 0 ≤ ε := by rw [hε]; linarith
  have hstep : m / n * η ^ 2 * (1 - (q + ε)) ^ (2 * t) * (ℓ + ε) ^ (2 * t + 3)
      ≤ ε * (1 / 2 * (m / n) * (1 - (q + ε)) ^ (2 * t + 1)) * (ℓ + 3 * ε) ^ (2 * t + 3) := by
    have hfac : (0 : ℝ) ≤ m / n * (1 - (q + ε)) ^ (2 * t) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hcore hfac
    rw [pow_succ (1 - (q + ε)) (2 * t)]
    nlinarith [hmul]
  have hfin : ε * (1 / 2 * (m / n) * (1 - (q + ε)) ^ (2 * t + 1)) * (ℓ + 3 * ε) ^ (2 * t + 3)
      ≤ ε * (m / n * (1 - (q + ε)) ^ (2 * t + 1) - (q + ε) ^ (2 * t)) * (ℓ + 3 * ε) ^ (2 * t + 3) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ0 hεnn) hDpos.le
  nlinarith [hstep, hfin]

/-- **`thm:r1`, the `m ≥ 7` integral (assembly B).**  For `t ≥ 2` (`m = 2t+3 ≥ 7`, `n = 2t+1`),
`q ∈ [0,1/3]`, `0 < ℓ < q + 1/m`:  `0 ≤ ∫₀^∞ (ℓ+s)^{-m} ρ(q+s) ds`.  Splits `(0,∞)` into
`(0,ε)(ε,3ε)(3ε,b)(b,∞)` (or `(0,4ε−b)(4ε−b,b)(b,∞)` when `b ≤ 3ε`): the reflection pair `(ε,3ε)` (or
around `2ε`) is `≥ 0`, the tail `(b,∞)` is `≥ 0`, and `surplus ≥ deficit` closes the negative window. -/
theorem r1_integral_nonneg {t : ℕ} (ht : 2 ≤ t) {q ℓ : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 3)
    (hℓ0 : 0 < ℓ) (hℓ : ℓ < q + 1 / ((2 * t + 3 : ℕ) : ℝ)) :
    0 ≤ ∫ s in Set.Ioi 0, 1 / (ℓ + s) ^ (2 * t + 3) * rho (2 * t + 1) (2 * t + 3) (q + s) := by
  have hmR : (2 * (t : ℝ) + 1) ≤ ((2 * t + 3 : ℕ) : ℝ) := by push_cast; linarith
  have hmp : (0 : ℝ) < ((2 * t + 3 : ℕ) : ℝ) := by positivity
  set ε := (1 - 2 * q) / 4 with hε
  set b := (2 * (t : ℝ) + 1) / ((2 * t + 3 : ℕ) : ℝ) - q with hbdef
  have ht' : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hεpos : 0 < ε := by rw [hε]; nlinarith [hq]
  have hbpos : 0 < b := by
    rw [hbdef, sub_pos, lt_div_iff₀ hmp]; push_cast
    nlinarith [mul_le_mul_of_nonneg_right hq (show (0:ℝ) ≤ 2 * (t:ℝ) + 3 by positivity), ht']
  have hab : 2 * ε < b := by
    have h12 : (1 : ℝ) / 2 < (2 * (t : ℝ) + 1) / ((2 * t + 3 : ℕ) : ℝ) := by
      rw [lt_div_iff₀ hmp]; push_cast; nlinarith [ht']
    rw [hε, hbdef]; linarith [h12]
  have hκpos : ∀ s : ℝ, 0 < ℓ + s → 0 ≤ 1 / (ℓ + s) ^ (2 * t + 3) := fun s h => by positivity
  -- integrability on Ioi 0 (via kernelIntegrand)
  have hint0 : IntegrableOn
      (fun s => 1 / (ℓ + s) ^ (2 * t + 3) * rho (2 * t + 1) (2 * t + 3) (q + s)) (Set.Ioi 0) :=
    kernelIntegrand_integrableOn (r := 1) (by norm_num) (by omega) q ℓ hℓ0
  -- tail (b,∞) ≥ 0
  have htail : 0 ≤ ∫ s in Set.Ioi b,
      1 / (ℓ + s) ^ (2 * t + 3) * rho (2 * t + 1) (2 * t + 3) (q + s) := by
    refine tail_nonneg _ q b (fun s hs => hκpos s (by simp only [Set.mem_Ioi] at hs; linarith))
      (fun s hs => ?_)
    simp only [Set.mem_Ioi] at hs
    refine rho_window_right t (2 * t + 3) hmR (q + s) ?_
    have hqs : (2 * (t : ℝ) + 1) / ((2 * t + 3 : ℕ) : ℝ) < q + s := by
      rw [hbdef] at hs; linarith
    rw [div_lt_iff₀ hmp] at hqs
    push_cast at hqs ⊢; nlinarith [hqs]
  -- ∫_{Ioi 0} = ∫_{0..b} + ∫_{Ioi b}
  have hsplit : (∫ s in Set.Ioi (0:ℝ), 1 / (ℓ + s) ^ (2 * t + 3) * rho (2 * t + 1) (2 * t + 3) (q + s))
      = (∫ s in (0:ℝ)..b, 1 / (ℓ + s) ^ (2 * t + 3) * rho (2 * t + 1) (2 * t + 3) (q + s))
        + ∫ s in Set.Ioi b, 1 / (ℓ + s) ^ (2 * t + 3) * rho (2 * t + 1) (2 * t + 3) (q + s) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hbpos.le,
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hint0.mono_set (fun x hx => hx.1)) (hint0.mono_set (Set.Ioi_subset_Ioi hbpos.le)),
      intervalIntegral.integral_of_le hbpos.le]
  rw [hsplit]
  -- reflection pair around 2ε is ≥ 0 (right half `(2ε, 2ε+w)`, left half `(2ε-w, 2ε)`, `0<w≤ε`)
  have hreflpair : ∀ w : ℝ, 0 ≤ w → w ≤ ε →
      0 ≤ (∫ s in (2 * ε)..(2 * ε + w), 1 / (ℓ + s) ^ (2 * t + 3) * rho (2 * t + 1) (2 * t + 3) (q + s))
        + ∫ s in (2 * ε - w)..(2 * ε), 1 / (ℓ + s) ^ (2 * t + 3) * rho (2 * t + 1) (2 * t + 3) (q + s) := by
    intro w hw0 hwε
    exact reflection_pair_nonneg hmR q (fun s => 1 / (ℓ + s) ^ (2 * t + 3)) (2 * ε) w hw0
      (by rw [hε]; ring)
      (fun x hx => hκpos x (by have := hx.1; nlinarith [hεpos]))
      (fun x hx => kappa_antitone (2 * t + 3) (by have := hx.1; nlinarith [hεpos])
        (by have := hx.2; linarith))
      (kernel_refl_intervalIntegrable hℓ0 (2 * t + 3) t q (2 * ε) (2 * ε - w) (2 * ε)
        (fun x hx => by
          rw [Set.uIcc_of_le (by linarith)] at hx; have := hx.2; nlinarith [hεpos, hw0]))
      (kernel_intervalIntegrable hℓ0 (2 * t + 3) t q (2 * ε - w) (2 * ε) (by linarith) (by linarith))
  have hmain : 0 ≤ ∫ s in (0:ℝ)..b, 1 / (ℓ + s) ^ (2 * t + 3) * rho (2 * t + 1) (2 * t + 3) (q + s) := by
    rcases le_or_gt b (3 * ε) with hble | hblt
    · -- b ≤ 3ε: reflect `(2ε,b)` against `(4ε-b,2ε)`, nonneg region `(0,4ε-b)`
      have h4b : 4 * ε - b ≤ 2 * ε := by linarith
      have h4b0 : 0 ≤ 4 * ε - b := by linarith [hab]
      have hIa := kernel_intervalIntegrable hℓ0 (2 * t + 3) t q 0 (4 * ε - b) le_rfl h4b0
      have hIb := kernel_intervalIntegrable hℓ0 (2 * t + 3) t q (4 * ε - b) b h4b0 hbpos.le
      rw [← intervalIntegral.integral_add_adjacent_intervals hIa hIb]
      have hleft : 0 ≤ ∫ s in (0:ℝ)..(4 * ε - b), 1 / (ℓ + s) ^ (2 * t + 3) * rho (2 * t + 1) (2 * t + 3) (q + s) := by
        refine region_nonneg _ q 0 (4 * ε - b) h4b0 (fun s hs => hκpos s (by have := hs.1; linarith)) (fun s hs => ?_)
        refine rho_window_left t (2 * t + 3) hmR (q + s) ?_
        have h2ε : 2 * ε = 1 / 2 - q := by rw [hε]; ring
        linarith [hs.2, h4b, h2ε]
      -- reflection over (4ε-b, b) with w = b-2ε
      have hpair := hreflpair (b - 2 * ε) (by linarith [hab]) (by linarith)
      have hadj := intervalIntegral.integral_add_adjacent_intervals
        (kernel_intervalIntegrable hℓ0 (2 * t + 3) t q (4 * ε - b) (2 * ε) h4b0 (by linarith))
        (kernel_intervalIntegrable hℓ0 (2 * t + 3) t q (2 * ε) b (by linarith) hbpos.le)
      rw [show 2 * ε + (b - 2 * ε) = b from by ring, show 2 * ε - (b - 2 * ε) = 4 * ε - b from by ring]
        at hpair
      rw [← hadj]
      linarith [hleft, hpair]
    · -- b > 3ε: surplus + reflection(ε,3ε) + deficit, with surplus ≥ deficit
      have hI1 := kernel_intervalIntegrable hℓ0 (2 * t + 3) t q 0 ε le_rfl hεpos.le
      have hIεb := kernel_intervalIntegrable hℓ0 (2 * t + 3) t q ε b hεpos.le hbpos.le
      have hI2 := kernel_intervalIntegrable hℓ0 (2 * t + 3) t q ε (3 * ε) hεpos.le (by linarith)
      have hI3 := kernel_intervalIntegrable hℓ0 (2 * t + 3) t q (3 * ε) b (by linarith) hbpos.le
      rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hIεb,
        ← intervalIntegral.integral_add_adjacent_intervals hI2 hI3]
      -- reflection ∫_{ε..3ε} ≥ 0
      have hrefl : 0 ≤ ∫ s in ε..(3 * ε), 1 / (ℓ + s) ^ (2 * t + 3) * rho (2 * t + 1) (2 * t + 3) (q + s) := by
        have hpair := hreflpair ε hεpos.le le_rfl
        have hadj := intervalIntegral.integral_add_adjacent_intervals
          (kernel_intervalIntegrable hℓ0 (2 * t + 3) t q ε (2 * ε) hεpos.le (by linarith))
          (kernel_intervalIntegrable hℓ0 (2 * t + 3) t q (2 * ε) (3 * ε) (by linarith) (by linarith))
        rw [show 2 * ε + ε = 3 * ε from by ring, show 2 * ε - ε = ε from by ring] at hpair
        rw [← hadj]; linarith [hpair]
      -- deficit hypotheses on [3ε, b]
      have hℓm2 : ((2 * t + 3 : ℕ) : ℝ) * ℓ < ((2 * t + 3 : ℕ) : ℝ) * q + 1 := by
        have := mul_lt_mul_of_pos_left hℓ hmp
        rwa [mul_add, mul_one_div, div_self (ne_of_gt hmp)] at this
      have hsign : ∀ s ∈ Set.Icc (3 * ε) b, 2 * (t : ℝ) * (ℓ + s) ≤ ((2 * t + 3 : ℕ) : ℝ) * (q + s) := by
        intro s hs; have hs3 := hs.1; rw [hε] at hs3; push_cast at hℓm2 ⊢
        nlinarith [hℓm2, hs3, hq, hℓ0, ht']
      have hB0 : ∀ s ∈ Set.Icc (3 * ε) b, 0 ≤ 1 - ((2 * t + 3 : ℕ) : ℝ) / (2 * (t : ℝ) + 1) * (q + s) := by
        intro s hs; have hn2 : (0:ℝ) < 2 * (t:ℝ) + 1 := by positivity
        rw [sub_nonneg, div_mul_eq_mul_div, div_le_one hn2]
        have hqb : q + s ≤ (2 * (t : ℝ) + 1) / ((2 * t + 3 : ℕ) : ℝ) := by
          have := hs.2; rw [hbdef] at this; linarith
        rw [le_div_iff₀ hmp] at hqb; push_cast at hqb ⊢; nlinarith [hqb]
      have hu1 : ∀ s ∈ Set.Icc (3 * ε) b, q + s ≤ 1 := by
        intro s hs
        have hqb : q + s ≤ (2 * (t : ℝ) + 1) / ((2 * t + 3 : ℕ) : ℝ) := by
          have := hs.2; rw [hbdef] at this; linarith
        have : (2 * (t : ℝ) + 1) / ((2 * t + 3 : ℕ) : ℝ) ≤ 1 := by rw [div_le_one hmp]; push_cast; linarith
        linarith
      have hρ0 : 0 ≤ ((2 * t + 3 : ℕ) : ℝ) / (2 * (t : ℝ) + 1) * (1 - (q + ε)) ^ (2 * t + 1) - (q + ε) ^ (2 * t) := by
        have hcn := cn_bound ht hq0 hq
        rw [← hε] at hcn
        have hR1 : (1:ℝ) ≤ ((2 * t + 3 : ℕ) : ℝ) / (2 * (t : ℝ) + 1) := by
          rw [le_div_iff₀ (by positivity)]; push_cast; linarith
        nlinarith [hcn, mul_le_mul_of_nonneg_right (sub_nonneg.mpr hR1)
          (pow_nonneg (by rw [hε]; linarith : (0:ℝ) ≤ 1 - (q + ε)) (2 * t + 1)),
          pow_nonneg (by rw [hε]; linarith : (0:ℝ) ≤ 1 - (q + ε)) (2 * t + 1)]
      have hsurp := surplus_bound hℓ0 (m := 2 * t + 3) q ε hq0 hεpos.le (by rw [hε]; linarith) hρ0
      have hdef := deficit_bound hℓ0 (m := 2 * t + 3) (t := t) (by omega) (by omega) q ε b
        hεpos.le (by linarith) hq0 hsign hB0 hu1
      have hsgd := surplus_ge_deficit ht hq0 hq hℓ0 hℓ hbdef (by linarith [hε])
        (fun h => by rw [hbdef, h]; push_cast; nlinarith [hq])
        (fun _ => by
          rw [hbdef]
          have hle : (2 * (t : ℝ) + 1) / ((2 * t + 3 : ℕ) : ℝ) ≤ 1 := by rw [div_le_one hmp]; push_cast; linarith
          nlinarith [hle, hq])
      rw [← hε] at hsgd
      linarith [hsurp, hrefl, hdef, hsgd]
  linarith [hmain, htail]

end OddCycleBound.HighDensity
