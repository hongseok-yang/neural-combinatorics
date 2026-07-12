/-
# High-density theorem — the residual strip, left-estimate machinery (M6, `lem:left-estimate`)

The residual strip (`eq:remaining-range`): `q ≤ 1/3`, `r ≥ 2`, `n = m−2r > 2r`, `0 < ℓ < q+r/m`,
`n = 2t+1` odd, `m ≥ 63`.  `lem:left-estimate` handles `0 < θ ≤ 1/6` and `1/6 ≤ θ < 1/4 ∧ ℓ ≤ 2/5`.
Unlike the right-reflection case it uses **no reflection**: the surplus `Σ` over `(0,ε)` (`ε = a/2`,
`a = 1/2 − q`) dominates the deficit `D` over the negative window `(a,b)` (`b = ν − q`, `ν = n/m`),
while `(ε,a]` and `(b,∞)` have `ρ ≥ 0`.

This file builds the analytic core:
* `power_integral_lower`  — `∫₀^ε s^{r-1}/(ℓ+s)^m ≥ ε^r/(r(ℓ+ε)^m)`  (monotone weight + `∫ s^{r-1}`).
* `left_surplus_bound` (`eq:tail-S`) — the surplus lower bound over `(0,ε)`.
* `affine_integral` + `left_deficit_bound` (`eq:tail-D`) — the deficit upper bound over `(a,b)`.
* `left_estimate_of_deficit_le_surplus` — reduces `0 ≤ diagKernel` to the **single scalar inequality**
  `D ≤ Σ` (which is `app:constants`, deferred: a finite rational sweep `63 ≤ m ≤ 499` plus an
  `rpow`-tail argument for `m ≥ 500`).
-/

import OddCycleBound.HighDensity.M6Reflection
import OddCycleBound.HighDensity.KernelR1
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory Set
open scoped BigOperators

namespace OddCycleBound.HighDensity

/-- Interval-integrability of the bare kernel weight `s ↦ s^{r-1}/(ℓ+s)^m` on `[a,b]` (nonneg
endpoints). -/
lemma kappa_intervalIntegrable {ℓ : ℝ} (hℓ : 0 < ℓ) (m r : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun s => s ^ (r - 1) / (ℓ + s) ^ m) volume a b := by
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun s hs => ?_)
  have hs0 : 0 ≤ s := by
    rcases le_total a b with h | h
    · rw [Set.uIcc_of_le h] at hs; linarith [hs.1]
    · rw [Set.uIcc_of_ge h] at hs; linarith [hs.1]
  positivity

/-- **`∫₀^ε s^{r-1}/(ℓ+s)^m ≥ ε^r/(r(ℓ+ε)^m)`.**  Bound the weight below by `1/(ℓ+ε)^m` (decreasing)
and integrate `∫₀^ε s^{r-1} = ε^r/r`. -/
lemma power_integral_lower {ℓ : ℝ} (hℓ : 0 < ℓ) {m r : ℕ} (hr : 1 ≤ r) (ε : ℝ) (hε : 0 ≤ ε) :
    ε ^ r / ((r : ℝ) * (ℓ + ε) ^ m) ≤ ∫ s in (0:ℝ)..ε, s ^ (r - 1) / (ℓ + s) ^ m := by
  have hmono : ∀ s ∈ Set.Icc (0:ℝ) ε, s ^ (r - 1) / (ℓ + ε) ^ m ≤ s ^ (r - 1) / (ℓ + s) ^ m := by
    intro s hs
    obtain ⟨hs0, hsε⟩ := hs
    have h := mul_le_mul_of_nonneg_left (kappa_antitone m (by linarith : (0:ℝ) < ℓ + s) hsε)
      (pow_nonneg hs0 (r - 1))
    rwa [mul_one_div, mul_one_div] at h
  have hintL : IntervalIntegrable (fun s => s ^ (r - 1) / (ℓ + ε) ^ m) volume 0 ε :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hintR : IntervalIntegrable (fun s => s ^ (r - 1) / (ℓ + s) ^ m) volume 0 ε :=
    kappa_intervalIntegrable hℓ m r 0 ε le_rfl hε
  have hle := intervalIntegral.integral_mono_on hε hintL hintR hmono
  -- evaluate the left integral exactly
  have hFTC : (∫ s in (0:ℝ)..ε, s ^ (r - 1)) = ε ^ r / (r : ℝ) := by
    rw [integral_pow, zero_pow (show (r - 1) + 1 ≠ 0 by omega), sub_zero,
      show (r - 1) + 1 = r from Nat.sub_add_cancel hr, Nat.cast_sub hr, Nat.cast_one,
      show (r : ℝ) - 1 + 1 = (r : ℝ) from by ring]
  have hLval : (∫ s in (0:ℝ)..ε, s ^ (r - 1) / (ℓ + ε) ^ m) = ε ^ r / ((r : ℝ) * (ℓ + ε) ^ m) := by
    rw [intervalIntegral.integral_div, hFTC, div_div]
  rw [hLval] at hle
  exact hle

/-- **`eq:tail-S` (surplus lower bound).**  On `(0,ε)`, `ρ(q+s) ≥ C₀` where
`C₀ = (m/n)(1−(q+ε))ⁿ − (q+ε)^{n-1}` (`rho_left_surplus` + monotonicity), and the weight integrates to
`≥ ε^r/(r(ℓ+ε)^m)`, so the surplus is `≥ C₀·ε^r/(r(ℓ+ε)^m)`. -/
lemma left_surplus_bound {ℓ : ℝ} (hℓ : 0 < ℓ) {m r t : ℕ} (hr : 1 ≤ r) (q ε : ℝ)
    (hq : 0 ≤ q) (hε : 0 ≤ ε) (hp : q + ε ≤ 1)
    (hconst : 0 ≤ (m : ℝ) / (2 * (t : ℝ) + 1) * (1 - (q + ε)) ^ (2 * t + 1) - (q + ε) ^ (2 * t)) :
    ((m : ℝ) / (2 * (t : ℝ) + 1) * (1 - (q + ε)) ^ (2 * t + 1) - (q + ε) ^ (2 * t))
        * (ε ^ r / ((r : ℝ) * (ℓ + ε) ^ m))
      ≤ ∫ s in (0:ℝ)..ε, s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s) := by
  set C₀ := (m : ℝ) / (2 * (t : ℝ) + 1) * (1 - (q + ε)) ^ (2 * t + 1) - (q + ε) ^ (2 * t) with hC₀
  -- pointwise `ρ(q+s) ≥ C₀` on `[0,ε]`
  have hρpt : ∀ s ∈ Set.Icc (0:ℝ) ε, C₀ ≤ rho (2 * t + 1) m (q + s) := by
    intro s hs
    obtain ⟨hs0, hsε⟩ := hs
    have h1 := rho_left_surplus t m (q + s) (by linarith)
    have hp1 : (1 - (q + ε)) ^ (2 * t + 1) ≤ (1 - (q + s)) ^ (2 * t + 1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have hp2 : (q + s) ^ (2 * t) ≤ (q + ε) ^ (2 * t) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have hmn : (0 : ℝ) ≤ (m : ℝ) / (2 * (t : ℝ) + 1) := by positivity
    rw [hC₀]; nlinarith [mul_le_mul_of_nonneg_left hp1 hmn, hp2, h1]
  -- `∫ κρ ≥ C₀·∫ κ`
  have hintκ : IntervalIntegrable (fun s => s ^ (r - 1) / (ℓ + s) ^ m) volume 0 ε :=
    kappa_intervalIntegrable hℓ m r 0 ε le_rfl hε
  have hintκρ : IntervalIntegrable
      (fun s => s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s)) volume 0 ε :=
    kernelr_intervalIntegrable hℓ m r t q 0 ε le_rfl hε
  have hstep : C₀ * (∫ s in (0:ℝ)..ε, s ^ (r - 1) / (ℓ + s) ^ m)
      ≤ ∫ s in (0:ℝ)..ε, s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hε (hintκ.const_mul C₀) hintκρ (fun s hs => ?_)
    have hκ0 : (0 : ℝ) ≤ s ^ (r - 1) / (ℓ + s) ^ m := by
      have := hs.1; exact div_nonneg (pow_nonneg (by linarith) _) (pow_pos (by linarith) _).le
    have := mul_le_mul_of_nonneg_left (hρpt s hs) hκ0
    nlinarith [this]
  -- chain with `∫ κ ≥ ε^r/(r(ℓ+ε)^m)`
  have hκint := power_integral_lower (m := m) hℓ hr ε hε
  calc C₀ * (ε ^ r / ((r : ℝ) * (ℓ + ε) ^ m))
      ≤ C₀ * (∫ s in (0:ℝ)..ε, s ^ (r - 1) / (ℓ + s) ^ m) :=
        mul_le_mul_of_nonneg_left hκint hconst
    _ ≤ _ := hstep

/-- Exact value of `∫_a^b (1 − c(q+s)) ds` (FTC, antiderivative `s − (c/2)(q+s)(q+s)`). -/
lemma affine_integral (c q a b : ℝ) :
    (∫ s in a..b, (1 - c * (q + s))) = (b - a) - c * ((q + b) ^ 2 - (q + a) ^ 2) / 2 := by
  have hd : ∀ s ∈ Set.uIcc a b,
      HasDerivAt (fun s => s - c / 2 * ((q + s) * (q + s))) (1 - c * (q + s)) s := by
    intro s _
    have hu : HasDerivAt (fun s : ℝ => q + s) 1 s := (hasDerivAt_id s).const_add q
    have hg := (hu.mul hu).const_mul (c / 2)
    have hd0 := (hasDerivAt_id s).sub hg
    rw [show (1 : ℝ) - c / 2 * (1 * (q + s) + (q + s) * 1) = 1 - c * (q + s) from by ring] at hd0
    exact hd0
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) a b)]
  ring

/-- **`eq:tail-D` (deficit upper bound).**  On the negative window `(a,b)`, bounding
`−ρ(q+s) ≤ (q+s)^{n-1}(1−(m/n)(q+s))` (`rho_neg`), pulling out `s^{r-1} ≤ b^{r-1}` and the decreasing
factor `(q+s)^{n-1}/(ℓ+s)^m ≤ (q+a)^{n-1}/(ℓ+a)^m` (`deficit_factor_antitone`), and integrating the
remaining affine factor exactly (`affine_integral`), gives `∫_a^b κρ ≥ −D`. -/
lemma left_deficit_bound {ℓ : ℝ} (hℓ : 0 < ℓ) {m r t : ℕ} (hr : 1 ≤ r) (ht : t ≠ 0) (hm : m ≠ 0)
    (q a b : ℝ) (ha0 : 0 ≤ a) (hab : a ≤ b) (hq : 0 ≤ q)
    (hsign : ∀ s ∈ Set.Icc a b, 2 * (t : ℝ) * (ℓ + s) ≤ (m : ℝ) * (q + s))
    (hu1 : ∀ s ∈ Set.Icc a b, q + s ≤ 1)
    (hfac : ∀ s ∈ Set.Icc a b, 0 ≤ 1 - (m : ℝ) / (2 * (t : ℝ) + 1) * (q + s)) :
    -(b ^ (r - 1) * ((q + a) ^ (2 * t) / (ℓ + a) ^ m)
        * ((b - a) - (m : ℝ) / (2 * (t : ℝ) + 1) * ((q + b) ^ 2 - (q + a) ^ 2) / 2))
      ≤ ∫ s in a..b, s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s) := by
  set κ0 := b ^ (r - 1) * ((q + a) ^ (2 * t) / (ℓ + a) ^ m) with hκ0def
  have hAnti := deficit_factor_antitone hℓ ht hm q a b ha0 hq hsign
  have hpt : ∀ s ∈ Set.Icc a b,
      -(s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s))
        ≤ κ0 * (1 - (m : ℝ) / (2 * (t : ℝ) + 1) * (q + s)) := by
    intro s hs
    obtain ⟨has, hsb⟩ := hs
    have hs0 : 0 ≤ s := le_trans ha0 has
    have hℓs : 0 < ℓ + s := by linarith
    have hℓa : 0 < ℓ + a := by linarith
    have hrn := rho_neg t m (q + s) (hu1 s ⟨has, hsb⟩)
    have hκpos : (0 : ℝ) ≤ s ^ (r - 1) / (ℓ + s) ^ m :=
      div_nonneg (pow_nonneg hs0 _) (pow_pos hℓs _).le
    have hA : -(s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s))
        ≤ s ^ (r - 1) / (ℓ + s) ^ m
          * ((q + s) ^ (2 * t) * (1 - (m : ℝ) / (2 * (t : ℝ) + 1) * (q + s))) := by
      rw [show -(s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s))
          = s ^ (r - 1) / (ℓ + s) ^ m * (-rho (2 * t + 1) m (q + s)) from by ring]
      exact mul_le_mul_of_nonneg_left hrn hκpos
    have hsr : s ^ (r - 1) ≤ b ^ (r - 1) := pow_le_pow_left₀ hs0 hsb _
    have hAf := hAnti ⟨le_refl a, hab⟩ ⟨has, hsb⟩ has
    have hmono : s ^ (r - 1) * ((q + s) ^ (2 * t) / (ℓ + s) ^ m)
        ≤ b ^ (r - 1) * ((q + a) ^ (2 * t) / (ℓ + a) ^ m) := by
      calc s ^ (r - 1) * ((q + s) ^ (2 * t) / (ℓ + s) ^ m)
          ≤ b ^ (r - 1) * ((q + s) ^ (2 * t) / (ℓ + s) ^ m) :=
            mul_le_mul_of_nonneg_right hsr
              (div_nonneg (pow_nonneg (by linarith) _) (pow_pos hℓs _).le)
        _ ≤ b ^ (r - 1) * ((q + a) ^ (2 * t) / (ℓ + a) ^ m) :=
            mul_le_mul_of_nonneg_left hAf (pow_nonneg (by linarith) _)
    calc -(s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s))
        ≤ s ^ (r - 1) / (ℓ + s) ^ m
            * ((q + s) ^ (2 * t) * (1 - (m : ℝ) / (2 * (t : ℝ) + 1) * (q + s))) := hA
      _ = (s ^ (r - 1) * ((q + s) ^ (2 * t) / (ℓ + s) ^ m))
            * (1 - (m : ℝ) / (2 * (t : ℝ) + 1) * (q + s)) := by ring
      _ ≤ κ0 * (1 - (m : ℝ) / (2 * (t : ℝ) + 1) * (q + s)) :=
            mul_le_mul_of_nonneg_right hmono (hfac s ⟨has, hsb⟩)
  have hintκρ := kernelr_intervalIntegrable hℓ m r t q a b ha0 (le_trans ha0 hab)
  have hintbound : IntervalIntegrable
      (fun s => κ0 * (1 - (m : ℝ) / (2 * (t : ℝ) + 1) * (q + s))) volume a b :=
    Continuous.intervalIntegrable (by fun_prop) a b
  have hintneg : IntervalIntegrable
      (fun s => -(s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s))) volume a b := hintκρ.neg
  have hmono_int := intervalIntegral.integral_mono_on hab hintneg hintbound hpt
  rw [intervalIntegral.integral_neg] at hmono_int
  rw [intervalIntegral.integral_const_mul] at hmono_int
  rw [affine_integral] at hmono_int
  linarith [hmono_int]

/-- **Surplus constant nonnegativity** (`hconst`, `c_n ≥ 0`).  Uniform — NOT a sweep: from `cn_bound`
(`(q+ε)^{2t} ≤ ½(1−(q+ε))^{2t+1}`, `t≥2`, `q≤1/3`, `ε=(1−2q)/4`) and `m/n ≥ 1`, the surplus constant
`(m/n)(1−(q+ε))^{n} − (q+ε)^{2t} ≥ ½(1−(q+ε))^{n} ≥ 0`. -/
lemma strip_surplus_const_nonneg {m t : ℕ} (ht : 2 ≤ t) (hmn : 2 * t + 1 ≤ m) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 3) :
    0 ≤ (m : ℝ) / (2 * (t : ℝ) + 1) * (1 - (q + (1 / 2 - q) / 2)) ^ (2 * t + 1)
        - (q + (1 / 2 - q) / 2) ^ (2 * t) := by
  have heps : (1 / 2 - q) / 2 = (1 - 2 * q) / 4 := by ring
  rw [heps]
  have hcn := cn_bound ht hq0 hq
  have hmn1 : (1 : ℝ) ≤ (m : ℝ) / (2 * (t : ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity)]
    have : (2 * (t : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast hmn
    linarith
  have hp : (0 : ℝ) ≤ 1 - (q + (1 - 2 * q) / 4) := by nlinarith [hq]
  have hpow : (0 : ℝ) ≤ (1 - (q + (1 - 2 * q) / 4)) ^ (2 * t + 1) := pow_nonneg hp _
  nlinarith [hcn, mul_le_mul_of_nonneg_right (sub_nonneg.mpr hmn1) hpow, hpow]

set_option maxHeartbeats 1000000 in
/-- **`lem:left-estimate` reduced to the scalar comparison `D ≤ Σ`.**  In the residual strip
(`q ≤ 1/3`, `r ≥ 2`, `n = m−2r > 2r`, `0 < ℓ < q+r/m`, `n = 2t+1`), with `a = 1/2−q`, `b = ν−q`,
`ε = a/2` (`ν = n/m`), the diagonal kernel is nonnegative **provided** the explicit deficit `D` is
dominated by the explicit surplus `Σ`.  Everything but the scalar `D ≤ Σ` is verified here (region
split, `ρ ≥ 0` on `(ε,a]` and `(b,∞)`, `tail-S`, `tail-D`, and the surplus constant `hconst` via
`strip_surplus_const_nonneg`).  The remaining obligation `D ≤ Σ` is exactly `app:constants` — a finite
rational sweep `63 ≤ m ≤ 499` plus an `rpow`-tail bound for `m ≥ 500` (deferred). -/
theorem diagKernel_nonneg_strip_left {m r n t : ℕ} (hr2 : 2 ≤ r) (hmn : m = n + 2 * r)
    (hn2r : 2 * r < n) (hnt : n = 2 * t + 1) {q ℓ : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 3) (hℓ0 : 0 < ℓ) (hℓr : ℓ < q + (r : ℝ) / (m : ℝ))
    (hSD : ((2 * (t : ℝ) + 1) / (m : ℝ) - q) ^ (r - 1)
            * ((q + (1 / 2 - q)) ^ (2 * t) / (ℓ + (1 / 2 - q)) ^ m)
            * ((((2 * (t : ℝ) + 1) / (m : ℝ) - q) - (1 / 2 - q))
              - (m : ℝ) / (2 * (t : ℝ) + 1)
                * ((q + ((2 * (t : ℝ) + 1) / (m : ℝ) - q)) ^ 2 - (q + (1 / 2 - q)) ^ 2) / 2)
          ≤ ((m : ℝ) / (2 * (t : ℝ) + 1) * (1 - (q + (1 / 2 - q) / 2)) ^ (2 * t + 1)
                - (q + (1 / 2 - q) / 2) ^ (2 * t))
            * (((1 / 2 - q) / 2) ^ r / ((r : ℝ) * (ℓ + (1 / 2 - q) / 2) ^ m))) :
    0 ≤ diagKernel m r q ℓ := by
  have hr1 : 1 ≤ r := by omega
  refine diagKernel_nonneg_of_integral (by omega) (by omega) q ℓ hℓ0 ?_
  rw [show m - 2 * r = 2 * t + 1 from by omega]
  -- casts
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hmR : (2 * (t : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast (show 2 * t + 1 ≤ m by omega)
  have hm2n : (m : ℝ) < 2 * (2 * (t : ℝ) + 1) := by
    exact_mod_cast (show m < 2 * (2 * t + 1) by omega)
  have ht2 : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (show 2 ≤ t by omega)
  have hmreal : (m : ℝ) = 2 * (t : ℝ) + 1 + 2 * (r : ℝ) := by
    rw [show m = 2 * t + 1 + 2 * r from by omega]; push_cast; ring
  have h4tr : 4 * (t : ℝ) * (r : ℝ) ≤ (m : ℝ) * (2 * (r : ℝ) + 1) := by
    rw [hmreal]; nlinarith [ht2, (show (2 : ℝ) ≤ (r : ℝ) by exact_mod_cast hr2)]
  -- ν = (2t+1)/m ∈ (1/2, 1]
  have hν12 : (1 : ℝ) / 2 < (2 * (t : ℝ) + 1) / (m : ℝ) := by
    rw [lt_div_iff₀ hmpos]; nlinarith [hm2n]
  have hν1 : (2 * (t : ℝ) + 1) / (m : ℝ) ≤ 1 := by rw [div_le_one hmpos]; exact hmR
  -- endpoints
  have hapos : (0 : ℝ) < 1 / 2 - q := by linarith
  have hε0 : (0 : ℝ) ≤ (1 / 2 - q) / 2 := by linarith
  have hεa : (1 / 2 - q) / 2 < 1 / 2 - q := by linarith
  have hbpos : (0 : ℝ) < (2 * (t : ℝ) + 1) / (m : ℝ) - q := by linarith [hν12]
  have hab : (1 / 2 - q : ℝ) ≤ (2 * (t : ℝ) + 1) / (m : ℝ) - q := by linarith [hν12]
  have hεb : (1 / 2 - q) / 2 ≤ (2 * (t : ℝ) + 1) / (m : ℝ) - q := by linarith [hab, hεa]
  have hp : q + (1 / 2 - q) / 2 ≤ 1 := by linarith
  -- `m·ℓ < m·q + r`
  have hℓm : (m : ℝ) * ℓ < (m : ℝ) * q + (r : ℝ) := by
    have h := mul_lt_mul_of_pos_left hℓr hmpos
    have he : (m : ℝ) * (q + (r : ℝ) / (m : ℝ)) = (m : ℝ) * q + (r : ℝ) := by field_simp
    linarith [h, he]
  -- deficit monotonicity/sign hypotheses on `[a,b]`
  have hsign : ∀ s ∈ Set.Icc (1 / 2 - q : ℝ) ((2 * (t : ℝ) + 1) / (m : ℝ) - q),
      2 * (t : ℝ) * (ℓ + s) ≤ (m : ℝ) * (q + s) := by
    intro s hs
    have has := hs.1
    have h2tpos : (0 : ℝ) < 2 * (t : ℝ) := by linarith
    have h3 := mul_lt_mul_of_pos_left hℓm h2tpos
    have hidentqs : (m : ℝ) * (2 * (r : ℝ) + 1) * (q + s)
        = (m : ℝ) * (m : ℝ) * (q + s) - 2 * (t : ℝ) * (m : ℝ) * (q + s) := by
      rw [hmreal]; ring
    have hmul' : (m : ℝ) * (2 * (t : ℝ) * (ℓ + s)) ≤ (m : ℝ) * ((m : ℝ) * (q + s)) := by
      nlinarith [h3, h4tr, hidentqs, hmpos,
        mul_nonneg (mul_nonneg hmpos.le (by linarith : (0:ℝ) ≤ 2 * (r:ℝ) + 1))
          (by linarith : (0:ℝ) ≤ q + s - 1/2)]
    exact le_of_mul_le_mul_left hmul' hmpos
  have hu1 : ∀ s ∈ Set.Icc (1 / 2 - q : ℝ) ((2 * (t : ℝ) + 1) / (m : ℝ) - q), q + s ≤ 1 := by
    intro s hs; have := hs.2; linarith [hν1]
  have hfac : ∀ s ∈ Set.Icc (1 / 2 - q : ℝ) ((2 * (t : ℝ) + 1) / (m : ℝ) - q),
      0 ≤ 1 - (m : ℝ) / (2 * (t : ℝ) + 1) * (q + s) := by
    intro s hs
    have hsb := hs.2
    have hn1pos : (0 : ℝ) < 2 * (t : ℝ) + 1 := by positivity
    rw [sub_nonneg, div_mul_eq_mul_div, div_le_one hn1pos]
    have hqb : q + s ≤ (2 * (t : ℝ) + 1) / (m : ℝ) := by linarith
    rw [le_div_iff₀ hmpos] at hqb; nlinarith [hqb]
  -- the four region facts
  have hconst := strip_surplus_const_nonneg (m := m) (t := t) (by omega) (by omega) hq0 hq
  have hsurp := left_surplus_bound (m := m) (r := r) (t := t) hℓ0 hr1 q ((1 / 2 - q) / 2)
    hq0 hε0 hp hconst
  have hdef := left_deficit_bound (m := m) (r := r) (t := t) hℓ0 hr1 (by omega) (by omega)
    q (1 / 2 - q) ((2 * (t : ℝ) + 1) / (m : ℝ) - q) hapos.le hab hq0 hsign hu1 hfac
  -- integrability on Ioi 0
  have hint0 : IntegrableOn
      (fun s => s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s)) (Set.Ioi 0) := by
    have h := kernelIntegrand_integrableOn (m := m) (r := r) (by omega) (by omega) q ℓ hℓ0
    unfold kernelIntegrand at h
    rw [show m - 2 * r = 2 * t + 1 from by omega] at h
    exact h
  -- region (ε,a): ρ ≥ 0
  have hregion : 0 ≤ ∫ s in ((1 / 2 - q) / 2)..(1 / 2 - q),
      s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s) := by
    refine region_nonneg _ q ((1 / 2 - q) / 2) (1 / 2 - q) hεa.le (fun s hs => ?_) (fun s hs => ?_)
    · have := hs.1; exact div_nonneg (pow_nonneg (by linarith) _) (pow_pos (by linarith) _).le
    · refine rho_window_left t m hmR (q + s) ?_; have := hs.2; linarith
  -- tail (b,∞): ρ ≥ 0
  have htail : 0 ≤ ∫ s in Set.Ioi ((2 * (t : ℝ) + 1) / (m : ℝ) - q),
      s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s) := by
    refine tail_nonneg _ q ((2 * (t : ℝ) + 1) / (m : ℝ) - q) (fun s hs => ?_) (fun s hs => ?_)
    · simp only [Set.mem_Ioi] at hs
      have hs0 : (0 : ℝ) < s := lt_trans hbpos hs
      exact div_nonneg (pow_nonneg hs0.le _) (pow_pos (by linarith) _).le
    · simp only [Set.mem_Ioi] at hs
      refine rho_window_right t m hmR (q + s) ?_
      have hqs : (2 * (t : ℝ) + 1) / (m : ℝ) < q + s := by linarith
      have h := (div_lt_iff₀ hmpos).mp hqs
      nlinarith [h]
  -- assemble the integral
  have hintI := kernelr_intervalIntegrable hℓ0 m r t q
  have hsplit : (∫ s in Set.Ioi (0:ℝ), s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s))
      = (∫ s in (0:ℝ)..((2 * (t : ℝ) + 1) / (m : ℝ) - q),
            s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s))
        + ∫ s in Set.Ioi ((2 * (t : ℝ) + 1) / (m : ℝ) - q),
            s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hbpos.le,
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hint0.mono_set (fun x hx => hx.1)) (hint0.mono_set (Set.Ioi_subset_Ioi hbpos.le)),
      intervalIntegral.integral_of_le hbpos.le]
  have hcomb : (∫ s in (0:ℝ)..((2 * (t : ℝ) + 1) / (m : ℝ) - q),
        s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s))
      = (∫ s in (0:ℝ)..((1 / 2 - q) / 2), s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s))
        + ((∫ s in ((1 / 2 - q) / 2)..(1 / 2 - q),
              s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s))
          + ∫ s in (1 / 2 - q)..((2 * (t : ℝ) + 1) / (m : ℝ) - q),
              s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (hintI 0 ((1 / 2 - q) / 2) le_rfl hε0)
          (hintI ((1 / 2 - q) / 2) ((2 * (t : ℝ) + 1) / (m : ℝ) - q) hε0 hbpos.le),
        ← intervalIntegral.integral_add_adjacent_intervals
          (hintI ((1 / 2 - q) / 2) (1 / 2 - q) hε0 hapos.le)
          (hintI (1 / 2 - q) ((2 * (t : ℝ) + 1) / (m : ℝ) - q) hapos.le hbpos.le)]
  rw [hsplit, hcomb]
  linarith [hsurp, hregion, hdef, htail, hSD]

end OddCycleBound.HighDensity
