/-
# High-density theorem — the residual strip, right-reflection assembly (M6, `lem:right-reflection`)

The residual range (`eq:remaining-range`) is `q ≤ 1/3`, `r ≥ 2`, `n = m−2r > 2r`, `0 < ℓ < q+r/m`,
with `m ≥ 63` odd (so `n` is odd, `n = 2t+1`).  `lem:right-reflection` handles the sub-case
`θ = r/m ≥ 1/6` (`m ≤ 6r`) and `ℓ > 2/5`.

Notation (`eq:tail-notation`): `a = 1/2 − q`, `ν = n/m`, `b = ν − q`, `L = b − a = 1/2 − 2θ`.  The
only interval where `ρ_{n,m}(q+s)` is negative is `(a,b)`.  We split `∫₀^∞ κ(s)ρ(q+s)` (with
`κ(s) = s^{r-1}/(ℓ+s)^m`) into
`[0,a] ∪ [a,b] ∪ [b,2b−a] ∪ (2b−a,∞)`:
* `[0,a]`   : `ρ ≥ 0` (`rho_window_left`, `q+s ≤ 1/2`),
* `(2b−a,∞)`: `ρ ≥ 0` (`rho_window_right`, `q+s ≥ 2ν−1/2 > ν`, using `ν > 1/2` from `n > 2r`),
* `[a,b]∪[b,2b−a]`: reflect around `b`; writing `q+s = ν−e`, `q+(2b−s) = ν+e`, the paired
  integrand is `≥ 0` pointwise via `rho_neg` + `rho_pos_tail` + **`right_condition`** (whose
  coefficient hypothesis is `threshold_bound` + `ℓ > 2/5`).
-/

import OddCycleBound.HighDensity.M6Strip
import OddCycleBound.HighDensity.KernelImproper
import OddCycleBound.HighDensity.KernelReflect
import OddCycleBound.HighDensity.KernelIntegrable

open MeasureTheory Set
open scoped BigOperators

namespace OddCycleBound.HighDensity

/-- **General-`r` reduction (`prop:kernel`).**  For `ℓ > 0`, `r ≥ 1`, `n = m−2r ≥ 1`, since
`C_{m,r}·ℓ^{n+r} > 0`, the diagonal kernel is nonnegative as soon as the improper integral is. -/
theorem diagKernel_nonneg_of_integral {m r : ℕ} (hr : r ≠ 0) (hn : 1 ≤ m - 2 * r) (q ℓ : ℝ)
    (hl : 0 < ℓ)
    (hI : 0 ≤ ∫ s in Set.Ioi (0:ℝ), s ^ (r - 1) / (ℓ + s) ^ m * rho (m - 2 * r) m (q + s)) :
    0 ≤ diagKernel m r q ℓ := by
  rw [kernel_form hr hn q ℓ hl]
  exact mul_nonneg (mul_nonneg (Cmr_pos hr hn).le (by positivity)) hI

/-- Interval-integrability of the general-`r` kernel integrand `s ↦ s^{r-1}(ℓ+s)^{-m}·ρ(q+s)` on
`[a,b]` with nonnegative endpoints (so `ℓ+s > 0` and `s ≥ 0` throughout). -/
lemma kernelr_intervalIntegrable {ℓ : ℝ} (hℓ : 0 < ℓ) (m r t : ℕ) (q a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable
      (fun s => s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.mul
  · refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun s hs => ?_)
    have hs0 : 0 ≤ s := by
      rcases le_total a b with h | h
      · rw [Set.uIcc_of_le h] at hs; linarith [hs.1]
      · rw [Set.uIcc_of_ge h] at hs; linarith [hs.1]
    positivity
  · exact (by unfold rho; fun_prop : Continuous fun s => rho (2 * t + 1) m (q + s)).continuousOn

/-- Interval-integrability of the *reflected* general-`r` kernel integrand
`x ↦ (2c−x)^{r-1}(ℓ+(2c−x))^{-m}·ρ(q+(2c−x))` on `[a,b]`, when `2c−x ≥ 0` throughout. -/
lemma kernelr_refl_intervalIntegrable {ℓ : ℝ} (hℓ : 0 < ℓ) (m r t : ℕ) (q c a b : ℝ)
    (hpos : ∀ x ∈ Set.uIcc a b, 0 ≤ 2 * c - x) :
    IntervalIntegrable
      (fun x => (2 * c - x) ^ (r - 1) / (ℓ + (2 * c - x)) ^ m
        * rho (2 * t + 1) m (q + (2 * c - x))) volume a b := by
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop) (fun x hx => ?_)) ?_
  · have := hpos x hx; positivity
  · exact (by unfold rho; fun_prop :
      Continuous fun x => rho (2 * t + 1) m (q + (2 * c - x))).continuousOn

/-- **Reflection pairing over `[a,b]` around the right endpoint `b`.**  Pairs the negative window
`[a,b]` with its reflection `[b,2b−a]` (`x ↦ 2b−x`).  If the reflected pair is nonnegative pointwise
and both integrands are interval-integrable, the two integrals of the kernel integrand sum to `≥ 0`. -/
lemma right_reflect_pair_nonneg {m t r : ℕ} {ℓ q a b : ℝ} (hab : a ≤ b)
    (hpt : ∀ x ∈ Set.Icc a b,
      0 ≤ x ^ (r - 1) / (ℓ + x) ^ m * rho (2 * t + 1) m (q + x)
        + (2 * b - x) ^ (r - 1) / (ℓ + (2 * b - x)) ^ m * rho (2 * t + 1) m (q + (2 * b - x)))
    (hfi : IntervalIntegrable
      (fun x => (2 * b - x) ^ (r - 1) / (ℓ + (2 * b - x)) ^ m
        * rho (2 * t + 1) m (q + (2 * b - x))) volume a b)
    (hgi : IntervalIntegrable
      (fun s => s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s)) volume a b) :
    0 ≤ (∫ s in a..b, s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s))
        + ∫ s in b..(2 * b - a), s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s) := by
  have hrefl : (∫ x in a..b,
      (2 * b - x) ^ (r - 1) / (ℓ + (2 * b - x)) ^ m * rho (2 * t + 1) m (q + (2 * b - x)))
      = ∫ s in b..(2 * b - a), s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s) := by
    rw [intervalIntegral.integral_comp_sub_left
      (fun s => s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s)) (2 * b)]
    congr 1 <;> ring
  rw [← hrefl, ← intervalIntegral.integral_add hgi hfi]
  exact intervalIntegral.integral_nonneg hab (fun x hx => hpt x hx)

/-- **Pointwise reflected pair (the heart of `lem:right-reflection`).**  Writing a point of the
negative window as `ν−e` (with reflected partner `ν+e`), and with the kernel weights
`κ(b∓e) = (b∓e)^{r-1}/(ℓ+(b∓e))^m`, the `κ`-weighted pair of `ρ`-values is nonnegative:
`κ(b−e)·ρ(ν−e) + κ(b+e)·ρ(ν+e) ≥ 0`.  From `rho_neg` (`−ρ(ν−e) ≤ (e/ν)(ν−e)^{n-1}`), `rho_pos_tail`
(`ρ(ν+e) ≥ (e/ν)(ν+e)^{n-1}`), and the reflection condition `hRC` (= `eq:right-condition`), which makes
`κ(b+e)(ν+e)^{n-1} ≥ κ(b−e)(ν−e)^{n-1}`. -/
lemma right_pair_pointwise {m t r : ℕ} {ℓ ν b e : ℝ} (hℓ : 0 < ℓ)
    (hm : (2 * (t : ℝ) + 1) ≤ (m : ℝ)) (hνdef : ν = (2 * (t : ℝ) + 1) / (m : ℝ))
    (hν : 0 < ν) (he0 : 0 ≤ e) (hbe : 0 < b - e) (hνe0 : 0 < ν - e) (hνe1 : ν + e ≤ 1)
    (hRC : ((ℓ + (b + e)) / (ℓ + (b - e))) ^ m
        ≤ ((b + e) / (b - e)) ^ (r - 1) * ((ν + e) / (ν - e)) ^ (2 * t)) :
    0 ≤ (b - e) ^ (r - 1) / (ℓ + (b - e)) ^ m * rho (2 * t + 1) m (ν - e)
      + (b + e) ^ (r - 1) / (ℓ + (b + e)) ^ m * rho (2 * t + 1) m (ν + e) := by
  have hn1 : (0 : ℝ) < 2 * (t : ℝ) + 1 := by positivity
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le hn1 hm
  have hbe' : 0 < b + e := by linarith
  have hd1 : 0 < ℓ + (b - e) := by linarith
  have hd2 : 0 < ℓ + (b + e) := by linarith
  have hνe0' : 0 < ν + e := by linarith
  set κ1 := (b - e) ^ (r - 1) / (ℓ + (b - e)) ^ m with hκ1def
  set κ2 := (b + e) ^ (r - 1) / (ℓ + (b + e)) ^ m with hκ2def
  have hκ1 : 0 ≤ κ1 := by rw [hκ1def]; positivity
  have hκ2 : 0 ≤ κ2 := by rw [hκ2def]; positivity
  have hev : 0 ≤ e / ν := div_nonneg he0 hν.le
  -- `1 − (m/n)(ν−e) = e/ν`  and  `(ν+e−n/m)/(n/m) = e/ν`
  have heq1 : (1 : ℝ) - (m : ℝ) / (2 * (t : ℝ) + 1) * (ν - e) = e / ν := by
    rw [hνdef]; field_simp; ring
  have heq2 : ((ν + e) - (2 * (t : ℝ) + 1) / (m : ℝ)) / ((2 * (t : ℝ) + 1) / (m : ℝ))
      * (ν + e) ^ (2 * t) = e / ν * (ν + e) ^ (2 * t) := by
    rw [← hνdef]; ring
  -- `ρ`-bounds
  have hu1 : ν - e ≤ 1 := by
    have hν1 : ν ≤ 1 := by rw [hνdef, div_le_one hmpos]; exact hm
    linarith
  have hrn0 := rho_neg t m (ν - e) hu1
  rw [heq1] at hrn0
  have hrn : -((ν - e) ^ (2 * t) * (e / ν)) ≤ rho (2 * t + 1) m (ν - e) := by linarith [hrn0]
  have hrp0 := rho_pos_tail t m hm (ν + e) hνe1
  rw [heq2] at hrp0
  -- the `κ`-comparison from `hRC`
  have hkappa : κ1 * (ν - e) ^ (2 * t) ≤ κ2 * (ν + e) ^ (2 * t) := by
    rw [hκ1def, hκ2def, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hRC' := hRC
    rw [div_pow, div_pow, div_pow, div_mul_div_comm,
      div_le_div_iff₀ (by positivity) (by positivity)] at hRC'
    nlinarith [hRC']
  -- assemble
  have hA := mul_le_mul_of_nonneg_left hrn hκ1
  have hB := mul_le_mul_of_nonneg_left hrp0 hκ2
  have hC : 0 ≤ κ2 * (e / ν * (ν + e) ^ (2 * t)) + κ1 * -((ν - e) ^ (2 * t) * (e / ν)) := by
    have h : κ2 * (e / ν * (ν + e) ^ (2 * t)) + κ1 * -((ν - e) ^ (2 * t) * (e / ν))
        = e / ν * (κ2 * (ν + e) ^ (2 * t) - κ1 * (ν - e) ^ (2 * t)) := by ring
    rw [h]; exact mul_nonneg hev (by linarith [hkappa])
  linarith [hA, hB, hC]

set_option maxHeartbeats 400000 in
/-- **`lem:right-reflection`.**  In the residual strip (`q ≤ 1/3`, `r ≥ 2`, `n = m−2r > 2r`,
`0 < ℓ < q + r/m`, `n = 2t+1` odd) with `m ≥ 63`, `θ = r/m ≥ 1/6` (`m ≤ 6r`) and `ℓ > 2/5`, the
diagonal kernel is nonnegative.  Split `∫₀^∞ κρ` into `[0,a] ∪ [a,b] ∪ [b,2b−a] ∪ (2b−a,∞)`:
`[0,a]` and `(2b−a,∞)` have `ρ ≥ 0`; the middle `[a,b]∪[b,2b−a]` is a reflected pair, nonnegative
pointwise via `right_pair_pointwise` (whose reflection condition is `right_condition` fed by
`threshold_bound` + `ℓ > 2/5`). -/
theorem diagKernel_nonneg_strip_right {m r n t : ℕ}
    (hm63 : 63 ≤ m) (hmodd : m % 2 = 1) (h6r : m ≤ 6 * r)
    (hmn : m = n + 2 * r) (hn2r : 2 * r < n) (hnt : n = 2 * t + 1)
    {q ℓ : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 3) (hℓ25 : 2 / 5 < ℓ) :
    0 ≤ diagKernel m r q ℓ := by
  have hℓ0 : 0 < ℓ := by linarith
  have hr1 : 1 ≤ r := by omega
  have hn1 : 1 ≤ n := by omega
  refine diagKernel_nonneg_of_integral (by omega) (by omega) q ℓ hℓ0 ?_
  rw [show m - 2 * r = 2 * t + 1 from by omega]
  -- casts of the integer constraints
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmR : (2 * (t : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast (show 2 * t + 1 ≤ m by omega)
  have hm2n : (m : ℝ) < 2 * (2 * (t : ℝ) + 1) := by
    exact_mod_cast (show m < 2 * (2 * t + 1) by omega)
  have hn4r : (2 * (t : ℝ) + 1) ≤ 4 * (r : ℝ) := by
    exact_mod_cast (show 2 * t + 1 ≤ 4 * r by omega)
  have hnR : (n : ℝ) = 2 * (t : ℝ) + 1 := by rw [hnt]; push_cast; ring
  have hmreal : (m : ℝ) = 2 * (t : ℝ) + 1 + 2 * (r : ℝ) := by
    rw [show m = 2 * t + 1 + 2 * r from by omega]; push_cast; ring
  -- ν = n/m
  set ν : ℝ := (n : ℝ) / (m : ℝ) with hνeq
  have hνdef : ν = (2 * (t : ℝ) + 1) / (m : ℝ) := by rw [hνeq, hnR]
  have hνpos : 0 < ν := by rw [hνeq]; exact div_pos hnpos hmpos
  have hν23 : ν ≤ 2 / 3 := by rw [hνdef, div_le_iff₀ hmpos]; nlinarith [hn4r, hmreal]
  have hν12 : 1 / 2 < ν := by rw [hνdef, lt_div_iff₀ hmpos]; nlinarith [hm2n]
  -- a, b
  set a : ℝ := 1 / 2 - q with hadef
  set b : ℝ := ν - q with hbdef
  have hqb : q + b = ν := by rw [hbdef]; ring
  have hapos : 0 < a := by rw [hadef]; linarith
  have hbpos : 0 < b := by rw [hbdef]; linarith
  have hab : a < b := by rw [hadef, hbdef]; linarith
  have h2ba : 0 < 2 * b - a := by linarith
  have hbba : b < 2 * b - a := by linarith
  -- integrability on Ioi 0
  have hint0 : IntegrableOn
      (fun s => s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s)) (Set.Ioi 0) := by
    have h := kernelIntegrand_integrableOn (m := m) (r := r) (by omega) (by omega) q ℓ hℓ0
    unfold kernelIntegrand at h
    rw [show m - 2 * r = 2 * t + 1 from by omega] at h
    exact h
  -- split Ioi 0 = Ioc 0 (2b-a) ∪ Ioi (2b-a)
  have hsplit : (∫ s in Set.Ioi (0:ℝ), s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s))
      = (∫ s in (0:ℝ)..(2 * b - a), s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s))
        + ∫ s in Set.Ioi (2 * b - a), s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi h2ba.le,
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hint0.mono_set (fun x hx => hx.1)) (hint0.mono_set (Set.Ioi_subset_Ioi h2ba.le)),
      intervalIntegral.integral_of_le h2ba.le]
  rw [hsplit]
  -- tail (2b-a, ∞) ≥ 0
  have htail : 0 ≤ ∫ s in Set.Ioi (2 * b - a),
      s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s) := by
    refine tail_nonneg _ q (2 * b - a) (fun s hs => ?_) (fun s hs => ?_)
    · simp only [Set.mem_Ioi] at hs
      have hs0 : (0 : ℝ) < s := lt_trans h2ba hs
      exact div_nonneg (pow_nonneg hs0.le _) (pow_pos (by linarith) _).le
    · simp only [Set.mem_Ioi] at hs
      refine rho_window_right t m hmR (q + s) ?_
      have hmν : (m : ℝ) * ν = 2 * (t : ℝ) + 1 := by rw [hνdef]; field_simp
      have hba2 : 2 * b - a = 2 * ν - q - 1 / 2 := by rw [hadef, hbdef]; ring
      have hqs : 2 * ν - 1 / 2 < q + s := by linarith [hs, hba2]
      have hmul := mul_lt_mul_of_pos_left hqs hmpos
      nlinarith [hmul, hmν, hm2n]
  -- region [0,a]: ρ ≥ 0
  have h0a : 0 ≤ ∫ s in (0:ℝ)..a,
      s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s) := by
    refine region_nonneg _ q 0 a hapos.le (fun s hs => ?_) (fun s hs => ?_)
    · have hs0 := hs.1
      exact div_nonneg (pow_nonneg hs0 _) (pow_pos (by linarith) _).le
    · refine rho_window_left t m hmR (q + s) ?_
      have := hs.2; rw [hadef] at this; linarith
  -- coefficient hypothesis for right_condition via threshold_bound + ℓ > 2/5
  have hDpos : 0 < ((r : ℝ) - 1) / b + ((n : ℝ) - 1) / ν := by
    have hr1' : (0 : ℝ) < (r : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 2 ≤ r by omega)
      linarith
    have hn1' : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 2 ≤ n by omega)
      linarith
    exact add_pos (div_pos hr1' hbpos) (div_pos hn1' hνpos)
  have hcoef : (m : ℝ) / (ℓ + b) ≤ ((r : ℝ) - 1) / b + ((n : ℝ) - 1) / ν := by
    have hthr := threshold_bound hm63 hmodd h6r hmn hn2r hbpos
    rw [← hνeq] at hthr
    have hmD : (m : ℝ) / (((r : ℝ) - 1) / b + ((n : ℝ) - 1) / ν) ≤ b + 2 / 5 := by linarith [hthr]
    rw [div_le_iff₀ hDpos] at hmD
    have hCpos : 0 < ℓ + b := by linarith
    rw [div_le_iff₀ hCpos]
    have hlt := mul_lt_mul_of_pos_right (show b + 2 / 5 < ℓ + b by linarith) hDpos
    nlinarith [hmD, hlt]
  -- middle reflected pair [a,b] ∪ [b,2b-a] ≥ 0
  have hpair : 0 ≤ (∫ s in a..b, s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s))
      + ∫ s in b..(2 * b - a), s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s) := by
    refine right_reflect_pair_nonneg hab.le (fun x hx => ?_) ?_ ?_
    · obtain ⟨hxa, hxb⟩ := hx
      have hxpos : 0 < x := lt_of_lt_of_le hapos hxa
      set y := b - x with hy
      have hy0 : 0 ≤ y := by rw [hy]; linarith
      have hyb : y < b := by rw [hy]; linarith
      have hby : 0 < b - y := by rw [hy]; linarith
      have hνy0 : 0 < ν - y := by rw [hy]; linarith [hqb, hxpos, hq0]
      have hνy1 : ν + y ≤ 1 := by rw [hy]; linarith [hν23, hxa, hadef, hbdef]
      have hRCraw := right_condition (m := m) (r := r) (n := 2 * t + 1)
        (b := b) (ν := ν) (C := ℓ + b) (e := y) hr1 (by omega) hbpos
        (by linarith [hqb, hq0]) (by linarith [hqb, hℓ25, hq]) hy0 hyb (by
          rw [show ((2 * t + 1 : ℕ) : ℝ) - 1 = (n : ℝ) - 1 from by rw [hnR]; push_cast; ring]
          exact hcoef)
      rw [show (2 * t + 1) - 1 = 2 * t from by omega] at hRCraw
      rw [show ℓ + b + y = ℓ + (b + y) from by ring,
          show ℓ + b - y = ℓ + (b - y) from by ring] at hRCraw
      have hkey := right_pair_pointwise (m := m) (t := t) (r := r) hℓ0 hmR hνdef hνpos
        hy0 hby hνy0 hνy1 hRCraw
      have e2b : 2 * b - x = b + y := by rw [hy]; ring
      have eqx : q + x = ν - y := by rw [hy, ← hqb]; ring
      have eq2b : q + (2 * b - x) = ν + y := by rw [hy, ← hqb]; ring
      have exby : x = b - y := by rw [hy]; ring
      rw [eqx, eq2b, e2b, exby]
      exact hkey
    · exact kernelr_refl_intervalIntegrable hℓ0 m r t q b a b
        (fun x hx => by rw [Set.uIcc_of_le hab.le] at hx; have := hx.2; linarith)
    · exact kernelr_intervalIntegrable hℓ0 m r t q a b hapos.le hbpos.le
  -- assemble [0,2b-a] = [0,a] + ([a,b] + [b,2b-a])
  have hIa2ba := kernelr_intervalIntegrable hℓ0 m r t q a (2 * b - a) hapos.le h2ba.le
  have hI0a := kernelr_intervalIntegrable hℓ0 m r t q 0 a le_rfl hapos.le
  have hIab := kernelr_intervalIntegrable hℓ0 m r t q a b hapos.le hbpos.le
  have hIb2ba := kernelr_intervalIntegrable hℓ0 m r t q b (2 * b - a) hbpos.le h2ba.le
  have hcomb : (∫ s in (0:ℝ)..(2 * b - a), s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s))
      = (∫ s in (0:ℝ)..a, s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s))
        + ((∫ s in a..b, s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s))
          + ∫ s in b..(2 * b - a), s ^ (r - 1) / (ℓ + s) ^ m * rho (2 * t + 1) m (q + s)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hI0a hIa2ba,
        ← intervalIntegral.integral_add_adjacent_intervals hIab hIb2ba]
  rw [hcomb]
  linarith [h0a, hpair, htail]

end OddCycleBound.HighDensity
