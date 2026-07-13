/-
# High-density theorem — the residual-strip `eq:tail-ratio` scalar factor bounds (M6, `app:constants`)

`lem:left-estimate` bounds `Σ/D` from below by the product (`eq:tail-ratio`,
`odd_cycle_lower_bound_clean.tex`, proof of `lem:left-estimate`)
`Σ/D ≥ c_n · (b/(rL²)) · (2(p−ε))ⁿ · (ε/b)^r · ((ℓ+a)/(ℓ+ε))ᵐ`, in the notation
`θ=r/m`, `ν=n/m=1−2θ`, `a=1/2−q`, `b=ν−q`, `L=b−a=1/2−2θ`, `ε=a/2=(1−2q)/4`, `p=1−q`.
Bounding each factor by a rational/`θ`-only quantity turns this into `Σ/D ≥ (99/(100m))·P(θ)·B(θ)^m`
(`eq:tail-A` for `θ≤1/6`, `eq:tail-B` for `θ≥1/6`), whose scalar tail is closed by `app:constants`
(`constA_m500`, `constB_m63`).

This file supplies the **scalar per-factor bounds** — the algebraic heart of that reduction, all
`rpow`-free (the remaining bridge only has to raise these to the powers `n`, `r`, `m`):

* `tail_two_p_eps`  : `2(p−ε) ≥ 7/6`                            (`⟺ q ≤ 1/3`),
* `tail_eps_b`      : `ε/b ≥ 1/(8−24θ)`                          (surplus `(1−3q)(1−4θ) ≥ 0`),
* `tail_b_over_Lsq` : `b/L² ≥ (2/3−2θ)/L²`                       (`⟺ q ≤ 1/3`; the `P`-factor),
* `tail_ratio_a`    : `(ℓ+a)/(ℓ+ε) ≥ (1/2+θ)/(5/12+θ)`          (case a, `θ≤1/6`, `ℓ≤q+θ`),
* `tail_ratio_b`    : `(ℓ+a)/(ℓ+ε) ≥ 34/29`                      (case b, `ℓ≤2/5`),
* `tail_cn_lower`   : `1 − (12/7)(5/7)³² > 99/100`               (the `c_n ≥ 99/100` constant).
-/

import Mathlib.Tactic

namespace OddCycleBound.HighDensity

/-- **`eq:tail-A` factor `2(p−ε) ≥ 7/6`** (`p = 1−q`, `ε = (1−2q)/4`).  Reduces to `q ≤ 1/3`:
`2(p−ε) = (3−2q)/2 ≥ 7/6 ⟺ q ≤ 1/3`. -/
lemma tail_two_p_eps {q : ℝ} (hq : q ≤ 1 / 3) :
    (7 : ℝ) / 6 ≤ 2 * ((1 - q) - (1 - 2 * q) / 4) := by
  linarith

/-- **`eq:tail-A` factor `ε/b ≥ 1/(8−24θ)`** (`ε = (1−2q)/4`, `b = ν−q = (1−2θ)−q`).  The cleared
surplus `(1−2q)/4·(8−24θ) − ((1−2θ)−q) = (1−3q)(1−4θ)` is `≥ 0` on `q ≤ 1/3`, `θ ≤ 1/6`. -/
lemma tail_eps_b {q θ : ℝ} (hq : q ≤ 1 / 3) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 4) :
    1 / (8 - 24 * θ) ≤ ((1 - 2 * q) / 4) / ((1 - 2 * θ) - q) := by
  have hd : (0 : ℝ) < 8 - 24 * θ := by linarith
  have hb : (0 : ℝ) < (1 - 2 * θ) - q := by linarith
  rw [div_le_div_iff₀ hd hb]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 3 * q) (by linarith : (0 : ℝ) ≤ 1 - 4 * θ)]

/-- **`eq:tail-A` `P`-factor `b/L² ≥ (2/3−2θ)/L²`** (`b = (1−2θ)−q`, `L = 1/2−2θ`).  Same positive
denominator `L²`, so it reduces to the numerator `b ≥ 2/3−2θ ⟺ q ≤ 1/3`. -/
lemma tail_b_over_Lsq {q θ : ℝ} (hq : q ≤ 1 / 3) (hθ : θ < 1 / 4) :
    (2 / 3 - 2 * θ) / (1 / 2 - 2 * θ) ^ 2 ≤ ((1 - 2 * θ) - q) / (1 / 2 - 2 * θ) ^ 2 := by
  have hL : (0 : ℝ) < (1 / 2 - 2 * θ) ^ 2 := by
    have : (0 : ℝ) < 1 / 2 - 2 * θ := by linarith
    positivity
  rw [div_le_div_iff₀ hL hL]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 3 - q) (sq_nonneg (1 / 2 - 2 * θ))]

/-- **`eq:tail-A` factor `(ℓ+a)/(ℓ+ε) ≥ (1/2+θ)/(5/12+θ)`** (case a, `θ ≤ 1/6`; `a = 1/2−q`,
`ε = (1−2q)/4`).  The ratio is decreasing in `ℓ` (since `a > ε`), so it suffices at `ℓ = q+θ`; the
cleared surplus is `(q+θ−ℓ)/12 + (1−3q)(1+2θ)/12 ≥ 0`. -/
lemma tail_ratio_a {q θ ℓ : ℝ} (hq : q ≤ 1 / 3) (hθ0 : 0 ≤ θ) (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ q + θ) :
    (1 / 2 + θ) / (5 / 12 + θ) ≤ (ℓ + (1 / 2 - q)) / (ℓ + (1 - 2 * q) / 4) := by
  have hd1 : (0 : ℝ) < 5 / 12 + θ := by linarith
  have hd2 : (0 : ℝ) < ℓ + (1 - 2 * q) / 4 := by linarith
  rw [div_le_div_iff₀ hd1 hd2]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 3 * q) (by linarith : (0 : ℝ) ≤ 1 + 2 * θ),
    (by linarith : (0 : ℝ) ≤ q + θ - ℓ)]

/-- **`eq:tail-B` factor `(ℓ+a)/(ℓ+ε) ≥ 34/29`** (case b, `ℓ ≤ 2/5`; `a = 1/2−q`, `ε = (1−2q)/4`).
Cleared surplus `(6 − 12q − 5ℓ)/29 ≥ 0` from `q ≤ 1/3` and `ℓ ≤ 2/5`. -/
lemma tail_ratio_b {q ℓ : ℝ} (hq : q ≤ 1 / 3) (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ 2 / 5) :
    (34 : ℝ) / 29 ≤ (ℓ + (1 / 2 - q)) / (ℓ + (1 - 2 * q) / 4) := by
  have hd2 : (0 : ℝ) < ℓ + (1 - 2 * q) / 4 := by nlinarith [hℓ0, (by linarith : (0:ℝ) ≤ 1 - 2 * q)]
  rw [le_div_iff₀ hd2]
  nlinarith [hq, hℓ]

/-- **The `c_n ≥ 99/100` constant of `eq:tail-A/B`** (`app:constants`, proof of `lem:left-estimate`):
`c_n ≥ 1 − ν(q+ε)^{n-1}/(p−ε)^n ≥ 1 − (12/7)(5/7)^{32} > 99/100` for `n ≥ 33`. -/
lemma tail_cn_lower : (99 : ℝ) / 100 < 1 - 12 / 7 * (5 / 7) ^ 32 := by
  norm_num

end OddCycleBound.HighDensity
