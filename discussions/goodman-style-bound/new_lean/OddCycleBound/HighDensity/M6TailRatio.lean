/-
# High-density theorem — the residual-strip `eq:tail-ratio` bridge (M6, `app:constants`)

`M6TailFactors.lean` proved the five scalar per-factor bounds of `eq:tail-ratio`.  This file lifts
them to the powers `n`, `r`, `m` that appear in `Σ/D` and assembles the `c_n ≥ 99/100` estimate —
the remaining analytic content between those scalar bounds and the constant inequality
`(99/(100m))·P(θ)·B(θ)^m ≥ 1` (`constA_m500`, `constB_m63`).

Notation as in the paper (`odd_cycle_lower_bound_clean.tex`, proof of `lem:left-estimate`):
`θ=r/m`, `ν=n/m=1−2θ`, `a=1/2−q`, `b=ν−q`, `L=1/2−2θ`, `ε=(1−2q)/4`, `p=1−q`.

Contents:
* `rpow_npow_eq`     : `(x^a)^m = x^k` when `a·m = k` (turns `(7/6)^{1−2θ}` etc. into integer powers),
* `rpow_neg_npow_eq` : `(x^{−θ})^m = (1/x)^r` when `θ·m = r`,
* `cn_core`          : `e^{n−1} ≤ (1/100)·f^n` for `e/f ≤ 5/7`, `f ≥ 7/12`, `n ≥ 33` (the `c_n` bound),
* `tail_pow_p`, `tail_pow_eps`, `tail_pow_ratio_a`, `tail_pow_ratio_b`
                     : the four `eq:tail-A/B` factors lifted to their powers.
-/

import OddCycleBound.HighDensity.M6TailFactors
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OddCycleBound.HighDensity

/-- `(x^a)^m = x^k` (outer/`x^k` natural powers, `x^a` an `rpow`) whenever `a·m = k`. -/
lemma rpow_npow_eq {x : ℝ} (hx : 0 < x) {a : ℝ} {k m : ℕ} (hk : a * (m : ℝ) = (k : ℝ)) :
    (x ^ a) ^ m = x ^ k := by
  rw [← Real.rpow_natCast (x ^ a) m, ← Real.rpow_mul hx.le, hk, Real.rpow_natCast]

/-- `(x^{−θ})^m = (1/x)^r` whenever `θ·m = r`. -/
lemma rpow_neg_npow_eq {x : ℝ} (hx : 0 < x) {θ : ℝ} {r m : ℕ} (hk : θ * (m : ℝ) = (r : ℝ)) :
    (x ^ (-θ)) ^ m = (1 / x) ^ r := by
  rw [← Real.rpow_natCast (x ^ (-θ)) m, ← Real.rpow_mul hx.le,
    show (-θ) * (m : ℝ) = -(θ * (m : ℝ)) by ring, hk, Real.rpow_neg hx.le, Real.rpow_natCast,
    one_div, inv_pow]

/-- **The `c_n ≥ 99/100` estimate** (`app:constants`, proof of `lem:left-estimate`), abstract form:
if `0 < e`, `f ≥ 7/12`, `e ≤ (5/7)f`, and `n ≥ 33`, then `e^{n−1} ≤ (1/100)·f^n`.  Applied with
`e = q+ε`, `f = p−ε`: gives `(m/n)f^n − e^{n-1} ≥ (99/100)(m/n)f^n`. -/
lemma cn_core {n : ℕ} (hn : 33 ≤ n) {e f : ℝ} (he : 0 < e) (hf7 : (7 : ℝ) / 12 ≤ f)
    (hef : e ≤ (5 / 7) * f) : e ^ (n - 1) ≤ (1 / 100) * f ^ n := by
  have hf : (0 : ℝ) < f := by linarith
  have h1 : e ^ (n - 1) ≤ ((5 / 7) * f) ^ (n - 1) := pow_le_pow_left₀ he.le hef _
  rw [mul_pow] at h1
  have h2 : (5 / 7 : ℝ) ^ (n - 1) ≤ (5 / 7) ^ 32 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hfn1 : (0 : ℝ) ≤ f ^ (n - 1) := pow_nonneg hf.le _
  have h3 : (5 / 7 : ℝ) ^ (n - 1) * f ^ (n - 1) ≤ (5 / 7) ^ 32 * f ^ (n - 1) :=
    mul_le_mul_of_nonneg_right h2 hfn1
  have hp32 : (5 / 7 : ℝ) ^ 32 ≤ 7 / 1200 := by norm_num
  have h4 : (5 / 7 : ℝ) ^ 32 ≤ (1 / 100) * f := by linarith
  have h5 : (5 / 7 : ℝ) ^ 32 * f ^ (n - 1) ≤ ((1 / 100) * f) * f ^ (n - 1) :=
    mul_le_mul_of_nonneg_right h4 hfn1
  have hfn : f ^ n = f ^ (n - 1) * f := by rw [← pow_succ]; congr 1; omega
  calc e ^ (n - 1) ≤ (5 / 7 : ℝ) ^ (n - 1) * f ^ (n - 1) := h1
    _ ≤ (5 / 7 : ℝ) ^ 32 * f ^ (n - 1) := h3
    _ ≤ ((1 / 100) * f) * f ^ (n - 1) := h5
    _ = (1 / 100) * f ^ n := by rw [hfn]; ring

/-- **`eq:tail-A` factor `(2(p−ε))^n ≥ ((7/6)^{1−2θ})^m`** (`θ = r/m`, `n = m − 2r`). -/
lemma tail_pow_p {n r m : ℕ} (hm : 0 < m) (hnrm : (n : ℝ) = (m : ℝ) - 2 * r) {q : ℝ}
    (hq : q ≤ 1 / 3) :
    ((7 / 6 : ℝ) ^ (1 - 2 * ((r : ℝ) / m))) ^ m ≤ (2 * ((1 - q) - (1 - 2 * q) / 4)) ^ n := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hk : (1 - 2 * ((r : ℝ) / m)) * (m : ℝ) = (n : ℝ) := by rw [hnrm]; field_simp
  have e2 : ((7 / 6 : ℝ) ^ (1 - 2 * ((r : ℝ) / m))) ^ m = (7 / 6) ^ n := rpow_npow_eq (by norm_num) hk
  rw [e2]
  exact pow_le_pow_left₀ (by norm_num) (tail_two_p_eps hq) n

/-- **`eq:tail-A` factor `(ε/b)^r ≥ ((8−24θ)^{−θ})^m`** (`ε = (1−2q)/4`, `b = (1−2θ)−q`, `θ = r/m`). -/
lemma tail_pow_eps {r m : ℕ} (hm : 0 < m) {q : ℝ}
    (hq : q ≤ 1 / 3) (hθ0 : (0 : ℝ) ≤ (r : ℝ) / m) (hθ : (r : ℝ) / m ≤ 1 / 4) :
    ((8 - 24 * ((r : ℝ) / m)) ^ (-((r : ℝ) / m))) ^ m
      ≤ ((1 - 2 * q) / 4 / ((1 - 2 * ((r : ℝ) / m)) - q)) ^ r := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  set θ : ℝ := (r : ℝ) / m with hθdef
  have hx : (0 : ℝ) < 8 - 24 * θ := by rw [hθdef] at hθ ⊢; linarith
  have hk : θ * (m : ℝ) = (r : ℝ) := by rw [hθdef]; field_simp
  have e2 : ((8 - 24 * θ) ^ (-θ)) ^ m = (1 / (8 - 24 * θ)) ^ r := rpow_neg_npow_eq hx hk
  rw [e2]
  refine pow_le_pow_left₀ (by positivity) ?_ r
  exact tail_eps_b hq hθ0 hθ

/-- **`eq:tail-A` factor `((ℓ+a)/(ℓ+ε))^m ≥ ((1/2+θ)/(5/12+θ))^m`** (case a). -/
lemma tail_pow_ratio_a {m : ℕ} {q θ ℓ : ℝ} (hq : q ≤ 1 / 3) (hθ0 : 0 ≤ θ) (hℓ0 : 0 < ℓ)
    (hℓ : ℓ ≤ q + θ) :
    ((1 / 2 + θ) / (5 / 12 + θ)) ^ m ≤ ((ℓ + (1 / 2 - q)) / (ℓ + (1 - 2 * q) / 4)) ^ m :=
  pow_le_pow_left₀ (by positivity) (tail_ratio_a hq hθ0 hℓ0 hℓ) m

/-- **`eq:tail-B` factor `((ℓ+a)/(ℓ+ε))^m ≥ (34/29)^m`** (case b). -/
lemma tail_pow_ratio_b {m : ℕ} {q ℓ : ℝ} (hq : q ≤ 1 / 3) (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ 2 / 5) :
    ((34 : ℝ) / 29) ^ m ≤ ((ℓ + (1 / 2 - q)) / (ℓ + (1 - 2 * q) / 4)) ^ m :=
  pow_le_pow_left₀ (by norm_num) (tail_ratio_b hq hℓ0 hℓ) m

end OddCycleBound.HighDensity
