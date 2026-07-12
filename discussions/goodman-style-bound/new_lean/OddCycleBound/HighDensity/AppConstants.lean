/-
# High-density theorem — `app:constants`, the `m ≥ 500` tail arithmetic (`eq:constant-A`)

`eq:constant-A` (`app:constants`) needs `(99/(100m))·P(θ)·B₀(θ)^m ≥ 1` for admissible pairs with
`m ≥ 63`.  The paper verifies `63 ≤ m ≤ 499` by exact rational evaluation and closes `m ≥ 500`
uniformly with `P(θ) ≥ 51` (`P_ge_51`), `B₀(θ) ≥ 201/200`, and the growth of `(201/200)^m/m`.

This file supplies the **arithmetic tail**: `constA_tail`, i.e. `(99/(100m))·51·(201/200)^m ≥ 1` for
`m ≥ 500` (the `P`-factor bounded below by `51` and `B₀` by `201/200`).  It reduces `eq:constant-A` for
`m ≥ 500` to the single `rpow` factor bound `B₀(θ) ≥ 201/200` (`0 < θ ≤ 1/6`), which is the only piece
left — and one now de-risked: with `exponentiation.threshold` raised, each subdivision piece of
`B₀`/`B₁` reduces (via `rpow`-monotonicity + raising to a common power) to a `norm_num`-checkable
rational inequality.

Ingredients: `pow_div_mono` (`(201/200)^m/m` increasing for `m ≥ 200`, so `≥` its `m = 500` value) and
the base case `(99·51)/(100·500)·(201/200)^500 ≥ 1` (a direct `norm_num` once the exponentiation
threshold is raised past `500`).
-/

import Mathlib.Tactic

namespace OddCycleBound.HighDensity

/-- `f(m) = (201/200)^m / m` is increasing for `m ≥ 500` (indeed for `m ≥ 200`): the step ratio is
`(201/200)·m/(m+1) ≥ 1 ⟺ m ≥ 200`.  Hence `f(m) ≥ f(500)`. -/
lemma pow_div_mono {m : ℕ} (hm : 500 ≤ m) :
    (201 / 200 : ℝ) ^ 500 / 500 ≤ (201 / 200) ^ m / (m : ℝ) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hk500 : (500 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    have hppos : (0 : ℝ) < (201 / 200 : ℝ) ^ k := by positivity
    have hstep : (201 / 200 : ℝ) ^ k / (k : ℝ) ≤ (201 / 200) ^ (k + 1) / ((k : ℝ) + 1) := by
      rw [pow_succ, div_le_div_iff₀ hkpos hk1pos]
      nlinarith [hppos, hk500]
    rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) from by push_cast; ring] at hstep
    linarith [ih, hstep]

set_option exponentiation.threshold 600 in
/-- **`eq:constant-A` arithmetic tail.**  For `m ≥ 500`, `(99/(100m))·51·(201/200)^m ≥ 1`.  This is
`eq:constant-A` with `P(θ)` replaced by its lower bound `51` (`P_ge_51`) and `B₀(θ)` by `201/200`; the
only remaining input for `eq:constant-A` at `m ≥ 500` is the `rpow` factor bound `B₀(θ) ≥ 201/200`. -/
lemma constA_tail {m : ℕ} (hm : 500 ≤ m) :
    1 ≤ 99 / (100 * (m : ℝ)) * 51 * (201 / 200) ^ m := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (500 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hbase : (1 : ℝ) ≤ 99 * 51 / 100 * ((201 / 200) ^ 500 / 500) := by norm_num
  have hkey : 99 * 51 / 100 * ((201 / 200) ^ 500 / 500)
      ≤ 99 * 51 / 100 * ((201 / 200) ^ m / (m : ℝ)) :=
    mul_le_mul_of_nonneg_left (pow_div_mono hm) (by norm_num)
  have heq : 99 / (100 * (m : ℝ)) * 51 * (201 / 200) ^ m
      = 99 * 51 / 100 * ((201 / 200) ^ m / (m : ℝ)) := by field_simp
  rw [heq]; linarith [hbase, hkey]

end OddCycleBound.HighDensity
