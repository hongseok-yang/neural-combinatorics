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

/-! ### `eq:constant-B` arithmetic tail: `(99/(100m))·72·(126/125)^m ≥ 1` for all `m ≥ 63`

Unlike `eq:constant-A` (whose weak `P ≥ 51`/`B₀ ≥ 201/200` bound only closes `m ≥ 500`, leaving the
finite sweep `63 ≤ m ≤ 499`), the `eq:constant-B` weak bounds `P ≥ 72`, `B₁ ≥ 126/125` close the
**entire** `m ≥ 63` range uniformly: `f(m) = (126/125)^m/m` is decreasing for `m ≤ 125` and increasing
for `m ≥ 125`, so its minimum over `m ≥ 63` is `f(125) = f(126) = (126/125)^125/125`, and
`(99/100)·72·f(125) > 1`.  Hence **no** finite certificate sweep is needed on the `B`-side. -/

/-- Decreasing step of `f(m) = (126/125)^m/m` for `1 ≤ k ≤ 125`: `f(k+1) ≤ f(k)` (ratio
`(126/125)·k/(k+1) ≤ 1 ⟺ k ≤ 125`). -/
lemma constB_step_down {k : ℕ} (hk1 : 1 ≤ k) (hk125 : k ≤ 125) :
    (126 / 125 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) ≤ (126 / 125) ^ k / (k : ℝ) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hppos : (0 : ℝ) < (126 / 125 : ℝ) ^ k := by positivity
  have hkle : (k : ℝ) ≤ 125 := by exact_mod_cast hk125
  rw [pow_succ, div_le_div_iff₀ hk1pos hkpos]
  nlinarith [mul_nonneg hppos.le (by linarith : (0 : ℝ) ≤ 125 - (k : ℝ))]

/-- Increasing step of `f(m) = (126/125)^m/m` for `k ≥ 125`: `f(k) ≤ f(k+1)`. -/
lemma constB_step_up {k : ℕ} (hk125 : 125 ≤ k) :
    (126 / 125 : ℝ) ^ k / (k : ℝ) ≤ (126 / 125) ^ (k + 1) / ((k : ℝ) + 1) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hppos : (0 : ℝ) < (126 / 125 : ℝ) ^ k := by positivity
  have hkge : (125 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk125
  rw [pow_succ, div_le_div_iff₀ hkpos hk1pos]
  nlinarith [mul_nonneg hppos.le (by linarith : (0 : ℝ) ≤ (k : ℝ) - 125)]

/-- Antitone branch on `[1,125]`: for `1 ≤ a ≤ b ≤ 125`, `f(b) ≤ f(a)`. -/
lemma constB_antitone_aux {a : ℕ} (ha : 1 ≤ a) {b : ℕ} (hab : a ≤ b) (hb : b ≤ 125) :
    (126 / 125 : ℝ) ^ b / (b : ℝ) ≤ (126 / 125) ^ a / (a : ℝ) := by
  revert hb
  induction b, hab using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ k hk ih =>
    intro hb
    have hk125 : k ≤ 125 := by omega
    have hka : 1 ≤ k := le_trans ha hk
    have hstep := constB_step_down hka hk125
    have ihk := ih hk125
    push_cast
    exact le_trans hstep ihk

/-- Increasing branch: `f(125) ≤ f(m)` for `m ≥ 125`. -/
lemma constB_pow_div_ge_min_up {m : ℕ} (h : 125 ≤ m) :
    (126 / 125 : ℝ) ^ 125 / 125 ≤ (126 / 125) ^ m / (m : ℝ) := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hstep := constB_step_up hk
    push_cast
    exact le_trans ih hstep

/-- **Two-sided minimum of `f(m) = (126/125)^m/m` over `m ≥ 63`.**  Attained at `m = 125` (`= 126`):
`f(125) ≤ f(m)` for every `m ≥ 63`. -/
lemma constB_pow_div_ge_min {m : ℕ} (hm : 63 ≤ m) :
    (126 / 125 : ℝ) ^ 125 / 125 ≤ (126 / 125) ^ m / (m : ℝ) := by
  rcases Nat.lt_or_ge m 125 with h | h
  · have h1 : 1 ≤ m := by omega
    have h2 : m ≤ 125 := by omega
    have hkey := constB_antitone_aux h1 h2 (le_refl 125)
    simpa using hkey
  · exact constB_pow_div_ge_min_up h

set_option exponentiation.threshold 200 in
/-- **`eq:constant-B` arithmetic tail.**  For `m ≥ 63`, `(99/(100m))·72·(126/125)^m ≥ 1`.  This is
`eq:constant-B` with `P(θ)` replaced by its lower bound `72` (`P_ge_72`) and `B₁(θ)` by `126/125`
(`B1_ge`); the two-sided minimum `(126/125)^m/m ≥ (126/125)^125/125` (`constB_pow_div_ge_min`) plus the
base value `(99/100)(72/125)(126/125)^125 > 1` close the whole range. -/
lemma constB_tail {m : ℕ} (hm : 63 ≤ m) :
    1 ≤ 99 / (100 * (m : ℝ)) * 72 * (126 / 125) ^ m := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (63 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hbase : (1 : ℝ) ≤ 99 * 72 / 100 * ((126 / 125) ^ 125 / 125) := by norm_num
  have hkey : 99 * 72 / 100 * ((126 / 125) ^ 125 / 125)
      ≤ 99 * 72 / 100 * ((126 / 125) ^ m / (m : ℝ)) :=
    mul_le_mul_of_nonneg_left (constB_pow_div_ge_min hm) (by norm_num)
  have heq : 99 / (100 * (m : ℝ)) * 72 * (126 / 125) ^ m
      = 99 * 72 / 100 * ((126 / 125) ^ m / (m : ℝ)) := by field_simp
  rw [heq]; linarith [hbase, hkey]

/-! ### `eq:constant-B`: the `rpow` factor bound `B₁(θ) ≥ 126/125` on `[1/6, 1/4]`

`B₁(θ) = (7/6)^{1-2θ}·(8-24θ)^{-θ}·(34/29)`.  Proved by the paper's 12-piece subdivision of `[1/6,1/4]`
into `[(24+i)/144, (25+i)/144]`: on each piece a monotonicity bound (`B1_mono`) reduces `B₁(θ)` to its
endpoint value `(7/6)^{1-2b}(8-24a)^{-b}(34/29)`, and that value `≥ 126/125` is verified by raising to
the common power `144` (`B1_cert`, turning the `rpow`s into `natpow`s) and a `norm_num` (with the
exponentiation threshold raised).  Together with `P_ge_72` this is the `θ`-factor content of
`eq:constant-B`. -/

/-- Monotonicity: on `[a,b] ⊆ [1/6,1/4]`, the endpoint value bounds `B₁(θ)` below.  `(7/6)^{1-2θ}` is
decreasing (`rpow` exponent), and `(8-24θ)^{-θ}` is increasing (base `↓`, exponent `↑` under a `≥ 1`
base), via `Real.rpow_le_rpow_of_exponent_le` / `Real.rpow_le_rpow` + `one_div` antitone. -/
lemma B1_mono {a b θ : ℝ} (ha16 : 1 / 6 ≤ a) (hab : a ≤ θ) (hθb : θ ≤ b) (hb14 : b ≤ 1 / 4) :
    (7 / 6 : ℝ) ^ (1 - 2 * b) * (8 - 24 * a) ^ (-b) * (34 / 29)
      ≤ (7 / 6) ^ (1 - 2 * θ) * (8 - 24 * θ) ^ (-θ) * (34 / 29) := by
  have h824θ : (0 : ℝ) < 8 - 24 * θ := by linarith
  have h824a : (1 : ℝ) ≤ 8 - 24 * a := by linarith
  have h1 : (7 / 6 : ℝ) ^ (1 - 2 * b) ≤ (7 / 6) ^ (1 - 2 * θ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hpow : (8 - 24 * θ : ℝ) ^ θ ≤ (8 - 24 * a) ^ b :=
    le_trans (Real.rpow_le_rpow h824θ.le (by linarith) (by linarith))
      (Real.rpow_le_rpow_of_exponent_le h824a (by linarith))
  have h2 : (8 - 24 * a : ℝ) ^ (-b) ≤ (8 - 24 * θ) ^ (-θ) := by
    rw [Real.rpow_neg (by linarith), Real.rpow_neg h824θ.le, inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos h824θ θ) hpow
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul h1 h2 (by positivity) (by positivity)) (by norm_num)

/-- Certificate reducer: the endpoint value `≥ 126/125` follows from the `144`-th-power `natpow`
inequality `(126/125)^144 ≤ (7/6)^p·(1/(8-24a)^q)·(34/29)^144`, where `p = (1-2b)·144`, `q = b·144`. -/
lemma B1_cert {a b : ℝ} (ha : (0 : ℝ) < 8 - 24 * a) (p q : ℕ)
    (hp : (1 - 2 * b) * ((144 : ℕ) : ℝ) = (p : ℝ)) (hq : b * ((144 : ℕ) : ℝ) = (q : ℝ))
    (hnat : (126 / 125 : ℝ) ^ 144 ≤ (7 / 6) ^ p * (1 / (8 - 24 * a) ^ q) * (34 / 29) ^ 144) :
    (126 / 125 : ℝ) ≤ (7 / 6) ^ (1 - 2 * b) * (8 - 24 * a) ^ (-b) * (34 / 29) := by
  have hXpos : (0 : ℝ) < (7 / 6) ^ (1 - 2 * b) * (8 - 24 * a) ^ (-b) * (34 / 29) := by positivity
  apply le_of_pow_le_pow_left₀ (n := 144) (by norm_num) hXpos.le
  rw [mul_pow, mul_pow, ← Real.rpow_natCast ((7 / 6 : ℝ) ^ (1 - 2 * b)) 144,
      ← Real.rpow_natCast ((8 - 24 * a : ℝ) ^ (-b)) 144, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul ha.le, hp, show (-b) * ((144 : ℕ) : ℝ) = -(q : ℝ) from by rw [← hq]; ring,
      Real.rpow_natCast, Real.rpow_neg ha.le, Real.rpow_natCast, ← inv_eq_one_div] at *
  exact hnat

set_option exponentiation.threshold 400 in
/-- **`eq:constant-B` factor bound `B₁(θ) ≥ 126/125`** for `1/6 ≤ θ ≤ 1/4` (12-piece subdivision). -/
lemma B1_ge {θ : ℝ} (h16 : (1 : ℝ) / 6 ≤ θ) (h14 : θ ≤ 1 / 4) :
    (126 / 125 : ℝ) ≤ (7 / 6) ^ (1 - 2 * θ) * (8 - 24 * θ) ^ (-θ) * (34 / 29) := by
  rcases le_or_gt θ ((25:ℝ)/144) with h0 | h0
  · exact le_trans (B1_cert (a := (24:ℝ)/144) (by norm_num) 94 25 (by norm_num) (by norm_num) (by norm_num)) (B1_mono (by norm_num) (by linarith) h0 (by norm_num))
  rcases le_or_gt θ ((26:ℝ)/144) with h1 | h1
  · exact le_trans (B1_cert (a := (25:ℝ)/144) (by norm_num) 92 26 (by norm_num) (by norm_num) (by norm_num)) (B1_mono (by norm_num) (le_of_lt h0) h1 (by norm_num))
  rcases le_or_gt θ ((27:ℝ)/144) with h2 | h2
  · exact le_trans (B1_cert (a := (26:ℝ)/144) (by norm_num) 90 27 (by norm_num) (by norm_num) (by norm_num)) (B1_mono (by norm_num) (le_of_lt h1) h2 (by norm_num))
  rcases le_or_gt θ ((28:ℝ)/144) with h3 | h3
  · exact le_trans (B1_cert (a := (27:ℝ)/144) (by norm_num) 88 28 (by norm_num) (by norm_num) (by norm_num)) (B1_mono (by norm_num) (le_of_lt h2) h3 (by norm_num))
  rcases le_or_gt θ ((29:ℝ)/144) with h4 | h4
  · exact le_trans (B1_cert (a := (28:ℝ)/144) (by norm_num) 86 29 (by norm_num) (by norm_num) (by norm_num)) (B1_mono (by norm_num) (le_of_lt h3) h4 (by norm_num))
  rcases le_or_gt θ ((30:ℝ)/144) with h5 | h5
  · exact le_trans (B1_cert (a := (29:ℝ)/144) (by norm_num) 84 30 (by norm_num) (by norm_num) (by norm_num)) (B1_mono (by norm_num) (le_of_lt h4) h5 (by norm_num))
  rcases le_or_gt θ ((31:ℝ)/144) with h6 | h6
  · exact le_trans (B1_cert (a := (30:ℝ)/144) (by norm_num) 82 31 (by norm_num) (by norm_num) (by norm_num)) (B1_mono (by norm_num) (le_of_lt h5) h6 (by norm_num))
  rcases le_or_gt θ ((32:ℝ)/144) with h7 | h7
  · exact le_trans (B1_cert (a := (31:ℝ)/144) (by norm_num) 80 32 (by norm_num) (by norm_num) (by norm_num)) (B1_mono (by norm_num) (le_of_lt h6) h7 (by norm_num))
  rcases le_or_gt θ ((33:ℝ)/144) with h8 | h8
  · exact le_trans (B1_cert (a := (32:ℝ)/144) (by norm_num) 78 33 (by norm_num) (by norm_num) (by norm_num)) (B1_mono (by norm_num) (le_of_lt h7) h8 (by norm_num))
  rcases le_or_gt θ ((34:ℝ)/144) with h9 | h9
  · exact le_trans (B1_cert (a := (33:ℝ)/144) (by norm_num) 76 34 (by norm_num) (by norm_num) (by norm_num)) (B1_mono (by norm_num) (le_of_lt h8) h9 (by norm_num))
  rcases le_or_gt θ ((35:ℝ)/144) with h10 | h10
  · exact le_trans (B1_cert (a := (34:ℝ)/144) (by norm_num) 74 35 (by norm_num) (by norm_num) (by norm_num)) (B1_mono (by norm_num) (le_of_lt h9) h10 (by norm_num))
  · exact le_trans (B1_cert (a := (35:ℝ)/144) (by norm_num) 72 36 (by norm_num) (by norm_num) (by norm_num)) (B1_mono (by norm_num) (le_of_lt h10) h14 (by norm_num))

end OddCycleBound.HighDensity
