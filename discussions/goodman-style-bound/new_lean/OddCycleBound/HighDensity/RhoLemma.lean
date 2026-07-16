/-
# High-density theorem — the sign structure of `ρ` (M3 foundation, paper lem:rho)

Pure real-analysis (no graphons, no integrals).  `ρ_{n,m}(u) = (m/n)(uⁿ+(1-u)ⁿ) − u^{n-1}`
(paper eq:rho-def) governs the sign of the diagonal kernel via the one-dimensional integral form.
This file proves the self-contained polynomial facts of `lem:rho`: the reflection inequality
`ρ(u)+ρ(1-u) ≥ 0` and the left window `ρ(u) ≥ 0` for `u ≤ 1/2`.  Throughout `n = 2t+1` is odd, so
`n-1 = 2t` is even.
-/

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace OddCycleBound.HighDensity

/-- `ρ_{n,m}(u) = (m/n)(uⁿ + (1-u)ⁿ) − u^{n-1}`. -/
noncomputable def rho (n m : ℕ) (u : ℝ) : ℝ :=
  (m / n : ℝ) * (u ^ n + (1 - u) ^ n) - u ^ (n - 1)

/-- For odd `n` and `a + b ≥ 0`, `aⁿ + bⁿ ≥ 0` (the larger of `a,b` dominates in odd power). -/
lemma odd_add_pow_nonneg {n : ℕ} (hn : Odd n) {a b : ℝ} (hab : 0 ≤ a + b) : 0 ≤ a ^ n + b ^ n := by
  rcases le_total a b with h | h
  · rcases le_total 0 a with ha | ha
    · exact add_nonneg (pow_nonneg ha n) (pow_nonneg (by linarith) n)
    · have hle : (-a) ^ n ≤ b ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      rw [hn.neg_pow] at hle; linarith
  · rcases le_total 0 b with hb | hb
    · exact add_nonneg (pow_nonneg (by linarith) n) (pow_nonneg hb n)
    · have hle : (-b) ^ n ≤ a ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      rw [hn.neg_pow] at hle; linarith

/-- `(2u-1)·(u^{2t} − (1-u)^{2t}) ≥ 0`: the two factors share the sign of `2u-1`. -/
lemma sign_prod (t : ℕ) (u : ℝ) : 0 ≤ (2 * u - 1) * (u ^ (2 * t) - (1 - u) ^ (2 * t)) := by
  have hgeom := geom_sum₂_mul (u ^ 2) ((1 - u) ^ 2) t
  rw [← pow_mul, ← pow_mul, show u ^ 2 - (1 - u) ^ 2 = 2 * u - 1 from by ring] at hgeom
  rw [← hgeom, show (2 * u - 1)
      * ((∑ i ∈ Finset.range t, (u ^ 2) ^ i * ((1 - u) ^ 2) ^ (t - 1 - i)) * (2 * u - 1))
      = (∑ i ∈ Finset.range t, (u ^ 2) ^ i * ((1 - u) ^ 2) ^ (t - 1 - i)) * (2 * u - 1) ^ 2 from by
    ring]
  exact mul_nonneg
    (Finset.sum_nonneg fun i _ => mul_nonneg (pow_nonneg (sq_nonneg u) i) (pow_nonneg (sq_nonneg _) _))
    (sq_nonneg _)

/-- Reflection identity `2(u^{2t+1}+(1-u)^{2t+1}) − u^{2t} − (1-u)^{2t} = (2u-1)(u^{2t}−(1-u)^{2t})`. -/
lemma two_pow_sub_eq (t : ℕ) (u : ℝ) :
    2 * (u ^ (2 * t + 1) + (1 - u) ^ (2 * t + 1)) - u ^ (2 * t) - (1 - u) ^ (2 * t)
      = (2 * u - 1) * (u ^ (2 * t) - (1 - u) ^ (2 * t)) := by
  rw [pow_succ u (2 * t), pow_succ (1 - u) (2 * t)]; ring

/-- **Reflection nonnegativity (`lem:rho`(iii)).**  For odd `n = 2t+1` with `n ≤ m`,
`ρ(u) + ρ(1-u) ≥ 0` for every real `u`. -/
lemma rho_reflect (t m : ℕ) (hm : (2 * t + 1 : ℝ) ≤ (m : ℝ)) (u : ℝ) :
    0 ≤ rho (2 * t + 1) m u + rho (2 * t + 1) m (1 - u) := by
  have hn1 : (0 : ℝ) < 2 * (t : ℝ) + 1 := by positivity
  have hsum : rho (2 * t + 1) m u + rho (2 * t + 1) m (1 - u)
      = (m : ℝ) / (2 * (t : ℝ) + 1) * (2 * (u ^ (2 * t + 1) + (1 - u) ^ (2 * t + 1)))
        - u ^ (2 * t) - (1 - u) ^ (2 * t) := by
    unfold rho
    rw [show (1 : ℝ) - (1 - u) = u from by ring, show (2 * t + 1) - 1 = 2 * t from by omega]
    push_cast
    ring
  rw [hsum]
  have hS : 0 ≤ u ^ (2 * t + 1) + (1 - u) ^ (2 * t + 1) :=
    odd_add_pow_nonneg ⟨t, by ring⟩ (by linarith)
  have hmn : (1 : ℝ) ≤ (m : ℝ) / (2 * (t : ℝ) + 1) := by
    rw [le_div_iff₀ hn1]; linarith
  have h1 : 2 * (u ^ (2 * t + 1) + (1 - u) ^ (2 * t + 1))
      ≤ (m : ℝ) / (2 * (t : ℝ) + 1) * (2 * (u ^ (2 * t + 1) + (1 - u) ^ (2 * t + 1))) := by
    nlinarith [hS, hmn, mul_nonneg (sub_nonneg.mpr hmn) hS]
  have h2 := two_pow_sub_eq t u
  have h3 := sign_prod t u
  linarith [h1, h2, h3]

/-- Grouping formula (`lem:rho`(i), first form):
`ρ(u) = (m/n)(1-u)((1-u)^{n-1} − u^{n-1}) + (m/n − 1)u^{n-1}`, `n = 2t+1`. -/
lemma rho_rearrange1 (t m : ℕ) (u : ℝ) :
    rho (2 * t + 1) m u
      = (m : ℝ) / (2 * (t : ℝ) + 1) * (1 - u) * ((1 - u) ^ (2 * t) - u ^ (2 * t))
        + ((m : ℝ) / (2 * (t : ℝ) + 1) - 1) * u ^ (2 * t) := by
  unfold rho
  rw [show (2 * t + 1) - 1 = 2 * t from by omega]
  push_cast
  rw [pow_succ u (2 * t), pow_succ (1 - u) (2 * t)]
  ring

/-- **Left window (`lem:rho`(ii)).**  For odd `n = 2t+1` with `n ≤ m` and `u ≤ 1/2`, `ρ(u) ≥ 0`. -/
lemma rho_window_left (t m : ℕ) (hm : (2 * (t : ℝ) + 1) ≤ (m : ℝ)) (u : ℝ) (hu : u ≤ 1 / 2) :
    0 ≤ rho (2 * t + 1) m u := by
  rw [rho_rearrange1]
  have hc : (1 : ℝ) ≤ (m : ℝ) / (2 * (t : ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hpow : u ^ (2 * t) ≤ (1 - u) ^ (2 * t) :=
    calc u ^ (2 * t) = (u ^ 2) ^ t := by rw [pow_mul]
      _ ≤ ((1 - u) ^ 2) ^ t := pow_le_pow_left₀ (sq_nonneg u) (by nlinarith [hu]) t
      _ = (1 - u) ^ (2 * t) := by rw [pow_mul]
  have hterm1 : 0 ≤ (m : ℝ) / (2 * (t : ℝ) + 1) * (1 - u) * ((1 - u) ^ (2 * t) - u ^ (2 * t)) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hterm2 : 0 ≤ ((m : ℝ) / (2 * (t : ℝ) + 1) - 1) * u ^ (2 * t) :=
    mul_nonneg (by linarith) (by rw [pow_mul]; exact pow_nonneg (sq_nonneg u) t)
  linarith

/-- Grouping formula (`lem:rho`(i), second form):
`ρ(u) = (m/n)(1-u)^n + u^{n-1}((m/n)u − 1)`, `n = 2t+1`. -/
lemma rho_rearrange2 (t m : ℕ) (u : ℝ) :
    rho (2 * t + 1) m u
      = (m : ℝ) / (2 * (t : ℝ) + 1) * (1 - u) ^ (2 * t + 1)
        + u ^ (2 * t) * ((m : ℝ) / (2 * (t : ℝ) + 1) * u - 1) := by
  unfold rho
  rw [show (2 * t + 1) - 1 = 2 * t from by omega]
  push_cast
  rw [pow_succ u (2 * t)]
  ring

/-- **Right window (`lem:rho`(ii)).**  For odd `n = 2t+1` with `n ≤ m` and `n ≤ m·u` (i.e. `u ≥ n/m`),
`ρ(u) ≥ 0`.  Splits at `u = 1`: for `u ≤ 1` the second grouping is nonnegative termwise; for `u ≥ 1`
the geometric factorisation gives `uⁿ − (u−1)ⁿ ≥ u^{n-1}`. -/
lemma rho_window_right (t m : ℕ) (hm : (2 * (t : ℝ) + 1) ≤ (m : ℝ)) (u : ℝ)
    (hu : (2 * (t : ℝ) + 1) ≤ (m : ℝ) * u) : 0 ≤ rho (2 * t + 1) m u := by
  have hn1 : (0 : ℝ) < 2 * (t : ℝ) + 1 := by positivity
  have hmn : (1 : ℝ) ≤ (m : ℝ) / (2 * (t : ℝ) + 1) := by rw [le_div_iff₀ hn1]; linarith
  rcases le_total u 1 with hle1 | hge1
  · rw [rho_rearrange2]
    have hB2 : (1 : ℝ) ≤ (m : ℝ) / (2 * (t : ℝ) + 1) * u := by
      rw [show (m : ℝ) / (2 * (t : ℝ) + 1) * u = (m : ℝ) * u / (2 * (t : ℝ) + 1) from by ring,
        le_div_iff₀ hn1, one_mul]; linarith
    have hA : 0 ≤ (m : ℝ) / (2 * (t : ℝ) + 1) * (1 - u) ^ (2 * t + 1) :=
      mul_nonneg (by positivity) (pow_nonneg (by linarith) _)
    have hB : 0 ≤ u ^ (2 * t) * ((m : ℝ) / (2 * (t : ℝ) + 1) * u - 1) :=
      mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg u) t) (by linarith)
    linarith
  · have hgeom := geom_sum₂_mul u (u - 1) (2 * t + 1)
    rw [show u - (u - 1) = 1 from by ring, mul_one] at hgeom
    have hterm_nonneg : ∀ i ∈ Finset.range (2 * t + 1),
        (0 : ℝ) ≤ u ^ i * (u - 1) ^ (2 * t + 1 - 1 - i) :=
      fun i _ => mul_nonneg (pow_nonneg (by linarith) i) (pow_nonneg (by linarith) _)
    have hsum_ge : u ^ (2 * t) ≤ ∑ i ∈ Finset.range (2 * t + 1), u ^ i * (u - 1) ^ (2 * t + 1 - 1 - i) := by
      have h2t : 2 * t ∈ Finset.range (2 * t + 1) := Finset.mem_range.2 (by omega)
      have := Finset.single_le_sum hterm_nonneg h2t
      simpa [show 2 * t + 1 - 1 - 2 * t = 0 from by omega] using this
    have hD : u ^ (2 * t) ≤ u ^ (2 * t + 1) - (u - 1) ^ (2 * t + 1) := hgeom ▸ hsum_ge
    have hu2t : (0 : ℝ) ≤ u ^ (2 * t) := by rw [pow_mul]; positivity
    have hDpos : (0 : ℝ) ≤ u ^ (2 * t + 1) - (u - 1) ^ (2 * t + 1) := le_trans hu2t hD
    have h1u : (1 - u) ^ (2 * t + 1) = -((u - 1) ^ (2 * t + 1)) := by
      rw [show (1 : ℝ) - u = -(u - 1) from by ring, Odd.neg_pow ⟨t, by ring⟩]
    unfold rho
    rw [show (2 * t + 1) - 1 = 2 * t from by omega, h1u]
    push_cast
    nlinarith [hmn, hD, mul_nonneg (sub_nonneg.mpr hmn) hDpos]

/-- **Window (`lem:rho`(ii), combined).**  `ρ(u) ≥ 0` for `u ∉ (1/2, n/m)` — i.e. whenever `u ≤ 1/2`
or `n ≤ m·u` (`u ≥ n/m`). -/
lemma rho_window (t m : ℕ) (hm : (2 * (t : ℝ) + 1) ≤ (m : ℝ)) (u : ℝ)
    (hu : u ≤ 1 / 2 ∨ (2 * (t : ℝ) + 1) ≤ (m : ℝ) * u) : 0 ≤ rho (2 * t + 1) m u := by
  rcases hu with h | h
  · exact rho_window_left t m hm u h
  · exact rho_window_right t m hm u h

/-- **Empty negative window (`lem:rho`(iv)).**  If `m ≥ 2n` (`n = 2t+1`), then `ρ(u) ≥ 0` for every
real `u`: the possible negative window `(1/2, n/m)` is empty since `n/m ≤ 1/2`.  This is the key input
for the `2r ≥ n` regime of `thm:pointwise`. -/
lemma rho_empty (t m : ℕ) (hm : 2 * (2 * (t : ℝ) + 1) ≤ (m : ℝ)) (u : ℝ) :
    0 ≤ rho (2 * t + 1) m u := by
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  rcases le_total u (1 / 2) with hle | hge
  · exact rho_window_left t m (by linarith) u hle
  · refine rho_window_right t m (by linarith) u ?_
    have hmpos : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have hprod := mul_le_mul hm hge (by norm_num) hmpos
    linarith

/-- **One-sided negative bound (`lem:rho`(v)).**  For `u ≤ 1` (in particular on the negative window
`(1/2, n/m)`), `−ρ(u) ≤ u^{n-1}(1 − (m/n)u)`, by dropping the nonnegative term `(m/n)(1-u)ⁿ` from the
second grouping. -/
lemma rho_neg (t m : ℕ) (u : ℝ) (hu : u ≤ 1) :
    -rho (2 * t + 1) m u ≤ u ^ (2 * t) * (1 - (m : ℝ) / (2 * (t : ℝ) + 1) * u) := by
  rw [rho_rearrange2]
  have h : 0 ≤ (m : ℝ) / (2 * (t : ℝ) + 1) * (1 - u) ^ (2 * t + 1) :=
    mul_nonneg (by positivity) (pow_nonneg (by linarith) _)
  have expand : -((m : ℝ) / (2 * (t : ℝ) + 1) * (1 - u) ^ (2 * t + 1)
        + u ^ (2 * t) * ((m : ℝ) / (2 * (t : ℝ) + 1) * u - 1))
      = u ^ (2 * t) * (1 - (m : ℝ) / (2 * (t : ℝ) + 1) * u)
        - (m : ℝ) / (2 * (t : ℝ) + 1) * (1 - u) ^ (2 * t + 1) := by ring
  rw [expand]
  linarith

/-- **Left-surplus bound (`lem:rho`(vi), `eq:rho-positive-left`).**  For `u ≥ 0`,
`ρ(u) ≥ (m/n)(1-u)ⁿ − u^{n-1}`, by dropping the nonnegative term `(m/n)uⁿ`. -/
lemma rho_left_surplus (t m : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    (m : ℝ) / (2 * (t : ℝ) + 1) * (1 - u) ^ (2 * t + 1) - u ^ (2 * t) ≤ rho (2 * t + 1) m u := by
  unfold rho
  rw [show (2 * t + 1) - 1 = 2 * t from by omega]
  push_cast
  have h : (0 : ℝ) ≤ (m : ℝ) / (2 * (t : ℝ) + 1) * u ^ (2 * t + 1) :=
    mul_nonneg (by positivity) (pow_nonneg hu _)
  nlinarith [h]

/-- **Right-tail bound (`lem:rho`(vi), `eq:rho-positive-right`).**  For `ν < u ≤ 1` (`ν = n/m`),
`ρ(u) ≥ ((u−ν)/ν)·u^{n-1}`.  From `νρ(u) = uⁿ+(1-u)ⁿ − νu^{n-1}`, discard `(1-u)ⁿ ≥ 0` (`u ≤ 1`). -/
lemma rho_pos_tail (t m : ℕ) (hm : (2 * (t : ℝ) + 1) ≤ (m : ℝ)) (u : ℝ) (hu : u ≤ 1) :
    (u - (2 * (t : ℝ) + 1) / m) / ((2 * (t : ℝ) + 1) / m) * u ^ (2 * t) ≤ rho (2 * t + 1) m u := by
  have hn1 : (0 : ℝ) < 2 * (t : ℝ) + 1 := by positivity
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hνpos : (0 : ℝ) < (2 * (t : ℝ) + 1) / m := by positivity
  have h1u : (0 : ℝ) ≤ (1 - u) ^ (2 * t + 1) := by
    rcases lt_or_eq_of_le hu with h | h
    · exact pow_nonneg (by linarith) _
    · rw [h]; simp
  have hexp : rho (2 * t + 1) m u * ((2 * (t : ℝ) + 1) / m)
      - (u - (2 * (t : ℝ) + 1) / m) * u ^ (2 * t) = (1 - u) ^ (2 * t + 1) := by
    unfold rho
    rw [show (2 * t + 1) - 1 = 2 * t from by omega, pow_succ u (2 * t)]
    push_cast
    field_simp
    ring
  rw [div_mul_eq_mul_div, div_le_iff₀ hνpos]
  linarith [h1u, hexp]

end OddCycleBound.HighDensity
