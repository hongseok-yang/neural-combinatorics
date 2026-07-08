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

end OddCycleBound.HighDensity
