import ApicesCommonness.Cycles.Host.Scalars

/-!
# The even-cycle lower bound on a finite host

Blueprint `lem:finite-even-cycle`: for even `n ≥ 4`,

```
  R_n ≥ ((1 + m)^n + (1 − m)^n) / 2 ≥ 1 + C(n, 2) m² ≥ 1.
```

The Rayleigh value of `T_{S_σ}` at the unit vector `u = (√wᵢ)` is `1 + σm` (`rayleigh_TS`), so
`t(C_n, S_σ) = Tr T_{S_σ}^n ≥ (1 + σm)^n` by `lem:finite-spectral`; average the two colours.  In the
binomial expansion of `(1 + m)^n + (1 − m)^n` the odd powers cancel and the even ones are
nonnegative; keep the terms of degree zero and two.
-/

open Finset Matrix SimpleGraph

namespace ApicesCommonness

/-- `((1 + x)^n + (1 − x)^n) / 2 ≥ 1 + C(n, 2) x²` for `n ≥ 2` (any real `x`). -/
lemma one_add_choose_two_le_binomial_mean (x : ℝ) {n : ℕ} (h2 : 2 ≤ n) :
    1 + (n.choose 2 : ℝ) * x ^ 2 ≤ ((1 + x) ^ n + (1 - x) ^ n) / 2 := by
  have hexp : (1 + x) ^ n + (1 - x) ^ n
      = ∑ k ∈ range (n + 1), (x ^ k + (-x) ^ k) * (n.choose k : ℝ) := by
    rw [add_comm 1 x, sub_eq_neg_add, add_pow, add_pow, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [one_pow, mul_one, mul_one]
    ring
  have hnn : ∀ k ∈ range (n + 1), 0 ≤ (x ^ k + (-x) ^ k) * (n.choose k : ℝ) := by
    intro k _
    refine mul_nonneg ?_ (Nat.cast_nonneg _)
    rcases Nat.even_or_odd k with hk | hk
    · rw [hk.neg_pow]
      have := hk.pow_nonneg x
      linarith
    · rw [hk.neg_pow]
      linarith
  have hsub : ({0, 2} : Finset ℕ) ⊆ range (n + 1) := by
    intro k hk
    simp only [mem_insert, mem_singleton] at hk
    rw [mem_range]
    omega
  have hle := sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ => hnn k hk)
  rw [sum_pair (by norm_num)] at hle
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, even_two, Even.neg_pow]
    at hle
  rw [hexp]
  linarith

namespace FiniteKernel

variable {d : ℕ} (K : FiniteKernel d)

/-- `t(C_n, S_σ) ≥ (1 + σ m)^n` for even `n ≥ 4`: the Rayleigh bound at the unit vector. -/
lemma colour_cycle_ge {n : ℕ} (hn : Even n) (h3 : 3 ≤ n) (σ : ℝ) :
    (1 + σ * K.m) ^ n ≤ hostDensity K.w (cycleGraph n) (K.S σ) := by
  rw [hostDensity_cycle_eq_trace K.w_nonneg (K.S_symm σ) h3, ← K.rayleigh_TS σ]
  exact rayleigh_pow_le_trace_pow (K.TS_isHermitian σ) K.unit_dot_self hn

/-- **`lem:finite-even-cycle`.**  For even `n ≥ 4`,
`R_n ≥ ((1 + m)^n + (1 − m)^n) / 2 ≥ 1 + C(n, 2) m² ≥ 1`. -/
theorem even_cycle_lower_bound {n : ℕ} (hn : Even n) (h4 : 4 ≤ n) :
    ((1 + K.m) ^ n + (1 - K.m) ^ n) / 2 ≤ K.R n ∧
      1 + (n.choose 2 : ℝ) * K.m ^ 2 ≤ ((1 + K.m) ^ n + (1 - K.m) ^ n) / 2 ∧ 1 ≤ K.R n := by
  have hp := K.colour_cycle_ge hn (by omega) 1
  have hm := K.colour_cycle_ge hn (by omega) (-1)
  rw [one_mul] at hp
  rw [neg_one_mul, ← sub_eq_add_neg] at hm
  have h1 : ((1 + K.m) ^ n + (1 - K.m) ^ n) / 2 ≤ K.R n := by
    rw [R]; linarith
  have h2 := one_add_choose_two_le_binomial_mean K.m (n := n) (by omega)
  have h3 : 0 ≤ (n.choose 2 : ℝ) * K.m ^ 2 := by positivity
  exact ⟨h1, h2, by linarith⟩

end FiniteKernel

end ApicesCommonness
