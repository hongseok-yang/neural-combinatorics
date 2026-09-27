import EvenCycleApex.Finite.ThreeApex

/-!
# Every apex number on a finite host

Blueprint `thm:finite-main`.  From three apices to `k ≥ 3` by apex lifting (`lem:apex-lifting`):
`A_{n/2,k} ≥ A_{n/2,3}^{k/3} / R_n^{k/3−1} ≥ R_n^{k/3} / R_n^{k/3−1} = R_n` (`apex_relative_host`),
using `A_{n/2,3} ≥ R_n ≥ 1`.  With the one- and two-apex bounds, `A_{n/2,k} ≥ 1` for every `k ≥ 1`
(`one_le_A`), and `all_even_apex_bounds` collects the three bounds of `thm:finite-main` (for two
apices the bound `Θ(b, c)^{n/4}` of plan D10).
-/

namespace EvenCycleApex

namespace FiniteKernel

variable {d : ℕ} (K : FiniteKernel d)

/-- **`A_{n/2,k} ≥ R_n` for `k ≥ 3`** on every finite host. -/
theorem apex_relative_host {n k : ℕ} (hn : Even n) (h4 : 4 ≤ n) (hk : 3 ≤ k) :
    K.R n ≤ K.A n k := by
  have hR1 : 1 ≤ K.R n := (K.even_cycle_lower_bound hn h4).2.2
  have hR0 : 0 < K.R n := by linarith
  have h3 := K.three_apex_relative hn h4
  have hlift := K.apex_number_moment_lifting (n := n) (s := 3) (k := k) (by norm_num) hk hR0
  push_cast at hlift
  have hexp : (0 : ℝ) ≤ (k : ℝ) / 3 := by positivity
  have hmono : K.R n ^ ((k : ℝ) / 3) ≤ K.A n 3 ^ ((k : ℝ) / 3) := Real.rpow_le_rpow hR0.le h3 hexp
  have hpos : 0 < K.R n ^ ((k : ℝ) / 3 - 1) := Real.rpow_pos_of_pos hR0 _
  have hR : K.R n = K.R n ^ ((k : ℝ) / 3) / K.R n ^ ((k : ℝ) / 3 - 1) := by
    have hk0 : 0 < K.R n ^ ((k : ℝ) / 3) := Real.rpow_pos_of_pos hR0 _
    rw [Real.rpow_sub hR0, Real.rpow_one]
    field_simp
  calc K.R n = K.R n ^ ((k : ℝ) / 3) / K.R n ^ ((k : ℝ) / 3 - 1) := hR
    _ ≤ K.A n 3 ^ ((k : ℝ) / 3) / K.R n ^ ((k : ℝ) / 3 - 1) :=
        div_le_div_of_nonneg_right hmono hpos.le
    _ ≤ K.A n k := hlift

/-- `A_{n/2,k} ≥ 1` for every `k ≥ 1` on every finite host. -/
theorem one_le_A {n k : ℕ} (hn : Even n) (h4 : 4 ≤ n) (hk : 1 ≤ k) : 1 ≤ K.A n k := by
  rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | h3
  · exact K.one_le_A_one hn h4
  · exact K.one_le_A_two hn h4
  · exact (K.even_cycle_lower_bound hn h4).2.2.trans (K.apex_relative_host hn h4 h3)

/-- **`thm:finite-main`.**  For every even `n ≥ 4` on every finite host:
`A_{n/2,1} ≥ (X²/(1+b))^{n/4} ≥ 1` (`X = E Π₁`); `A_{n/2,2} ≥ Θ(b,c)^{n/4} ≥ 1` (plan D10); and
`A_{n/2,k} ≥ R_n ≥ 1` for every `k ≥ 3`. -/
theorem all_even_apex_bounds {n : ℕ} (hn : Even n) (h4 : 4 ≤ n) :
    ((K.EPi 1 ^ 2 / (1 + K.b)) ^ ((n : ℝ) / 4) ≤ K.A n 1 ∧
        1 ≤ (K.EPi 1 ^ 2 / (1 + K.b)) ^ ((n : ℝ) / 4)) ∧
      (twoApexTheta K.b K.c ^ ((n : ℝ) / 4) ≤ K.A n 2 ∧ 1 ≤ twoApexTheta K.b K.c ^ ((n : ℝ) / 4)) ∧
      (∀ k, 3 ≤ k → K.R n ≤ K.A n k) ∧ 1 ≤ K.R n :=
  ⟨K.one_apex_bound hn h4, K.two_apex_bound hn h4, fun _ hk => K.apex_relative_host hn h4 hk,
    (K.even_cycle_lower_bound hn h4).2.2⟩

end FiniteKernel

end EvenCycleApex
