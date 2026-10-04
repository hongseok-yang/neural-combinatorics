import ApicesCommonness.Cycles.Host.Scalars

/-!
# Definition regression tests: the three exact 2-point hosts

Plan §2.2.  The blueprint's auxiliary program `verify_algebra.py` evaluates its scalars exactly on
three rational 2-point hosts.  Here the Lean definitions are evaluated from scratch on the same
hosts and must give the same numbers:

| host | `U` | `w` | `m` | `b` | `c` | `τ` | `p₃` | `R₄` | `r₊,₄` | `r₋,₄` |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | `[[0, 1/4], [1/4, −1/2]]` | `(1/2, 1/2)` | 0 | 1/64 | 17/2048 | −7/256 | −1/256 | 2193/2048 | 2161/2048 | 2225/2048 |
| 2 | `[[1/4, 1/4], [1/4, 1/4]]` | `(1/3, 2/3)` | 1/4 | 1/16 | 1/256 | 1/64 | 1/64 | 353/256 | 625/256 | 81/256 |
| 3 | `[[17/32, −15/32], [−15/32, 17/32]]` | `(1/2, 1/2)` | 1/32 | 1/1024 | 65537/1048576 | 4097/32768 | 1/32768 | 1120257/1048576 | 1251457/1048576 | 989057/1048576 |

`R₄` and `r_{±,4}` are computed as four-cycle densities of `S_σ = 1 ± U` directly from
`hostDensity`, not through `fourth_colour_traces`, so these tests also check that lemma's
normalization.
-/

open Finset SimpleGraph

namespace ApicesCommonness.Regression

/-- Host 1 (`case 1` of `verify_algebra.py`). -/
noncomputable def host1 : FiniteKernel 2 where
  w := ![1 / 2, 1 / 2]
  w_nonneg := by intro i; fin_cases i <;> norm_num
  w_sum := by simp only [Fin.sum_univ_two]; norm_num
  U := ![![0, 1 / 4], ![1 / 4, -1 / 2]]
  U_symm := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  U_abs_le := by intro i j; fin_cases i <;> fin_cases j <;> norm_num

/-- Host 2 (`case 2`): unequal weights. -/
noncomputable def host2 : FiniteKernel 2 where
  w := ![1 / 3, 2 / 3]
  w_nonneg := by intro i; fin_cases i <;> norm_num
  w_sum := by simp only [Fin.sum_univ_two]; norm_num
  U := ![![1 / 4, 1 / 4], ![1 / 4, 1 / 4]]
  U_symm := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  U_abs_le := by intro i j; fin_cases i <;> fin_cases j <;> norm_num

/-- Host 3 (`case 3`). -/
noncomputable def host3 : FiniteKernel 2 where
  w := ![1 / 2, 1 / 2]
  w_nonneg := by intro i; fin_cases i <;> norm_num
  w_sum := by simp only [Fin.sum_univ_two]; norm_num
  U := ![![17 / 32, -15 / 32], ![-15 / 32, 17 / 32]]
  U_symm := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  U_abs_le := by intro i j; fin_cases i <;> fin_cases j <;> norm_num

open FiniteKernel

/-- Evaluate a four-cycle density of `S_σ` on a 2-point host from the definition. -/
private lemma C4_expand (K : FiniteKernel 2) (σ : ℝ) :
    hostDensity K.w (cycleGraph 4) (K.S σ)
      = ∑ i, ∑ j, ∑ k, ∑ l, K.w i * K.w j * K.w k * K.w l *
          ((1 + σ * K.U i j) * (1 + σ * K.U i l) * (1 + σ * K.U j k) * (1 + σ * K.U k l)) := by
  rw [hostDensity_eq_edgeDensity, edgePairs_cycleGraph_four]
  unfold edgeDensity c4Edges
  simp only [sum_fun_fin_succ, Fintype.sum_unique, Fin.prod_univ_four]
  simp [S_apply, mul_assoc]

theorem host1_scalars :
    host1.m = 0 ∧ host1.b = 1 / 64 ∧ host1.c = 17 / 2048 ∧ host1.τ = -7 / 256 ∧
      host1.p3 = -1 / 256 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [m, b, f, c, τ, p3, host1, Fin.sum_univ_two] <;> norm_num

theorem host1_traces :
    host1.R 4 = 2193 / 2048 ∧ host1.rσ4 1 = 2161 / 2048 ∧ host1.rσ4 (-1) = 2225 / 2048 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [R, rσ4, C4_expand, Fin.sum_univ_two] <;> norm_num [host1]

theorem host2_scalars :
    host2.m = 1 / 4 ∧ host2.b = 1 / 16 ∧ host2.c = 1 / 256 ∧ host2.τ = 1 / 64 ∧
      host2.p3 = 1 / 64 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [m, b, f, c, τ, p3, host2, Fin.sum_univ_two] <;> norm_num

theorem host2_traces :
    host2.R 4 = 353 / 256 ∧ host2.rσ4 1 = 625 / 256 ∧ host2.rσ4 (-1) = 81 / 256 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [R, rσ4, C4_expand, Fin.sum_univ_two] <;> norm_num [host2]

theorem host3_scalars :
    host3.m = 1 / 32 ∧ host3.b = 1 / 1024 ∧ host3.c = 65537 / 1048576 ∧
      host3.τ = 4097 / 32768 ∧ host3.p3 = 1 / 32768 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [m, b, f, c, τ, p3, host3, Fin.sum_univ_two] <;> norm_num

theorem host3_traces :
    host3.R 4 = 1120257 / 1048576 ∧ host3.rσ4 1 = 1251457 / 1048576 ∧
      host3.rσ4 (-1) = 989057 / 1048576 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [R, rσ4, C4_expand, Fin.sum_univ_two] <;> norm_num [host3]

end ApicesCommonness.Regression
