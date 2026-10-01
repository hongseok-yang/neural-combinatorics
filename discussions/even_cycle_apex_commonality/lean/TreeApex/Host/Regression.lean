import TreeApex.Host.Goodman

/-!
# Regression hosts (plan §2.2)

Two explicit rational hosts whose scalars are compared with the exact values printed by
`python tools/tree_entropy_check.py --host` (recorded in `TREES_NOTES.md`, T0):

| host | `E` | `D` | `R` | `σ_h` | `τ_h` |
|---|---|---|---|---|---|
| `w = (1/2, 1/2)`, `M = [[1/4, 1], [1, 0]]` | 9/16 | 41/128 | 49/512 | 33/64 | 35/128 |
| `w = (1/3, 2/3, 0)`, `M = [[1, 1/2, 0], [1/2, 1/3, 1], [0, 1, 1]]` | 13/27 | 121/486 | 205/1458 | 130/243 | 49/162 |

`σ_h` and `τ_h` are evaluated from the triple sums of `t(P₃, ·)` and `t(K₃, ·)` in `M` and `1 − M`
(not through Goodman's identity), so the agreement is an independent check of `hostDens_P₃`,
`hostDens_K₃` and of the identity itself.  The second host has a weight `0` and kernel entries
`0` and `1`.
-/

open Finset SimpleGraph

namespace TreeApex

namespace ProbHost

/-- `w = (1/2, 1/2)`, `M = [[1/4, 1], [1, 0]]`. -/
noncomputable def regHost₁ : ProbHost (Fin 2) where
  w := ![1 / 2, 1 / 2]
  w_nonneg i := by fin_cases i <;> simp
  w_sum := by simp only [Fin.sum_univ_two]; norm_num
  M := ![![1 / 4, 1], ![1, 0]]
  M_symm i j := by fin_cases i <;> fin_cases j <;> rfl
  M_nonneg i j := by fin_cases i <;> fin_cases j <;> norm_num
  M_le_one i j := by fin_cases i <;> fin_cases j <;> norm_num

/-- `w = (1/3, 2/3, 0)`, `M = [[1, 1/2, 0], [1/2, 1/3, 1], [0, 1, 1]]`. -/
noncomputable def regHost₂ : ProbHost (Fin 3) where
  w := ![1 / 3, 2 / 3, 0]
  w_nonneg i := by fin_cases i <;> norm_num [Matrix.cons_val]
  w_sum := by simp [Fin.sum_univ_three]; norm_num
  M := ![![1, 1 / 2, 0], ![1 / 2, 1 / 3, 1], ![0, 1, 1]]
  M_symm i j := by fin_cases i <;> fin_cases j <;> rfl
  M_nonneg i j := by fin_cases i <;> fin_cases j <;> norm_num
  M_le_one i j := by fin_cases i <;> fin_cases j <;> norm_num

lemma regHost₁_E : regHost₁.E = 9 / 16 := by
  simp [E, deg, regHost₁, Fin.sum_univ_two]; norm_num

lemma regHost₁_D : regHost₁.D = 41 / 128 := by
  simp [D, deg, regHost₁, Fin.sum_univ_two]; norm_num

lemma regHost₁_R : regHost₁.R = 49 / 512 := by
  simp [R, tri, cod, regHost₁, Fin.sum_univ_two]; norm_num

lemma regHost₁_sigma : regHost₁.Mh (pathGraph 3) = 33 / 64 := by
  rw [Mh, hostDens_P₃, hostDens_P₃]
  simp [regHost₁, Mc, Fin.sum_univ_two]; norm_num

lemma regHost₁_tau : regHost₁.Mh (⊤ : SimpleGraph (Fin 3)) = 35 / 128 := by
  rw [Mh, hostDens_K₃, hostDens_K₃]
  simp [regHost₁, Mc, Fin.sum_univ_two]; norm_num

lemma regHost₂_E : regHost₂.E = 13 / 27 := by
  simp [E, deg, regHost₂, Fin.sum_univ_three]; norm_num

lemma regHost₂_D : regHost₂.D = 121 / 486 := by
  simp [D, deg, regHost₂, Fin.sum_univ_three]; norm_num

lemma regHost₂_R : regHost₂.R = 205 / 1458 := by
  simp [R, tri, cod, regHost₂, Fin.sum_univ_three]; norm_num

lemma regHost₂_sigma : regHost₂.Mh (pathGraph 3) = 130 / 243 := by
  rw [Mh, hostDens_P₃, hostDens_P₃]
  simp [regHost₂, Mc, Fin.sum_univ_three]; norm_num

lemma regHost₂_tau : regHost₂.Mh (⊤ : SimpleGraph (Fin 3)) = 49 / 162 := by
  rw [Mh, hostDens_K₃, hostDens_K₃]
  simp [regHost₂, Mc, Fin.sum_univ_three]; norm_num

end ProbHost

end TreeApex
