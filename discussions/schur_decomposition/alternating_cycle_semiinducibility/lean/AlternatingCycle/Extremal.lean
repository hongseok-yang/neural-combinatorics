import AlternatingCycle.StepModel

/-!
# The two extremal graphons, and why `m` must be odd

§11 of `alternating_cycles_schur_proof.tex`.  The strengthened inequality
`4^m Alt_{2m}(W) + t(C_{2m},2W−1) ≤ 1` is sharp at **both** ends, and the parity hypothesis cannot
be dropped:

* `half` — the constant graphon `W ≡ 1/2`: `4^m Alt = 1`, `t(C_{2m},2W−1) = 0`.
* `bip` — the balanced complete bipartite graphon: `2W − 1 = −φ⊗φ`, so `X = −Q` for a rank-one
  projection `Q`, giving `t(C_{2m},2W−1) = 1` and, by `eq:parity-example`,
  `Tr(((P+X)(P−X))^m) = 1 + (−1)^m`.  For odd `m` that is `0` and the inequality is again an
  equality; for **even** `m` it is `2`, i.e. `Alt_{2m}(W) = 2·4^{-m}`, twice the random value.

So neither term of `eq:main-strengthened` can be dropped or given a larger coefficient, and
`thm:main` genuinely does not extend from cycles of length `4k+2` to length `4k`.

These are also the regression tests for the finite model: an error in `TW`, `TU`, `Xm` or `alt`
would show up here as a wrong constant.
-/

namespace AlternatingCycle

open Matrix Finset

noncomputable section

/-- `(M^m)₀₀ = (M₀₀)^m` for `1 × 1` matrices. -/
lemma pow_fin_one_apply (M : Matrix (Fin 1) (Fin 1) ℝ) :
    ∀ m : ℕ, (M ^ m) 0 0 = M 0 0 ^ m
  | 0 => by simp
  | m + 1 => by
      rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_one, pow_fin_one_apply M m, pow_succ]

/-! ### The constant graphon `W ≡ 1/2` -/

/-- The constant graphon `W ≡ 1/2`, as a one-cell step graphon. -/
def half : StepGraphon 1 where
  w := fun _ => 1
  W := fun _ _ => 1 / 2
  w_nonneg := fun _ => zero_le_one
  w_sum := by simp
  W_symm := fun _ _ => rfl
  W_nonneg := fun _ _ => by norm_num
  W_le_one := fun _ _ => by norm_num

@[simp] lemma half_e (i : Fin 1) : half.e i = 1 := by
  show Real.sqrt 1 = 1
  simp

@[simp] lemma half_Xm : half.Xm = 0 := by
  refine Matrix.ext fun i j => ?_
  show (2 * (1 / 2 : ℝ) - 1) * half.e i * half.e j = 0
  norm_num

lemma half_TW_mul_TU_apply : (half.TW * half.TU) 0 0 = 1 / 4 := by
  rw [Matrix.mul_apply, Fin.sum_univ_one]
  show (1 / 2 : ℝ) * half.e 0 * half.e 0 * ((1 - 1 / 2) * half.e 0 * half.e 0) = 1 / 4
  norm_num

/-- `Alt_{2m}(1/2) = 4^{-m}`: the constant graphon attains `eq:main-unweighted`. -/
theorem half_alt (m : ℕ) : half.alt m = 1 / 4 ^ m := by
  rw [StepGraphon.alt, Matrix.trace_fin_one, pow_fin_one_apply, half_TW_mul_TU_apply, div_pow]
  norm_num

theorem half_signedCycle {m : ℕ} (hm : 0 < m) : half.signedCycle m = 0 := by
  rw [StepGraphon.signedCycle, half_Xm, zero_pow (by omega), Matrix.trace_zero]

/-- Equality in `eq:main-strengthened` at the constant graphon. -/
theorem half_sharp {m : ℕ} (hm : 0 < m) :
    4 ^ m * half.alt m + half.signedCycle m = 1 := by
  rw [half_alt, half_signedCycle hm, add_zero]
  have h : (4 : ℝ) ^ m ≠ 0 := by positivity
  field_simp

/-! ### The balanced complete bipartite graphon -/

/-- The balanced complete bipartite graphon, as a two-cell step graphon. -/
def bip : StepGraphon 2 where
  w := fun _ => 1 / 2
  W := fun i j => if i = j then 0 else 1
  w_nonneg := fun _ => by norm_num
  w_sum := by simp
  W_symm := fun i j => by by_cases h : i = j <;> simp [h, eq_comm]
  W_nonneg := fun i j => by by_cases h : i = j <;> simp [h]
  W_le_one := fun i j => by by_cases h : i = j <;> simp [h]

lemma bip_e_mul (i j : Fin 2) : bip.e i * bip.e j = 1 / 2 := by
  show Real.sqrt (1 / 2) * Real.sqrt (1 / 2) = 1 / 2
  exact Real.mul_self_sqrt (by norm_num)

lemma bip_TW_apply (i j : Fin 2) : bip.TW i j = if i = j then 0 else 1 / 2 := by
  show (if i = j then (0 : ℝ) else 1) * bip.e i * bip.e j = _
  rw [mul_assoc, bip_e_mul]
  by_cases h : i = j <;> simp [h]

lemma bip_TU_apply (i j : Fin 2) : bip.TU i j = if i = j then 1 / 2 else 0 := by
  show (1 - if i = j then (0 : ℝ) else 1) * bip.e i * bip.e j = _
  rw [mul_assoc, bip_e_mul]
  by_cases h : i = j <;> simp [h]

lemma bip_Xm_apply (i j : Fin 2) : bip.Xm i j = if i = j then -(1 / 2) else 1 / 2 := by
  show (2 * (if i = j then (0 : ℝ) else 1) - 1) * bip.e i * bip.e j = _
  rw [mul_assoc, bip_e_mul]
  rcases eq_or_ne i j with h | h
  · rw [if_pos h, if_pos h]; norm_num
  · rw [if_neg h, if_neg h]; norm_num

lemma bip_TU_eq : bip.TU = ((1 : ℝ) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine Matrix.ext fun i j => ?_
  rw [bip_TU_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : i = j <;> simp [h]

lemma bip_prod : bip.TW * bip.TU = ((1 : ℝ) / 2) • bip.TW := by
  rw [bip_TU_eq, Matrix.mul_smul, Matrix.mul_one]

lemma bip_TW_sq : bip.TW * bip.TW = ((1 : ℝ) / 4) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp only [bip_TW_apply]
  fin_cases i <;> fin_cases j <;> norm_num

lemma bip_trace_TW : Matrix.trace bip.TW = 0 := by
  rw [Matrix.trace_fin_two]
  simp only [bip_TW_apply]
  norm_num

lemma bip_TW_pow_even : ∀ k : ℕ,
    bip.TW ^ (2 * k) = ((1 : ℝ) / 4) ^ k • (1 : Matrix (Fin 2) (Fin 2) ℝ)
  | 0 => by simp
  | k + 1 => by
      have h : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
      rw [h, pow_succ, pow_succ, bip_TW_pow_even k, Matrix.smul_mul, Matrix.one_mul,
        Matrix.smul_mul, bip_TW_sq, smul_smul]
      congr 1

lemma bip_TW_pow_odd (k : ℕ) : bip.TW ^ (2 * k + 1) = ((1 : ℝ) / 4) ^ k • bip.TW := by
  rw [pow_succ, bip_TW_pow_even k, Matrix.smul_mul, Matrix.one_mul]

/-- For odd `m` the alternating density at the bipartite graphon vanishes
(`eq:parity-example` with `Tr((P−Q)^m) = 0`). -/
theorem bip_alt_odd (k : ℕ) : bip.alt (2 * k + 1) = 0 := by
  rw [StepGraphon.alt, bip_prod, smul_pow, bip_TW_pow_odd, smul_smul, Matrix.trace_smul,
    bip_trace_TW, smul_zero]

/-- **The parity obstruction.**  For even `m` the alternating density is *twice* the random value,
`4^m Alt_{2m} = 2`.  This is why `thm:main` cannot extend to cycles of length `4k`. -/
theorem bip_violates_even (k : ℕ) : 4 ^ (2 * k) * bip.alt (2 * k) = 2 := by
  rw [StepGraphon.alt, bip_prod, smul_pow, bip_TW_pow_even, smul_smul, Matrix.trace_smul,
    Matrix.trace_one, smul_eq_mul]
  rw [show (Fintype.card (Fin 2) : ℝ) = 2 by simp]
  have h4 : (4 : ℝ) ^ (2 * k) = 2 ^ (2 * k) * 2 ^ (2 * k) := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  have hh : ((1 : ℝ) / 2) ^ (2 * k) = 1 / 2 ^ (2 * k) := by rw [div_pow, one_pow]
  have hq : ((1 : ℝ) / 4) ^ k = 1 / 2 ^ (2 * k) := by
    rw [div_pow, one_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  rw [h4, hh, hq]
  have hne : (2 : ℝ) ^ (2 * k) ≠ 0 := by positivity
  field_simp

lemma bip_Xm_sq : bip.Xm * bip.Xm = -bip.Xm := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]
  simp only [bip_Xm_apply]
  fin_cases i <;> fin_cases j <;> norm_num

lemma bip_Xm_pow (r : ℕ) : bip.Xm ^ (r + 1) = (-1 : ℝ) ^ r • bip.Xm := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ, ih, Matrix.smul_mul, bip_Xm_sq, pow_succ]
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
      ring

/-- At the bipartite graphon the signed even-cycle density is `1`: the other extreme point of
`eq:main-strengthened`. -/
theorem bip_signedCycle (m : ℕ) (hm : 0 < m) : bip.signedCycle m = 1 := by
  obtain ⟨r, hr⟩ : ∃ r, 2 * m = r + 1 := ⟨2 * m - 1, by omega⟩
  have hev : (-1 : ℝ) ^ r = -1 := by
    have : Odd r := by
      rcases Nat.even_or_odd r with h | h
      · exfalso
        obtain ⟨t, ht⟩ := h
        omega
      · exact h
    exact this.neg_one_pow
  rw [StepGraphon.signedCycle, hr, bip_Xm_pow, hev, Matrix.trace_smul, Matrix.trace_fin_two,
    smul_eq_mul]
  simp only [bip_Xm_apply]
  norm_num

/-- Equality in `eq:main-strengthened` at the bipartite graphon, for odd `m`. -/
theorem bip_sharp (k : ℕ) :
    4 ^ (2 * k + 1) * bip.alt (2 * k + 1) + bip.signedCycle (2 * k + 1) = 1 := by
  rw [bip_alt_odd, bip_signedCycle _ (by omega), mul_zero, zero_add]



end

end AlternatingCycle
