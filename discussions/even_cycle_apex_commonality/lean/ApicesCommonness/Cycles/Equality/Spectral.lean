import ApicesCommonness.Cycles.Finite.AllApices

/-!
# Near even-trace equality, the fourth trace is controlled

Blueprint `lem:spectral-interpolation` and `lem:spectral-concentration`, and their host form
(DEVIATIONS X4): on every finite host, for even `n > 4`,

```
  R₄ ≤ ½ ∑_σ [ t_σ^{4/n} + 4^{(n−4)/(n−2)} max(t_σ − (1 + σm)ⁿ, 0)^{2/(n−2)} ],   t_σ = t(C_n, S_σ)
```

(`R_four_le`), from the Rayleigh value `1 + σm` of `T_{S_σ}` at the unit vector and `Tr T_{S_σ}² ≤ 4`.
-/

open Finset Matrix SimpleGraph

namespace ApicesCommonness

/-- **`lem:spectral-interpolation`.**  For `xᵢ ≥ 0` and `n > 4`,
`∑ xᵢ⁴ ≤ (∑ xᵢ²)^{(n−4)/(n−2)} (∑ xᵢⁿ)^{2/(n−2)}` (Hölder). -/
theorem finite_spectral_remainder_interpolation {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) {n : ℕ} (hn : 4 < n) :
    ∑ i ∈ s, x i ^ 4 ≤ (∑ i ∈ s, x i ^ 2) ^ (((n : ℝ) - 4) / ((n : ℝ) - 2))
      * (∑ i ∈ s, x i ^ n) ^ (2 / ((n : ℝ) - 2)) := by
  have hn4 : (4 : ℝ) < n := by exact_mod_cast hn
  have hn2' : (n : ℝ) - 2 ≠ 0 := by intro h; linarith
  have hn4' : (n : ℝ) - 4 ≠ 0 := by intro h; linarith
  set p : ℝ := ((n : ℝ) - 2) / ((n : ℝ) - 4) with hp
  set q : ℝ := ((n : ℝ) - 2) / 2 with hq
  have hp1 : 1 < p := by rw [hp, lt_div_iff₀ (by linarith)]; linarith
  have hpq : p.HolderConjugate q := by
    rw [Real.holderConjugate_iff_eq_conjExponent hp1, hp, hq]
    field_simp
    ring
  have hp0 : p ≠ 0 := by linarith
  have hq0 : q ≠ 0 := by rw [hq]; intro h; linarith [show (n : ℝ) - 2 = 0 by linarith]
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s hpq (f := fun i => (x i ^ 2) ^ (1 / p))
    (g := fun i => (x i ^ n) ^ (1 / q)) (fun i hi => by have := hx i hi; positivity)
    (fun i hi => by have := hx i hi; positivity)
  have hf : ∀ i ∈ s, ((x i ^ 2) ^ (1 / p)) ^ p = x i ^ 2 := fun i hi => by
    rw [← Real.rpow_mul (by have := hx i hi; positivity), one_div_mul_cancel hp0, Real.rpow_one]
  have hg : ∀ i ∈ s, ((x i ^ n) ^ (1 / q)) ^ q = x i ^ n := fun i hi => by
    rw [← Real.rpow_mul (by have := hx i hi; positivity), one_div_mul_cancel hq0, Real.rpow_one]
  have hexp : (2 : ℝ) * (1 / p) + (n : ℝ) * (1 / q) = 4 := by
    rw [hp, hq]
    field_simp
    ring
  have hfg : ∀ i ∈ s, (x i ^ 2) ^ (1 / p) * (x i ^ n) ^ (1 / q) = x i ^ 4 := fun i hi => by
    have h0 := hx i hi
    calc (x i ^ 2) ^ (1 / p) * (x i ^ n) ^ (1 / q)
        = x i ^ ((2 : ℝ) * (1 / p)) * x i ^ ((n : ℝ) * (1 / q)) := by
          rw [← Real.rpow_natCast (x i) 2, ← Real.rpow_natCast (x i) n, ← Real.rpow_mul h0,
            ← Real.rpow_mul h0]
          norm_num
      _ = x i ^ ((2 : ℝ) * (1 / p) + (n : ℝ) * (1 / q)) :=
          (Real.rpow_add' h0 (by rw [hexp]; norm_num)).symm
      _ = x i ^ 4 := by
          rw [hexp, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [sum_congr rfl hf, sum_congr rfl hg, sum_congr rfl hfg] at h
  have e1 : 1 / p = ((n : ℝ) - 4) / ((n : ℝ) - 2) := by rw [hp, one_div_div]
  have e2 : 1 / q = 2 / ((n : ℝ) - 2) := by rw [hq, one_div_div]
  rwa [e1, e2] at h

variable {d : ℕ} {B : Matrix (Fin d) (Fin d) ℝ}

/-- **`lem:spectral-concentration`** (with any Rayleigh value `ρ ≥ 0`).  For a symmetric `B`
with `Tr B² ≤ 4`, a unit vector `g` with `ρ = ⟨g, Bg⟩ ≥ 0`, and even `n > 4`,
`Tr B⁴ ≤ (Tr Bⁿ)^{4/n} + 4^{(n−4)/(n−2)} max(Tr Bⁿ − ρⁿ, 0)^{2/(n−2)}`. -/
theorem finite_fourth_trace_from_even_trace (hB : B.IsHermitian) {g : Fin d → ℝ}
    (hg : g ⬝ᵥ g = 1) (hρ : 0 ≤ g ⬝ᵥ (B *ᵥ g)) (h2 : trace (B ^ 2) ≤ 4) {n : ℕ} (hn : Even n)
    (h5 : 4 < n) :
    trace (B ^ 4) ≤ trace (B ^ n) ^ ((4 : ℝ) / n)
      + 4 ^ (((n : ℝ) - 4) / ((n : ℝ) - 2))
        * max (trace (B ^ n) - (g ⬝ᵥ (B *ᵥ g)) ^ n) 0 ^ (2 / ((n : ℝ) - 2)) := by
  set lam := (eigenSystemOf hB).val with hlam
  set ρ := g ⬝ᵥ (B *ᵥ g) with hρdef
  have hne : (univ : Finset (Fin d)).Nonempty := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [dotProduct] at hg
    · exact ⟨⟨0, hd⟩, mem_univ _⟩
  obtain ⟨i₀, -, hmax⟩ := exists_max_image univ lam hne
  -- the Rayleigh value is at most the largest eigenvalue
  have hρle : ρ ≤ lam i₀ := by
    rw [hρdef, dot_mulVec_eq_sum_eigen hB, ← hlam]
    calc ∑ i, lam i * eigenCoord hB g i ^ 2 ≤ ∑ i, lam i₀ * eigenCoord hB g i ^ 2 :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hmax i (mem_univ i)) (sq_nonneg _)
      _ = lam i₀ := by rw [← mul_sum, sum_eigenCoord_sq hB g, hg, mul_one]
  have hl0 : 0 ≤ lam i₀ := hρ.trans hρle
  have hn4 : (4 : ℝ) < n := by exact_mod_cast h5
  have hev : ∀ i, 0 ≤ lam i ^ n := fun i => hn.pow_nonneg _
  set t := trace (B ^ n) with ht
  have htsum : t = ∑ i, lam i ^ n := by rw [ht, trace_pow_eq_sum_eigen hB]
  have hsplit : ∀ k : ℕ, ∑ i, lam i ^ k = lam i₀ ^ k + ∑ i ∈ univ.erase i₀, lam i ^ k := fun k => by
    rw [add_comm, sum_erase_add _ _ (mem_univ i₀)]
  -- the top eigenvalue: `λ⁴ ≤ t^{4/n}`
  have hrest_n : 0 ≤ ∑ i ∈ univ.erase i₀, lam i ^ n := sum_nonneg fun i _ => hev i
  have htop : lam i₀ ^ 4 ≤ t ^ ((4 : ℝ) / n) := by
    have hle : lam i₀ ^ n ≤ t := by rw [htsum, hsplit n]; linarith
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    calc lam i₀ ^ 4 = (lam i₀ ^ n) ^ ((4 : ℝ) / n) := by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hl0]
          congr 1
          field_simp
          norm_num
      _ ≤ t ^ ((4 : ℝ) / n) := Real.rpow_le_rpow (hev i₀) hle (by positivity)
  -- the other eigenvalues, by interpolation
  have hint := finite_spectral_remainder_interpolation (univ.erase i₀) (fun i => |lam i|)
    (fun i _ => abs_nonneg _) h5
  simp only [(show Even 4 by decide).pow_abs, (show Even 2 by decide).pow_abs, hn.pow_abs] at hint
  have h2sum : ∑ i ∈ univ.erase i₀, lam i ^ 2 ≤ 4 := by
    have := trace_pow_eq_sum_eigen hB 2
    rw [← hlam, hsplit 2] at this
    nlinarith [sq_nonneg (lam i₀)]
  have hnsum : ∑ i ∈ univ.erase i₀, lam i ^ n ≤ max (t - ρ ^ n) 0 := by
    refine le_max_of_le_left ?_
    have : ρ ^ n ≤ lam i₀ ^ n := pow_le_pow_left₀ hρ hρle n
    rw [htsum, hsplit n]
    linarith
  have hα : (0 : ℝ) ≤ ((n : ℝ) - 4) / ((n : ℝ) - 2) := div_nonneg (by linarith) (by linarith)
  have hβ : (0 : ℝ) ≤ 2 / ((n : ℝ) - 2) := div_nonneg (by norm_num) (by linarith)
  have hrest4 : ∑ i ∈ univ.erase i₀, lam i ^ 4
      ≤ 4 ^ (((n : ℝ) - 4) / ((n : ℝ) - 2)) * max (t - ρ ^ n) 0 ^ (2 / ((n : ℝ) - 2)) := by
    refine hint.trans (mul_le_mul (Real.rpow_le_rpow (sum_nonneg fun i _ => sq_nonneg _) h2sum hα)
      (Real.rpow_le_rpow hrest_n hnsum hβ) (Real.rpow_nonneg hrest_n _) (by positivity))
  rw [trace_pow_eq_sum_eigen hB 4, ← hlam, hsplit 4]
  linarith

namespace FiniteKernel

variable (K : FiniteKernel d)

/-- `Tr T_{S_σ}² = ∑ wᵢ wⱼ S_σ(i,j)² ≤ 4` for `σ = ±1`. -/
lemma trace_TS_sq_le {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : trace (K.TS σ ^ 2) ≤ 4 := by
  have h : trace (K.TS σ ^ 2) = ∑ i, ∑ j, K.w i * K.w j * K.S σ i j ^ 2 := by
    rw [sq, trace, TS]
    simp only [diag_apply, mul_apply, hostMatrix_apply]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [K.S_symm σ j i]
    have hi := Real.mul_self_sqrt (K.w_nonneg i)
    have hj := Real.mul_self_sqrt (K.w_nonneg j)
    calc K.S σ i j * √(K.w i) * √(K.w j) * (K.S σ i j * √(K.w j) * √(K.w i))
        = K.S σ i j ^ 2 * (√(K.w i) * √(K.w i)) * (√(K.w j) * √(K.w j)) := by ring
      _ = K.w i * K.w j * K.S σ i j ^ 2 := by rw [hi, hj]; ring
  rw [h]
  calc ∑ i, ∑ j, K.w i * K.w j * K.S σ i j ^ 2 ≤ ∑ i, ∑ j, K.w i * K.w j * 4 := by
        refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
        have h0 := K.S_nonneg hσ i j
        have h2 := K.S_le_two hσ i j
        exact mul_le_mul_of_nonneg_left (by nlinarith) (mul_nonneg (K.w_nonneg i) (K.w_nonneg j))
    _ = 4 := by simp only [← sum_mul, ← mul_sum, K.w_sum, mul_one, one_mul]

/-- The upper bound for `R₄` in terms of the colour cycle densities and `m` (DEVIATIONS X4). -/
noncomputable def fourthBound (n : ℕ) (t : ℝ) (ρ : ℝ) : ℝ :=
  t ^ ((4 : ℝ) / n) + 4 ^ (((n : ℝ) - 4) / ((n : ℝ) - 2)) * max (t - ρ ^ n) 0 ^ (2 / ((n : ℝ) - 2))

/-- `r_{σ,4} ≤ fourthBound(t(C_n, S_σ), 1 + σm)`. -/
lemma rσ4_le_fourthBound {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {n : ℕ} (hn : Even n) (h5 : 4 < n) :
    K.rσ4 σ ≤ fourthBound n (hostDensity K.w (cycleGraph n) (K.S σ)) (1 + σ * K.m) := by
  have hρ : 0 ≤ hostUnit K.w ⬝ᵥ (K.TS σ *ᵥ hostUnit K.w) := by
    rw [K.rayleigh_TS σ]
    have := abs_le.mp K.abs_m_le_one
    rcases hσ with rfl | rfl <;> linarith
  have h := finite_fourth_trace_from_even_trace (K.TS_isHermitian σ) K.unit_dot_self hρ
    (K.trace_TS_sq_le hσ) hn h5
  rw [K.rayleigh_TS σ] at h
  rw [K.rσ4_eq_trace, fourthBound, hostDensity_cycle_eq_trace K.w_nonneg (K.S_symm σ) (by omega)]
  exact h

/-- **The host form of `lem:spectral-concentration`** (DEVIATIONS X4). -/
theorem R_four_le_fourthBound {n : ℕ} (hn : Even n) (h5 : 4 < n) :
    K.R 4 ≤ (fourthBound n (hostDensity K.w (cycleGraph n) (K.S 1)) (1 + 1 * K.m)
      + fourthBound n (hostDensity K.w (cycleGraph n) (K.S (-1))) (1 + -1 * K.m)) / 2 := by
  have h1 := K.rσ4_le_fourthBound (Or.inl rfl) hn h5
  have h2 := K.rσ4_le_fourthBound (Or.inr rfl) hn h5
  change (K.rσ4 1 + K.rσ4 (-1)) / 2 ≤ _
  linarith

end FiniteKernel

end ApicesCommonness
