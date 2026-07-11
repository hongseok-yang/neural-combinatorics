/-
# High-density theorem — the integration-by-parts range (M3, `thm:ibp`, `r = 1`)

`lem:ibp` (clean tex) / `thm:ibp` (paper): for `q ∈ [0,1/2]`, the diagonal kernel is nonnegative
whenever `ℓ ≥ q + r/m`.  This file does the `r = 1` case (all we need to close `thm:r1`), via the
finite Beta form `gform_eq` (`r = 1` ⇒ the Beta weight is `1`).

With `V(x) = qx+ℓ(1-x)`, `W(x) = (1-q)x−ℓ(1-x)`, `n = m−2 = 2t+1`, writing
`J_f = ∫₀¹ f dx`, the diagonal kernel is `C_{m,1}·I` with
`I = (m/n)(J_{Vⁿ} + J_{Wⁿ}) − J_{xVⁿ⁻¹}`.  It is nonnegative because
* `J_{Wⁿ} ≥ 0` (Beta symmetry `x ↦ 1-x`: `W(x)+W(1-x) = 1−q−ℓ ≥ 0`, odd powers), `jW_nonneg`;
* `J_{Vⁿ} ≥ 0` (`V ≥ 0` for `q,ℓ ≥ 0`);
* `J_{xVⁿ⁻¹} ≤ J_{Vⁿ}/(n(ℓ−q))` from the FTC identity
  `J_{Vⁿ} + n(q−ℓ)J_{xVⁿ⁻¹} = qⁿ` on `x·Vⁿ` (`jXV_ftc`), using `qⁿ ≥ 0`;
* `ℓ ≥ q+1/m ⟹ m/n ≥ 1/(n(ℓ−q))`.
-/

import OddCycleBound.HighDensity.KernelForm
import OddCycleBound.HighDensity.KernelR1

open MeasureTheory intervalIntegral
open scoped BigOperators

namespace OddCycleBound.HighDensity

/-- **Beta symmetry (`E[Wⁿ] ≥ 0`).**  For odd `n = 2t+1` and `ℓ ≤ 1−q`, `∫₀¹ W(x)ⁿ dx ≥ 0`, where
`W(x) = (1-q)x + (-ℓ)(1-x)`.  Reflecting `x ↦ 1-x` (the constant Beta weight is symmetric),
`2 J_W = ∫₀¹ (W(x)ⁿ + W(1-x)ⁿ)` and `W(x) + W(1-x) = 1−q−ℓ ≥ 0`, so the integrand is `≥ 0` termwise. -/
lemma jW_nonneg (t : ℕ) (q ℓ : ℝ) (hW : 0 ≤ 1 - q - ℓ) :
    0 ≤ ∫ x in (0:ℝ)..1, ((1 - q) * x + (-ℓ) * (1 - x)) ^ (2 * t + 1) := by
  set f : ℝ → ℝ := fun y => ((1 - q) * y + (-ℓ) * (1 - y)) ^ (2 * t + 1) with hf
  have hcont : Continuous f := by rw [hf]; fun_prop
  have hcont' : Continuous (fun x => f (1 - x)) := by rw [hf]; fun_prop
  have hrefl : (∫ x in (0:ℝ)..1, f (1 - x)) = ∫ x in (0:ℝ)..1, f x := by
    simpa using intervalIntegral.integral_comp_sub_left f (1 : ℝ)
  have hpt : 0 ≤ ∫ x in (0:ℝ)..1, (f x + f (1 - x)) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _
    rw [hf]
    have hab : (0:ℝ) ≤ ((1 - q) * x + (-ℓ) * (1 - x))
        + ((1 - q) * (1 - x) + (-ℓ) * (1 - (1 - x))) := by
      have he : ((1 - q) * x + (-ℓ) * (1 - x)) + ((1 - q) * (1 - x) + (-ℓ) * (1 - (1 - x)))
          = 1 - q - ℓ := by ring
      rw [he]; exact hW
    exact odd_add_pow_nonneg ⟨t, by ring⟩ hab
  rw [intervalIntegral.integral_add (hcont.intervalIntegrable 0 1) (hcont'.intervalIntegrable 0 1),
    hrefl] at hpt
  linarith

/-- **The FTC identity behind the IBP estimate (`r = 1`).**  For `V(x) = qx+ℓ(1-x)` and `n = 2t+1`,
`∫₀¹ Vⁿ + n(q−ℓ)∫₀¹ x·Vⁿ⁻¹ = qⁿ`, from `∫₀¹ d/dx[x·Vⁿ] = 1·V(1)ⁿ − 0 = qⁿ` (`V(1) = q`). -/
lemma jXV_ftc (t : ℕ) (q ℓ : ℝ) :
    (∫ x in (0:ℝ)..1, (q * x + ℓ * (1 - x)) ^ (2 * t + 1))
      + (2 * (t : ℝ) + 1) * (q - ℓ)
          * (∫ x in (0:ℝ)..1, x * (q * x + ℓ * (1 - x)) ^ (2 * t))
      = q ^ (2 * t + 1) := by
  have hVderiv : ∀ x : ℝ, HasDerivAt (fun y => q * y + ℓ * (1 - y)) (q - ℓ) x := fun x => by
    have h1 : HasDerivAt (fun y : ℝ => q * y) q x := by simpa using (hasDerivAt_id x).const_mul q
    have h2 : HasDerivAt (fun y : ℝ => ℓ * (1 - y)) (-ℓ) x := by
      simpa using (((hasDerivAt_id x).const_sub (1 : ℝ)).const_mul ℓ)
    have h3 : HasDerivAt (fun y : ℝ => q * y + ℓ * (1 - y)) (q + -ℓ) x := h1.add h2
    simpa only [sub_eq_add_neg] using h3
  -- FTC on `x·Vⁿ`; the derivative in its clean shape `Vⁿ + n(q−ℓ)·x·Vⁿ⁻¹`
  have hFderiv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun y => y * (q * y + ℓ * (1 - y)) ^ (2 * t + 1))
        ((q * x + ℓ * (1 - x)) ^ (2 * t + 1)
          + (2 * (t : ℝ) + 1) * (q - ℓ) * (x * (q * x + ℓ * (1 - x)) ^ (2 * t))) x := by
    intro x _
    have hp : HasDerivAt (fun y => (q * y + ℓ * (1 - y)) ^ (2 * t + 1))
        ((2 * (t : ℝ) + 1) * (q * x + ℓ * (1 - x)) ^ (2 * t) * (q - ℓ)) x := by
      have h := (hVderiv x).pow (2 * t + 1)
      simp only [Nat.add_sub_cancel] at h
      rw [show (2 * (t : ℝ) + 1) * (q * x + ℓ * (1 - x)) ^ (2 * t) * (q - ℓ)
          = ((2 * t + 1 : ℕ) : ℝ) * (q * x + ℓ * (1 - x)) ^ (2 * t) * (q - ℓ) from by
            push_cast; ring]
      exact h
    have h2 := (hasDerivAt_id x).mul hp
    simp only [id_eq, one_mul] at h2
    rw [show (q * x + ℓ * (1 - x)) ^ (2 * t + 1)
          + (2 * (t : ℝ) + 1) * (q - ℓ) * (x * (q * x + ℓ * (1 - x)) ^ (2 * t))
        = (q * x + ℓ * (1 - x)) ^ (2 * t + 1)
          + x * ((2 * (t : ℝ) + 1) * (q * x + ℓ * (1 - x)) ^ (2 * t) * (q - ℓ)) from by ring]
    exact h2
  have hint : IntervalIntegrable
      (fun x => (q * x + ℓ * (1 - x)) ^ (2 * t + 1)
        + (2 * (t : ℝ) + 1) * (q - ℓ) * (x * (q * x + ℓ * (1 - x)) ^ (2 * t))) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hFderiv hint
  rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
      ((Continuous.intervalIntegrable (by fun_prop) 0 1)),
    intervalIntegral.integral_const_mul] at hftc
  have hRHS : (fun y => y * (q * y + ℓ * (1 - y)) ^ (2 * t + 1)) 1
      - (fun y => y * (q * y + ℓ * (1 - y)) ^ (2 * t + 1)) 0 = q ^ (2 * t + 1) := by
    simp
  rw [hRHS] at hftc
  linarith [hftc]

/-- **`thm:ibp`, the `r = 1` case.**  For odd `n = 2t+1` (so `m = 2t+3`), `q ∈ [0,1/2]`, `ℓ ≤ 1−q`,
and `ℓ ≥ q + 1/m`, the diagonal kernel `P̃_{m,1}(q,ℓ) ≥ 0`.  Via `gform_eq` (`r = 1`, weight `= 1`):
`I = (m/n)(J_V + J_W) − J_{xVⁿ⁻¹} ≥ (m/n)J_V − J_{xVⁿ⁻¹} ≥ (1/(n(ℓ−q)))J_V − J_{xVⁿ⁻¹} ≥ 0`. -/
theorem diagKernel_nonneg_ibp_r1 {t : ℕ} {q ℓ : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2)
    (hℓp : ℓ ≤ 1 - q) (hℓ : q + 1 / ((2 * t + 3 : ℕ) : ℝ) ≤ ℓ) :
    0 ≤ diagKernel (2 * t + 3) 1 q ℓ := by
  have hmp : (0 : ℝ) < 2 * (t : ℝ) + 3 := by positivity
  have hm3 : ((2 * t + 3 : ℕ) : ℝ) = 2 * (t : ℝ) + 3 := by push_cast; ring
  have hn : 1 ≤ (2 * t + 3) - 2 * 1 := by omega
  have hnR : (0 : ℝ) < 2 * (t : ℝ) + 1 := by positivity
  have hℓ' : q + 1 / (2 * (t : ℝ) + 3) ≤ ℓ := by rw [← hm3]; exact hℓ
  have h1m : (0 : ℝ) < 1 / (2 * (t : ℝ) + 3) := by positivity
  have hℓ0 : 0 < ℓ := by linarith [hℓ', h1m, hq0]
  have hℓq : q < ℓ := by linarith [hℓ', h1m]
  -- rewrite the two exponents `m-2*1` and `m-2*1-1`
  have he1 : (2 * t + 3) - 2 * 1 = 2 * t + 1 := by omega
  rw [gform_eq (by norm_num) hn]
  apply mul_nonneg (Cmr_pos (by norm_num) hn).le
  -- the Beta weight is `x^0(1-x)^0 = 1`; normalise casts and exponents
  simp only [show (1 : ℕ) - 1 = 0 from rfl, pow_zero, one_mul, he1, Nat.add_sub_cancel]
  push_cast
  -- name the three integrals
  set JV := ∫ x in (0:ℝ)..1, (q * x + ℓ * (1 - x)) ^ (2 * t + 1) with hJV
  set JW := ∫ x in (0:ℝ)..1, ((1 - q) * x + (-ℓ) * (1 - x)) ^ (2 * t + 1) with hJW
  set JX := ∫ x in (0:ℝ)..1, x * (q * x + ℓ * (1 - x)) ^ (2 * t) with hJX
  set MN := (2 * (t : ℝ) + 3) / (2 * (t : ℝ) + 1) with hMNdef
  have hMN : 0 < MN := by rw [hMNdef]; positivity
  have hsplit : (∫ x in (0:ℝ)..1,
        MN * ((q * x + ℓ * (1 - x)) ^ (2 * t + 1) + ((1 - q) * x + (-ℓ) * (1 - x)) ^ (2 * t + 1))
          - x * (q * x + ℓ * (1 - x)) ^ (2 * t))
      = MN * (JV + JW) - JX := by
    rw [intervalIntegral.integral_sub
        (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [hsplit]
  -- the three facts
  have hJVnn : 0 ≤ JV := by
    rw [hJV]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact pow_nonneg (by nlinarith [hx.1, hx.2, hℓ0.le]) _
  have hJWnn : 0 ≤ JW := jW_nonneg t q ℓ (by linarith)
  have hftc : JV + (2 * (t : ℝ) + 1) * (q - ℓ) * JX = q ^ (2 * t + 1) := jXV_ftc t q ℓ
  have hqn : (0 : ℝ) ≤ q ^ (2 * t + 1) := pow_nonneg hq0 _
  have hnℓq : 0 < (2 * (t : ℝ) + 1) * (ℓ - q) := mul_pos hnR (by linarith)
  have hJXeq : (2 * (t : ℝ) + 1) * (ℓ - q) * JX = JV - q ^ (2 * t + 1) := by nlinarith [hftc]
  have hJXle : JX ≤ JV / ((2 * (t : ℝ) + 1) * (ℓ - q)) := by
    rw [le_div_iff₀ hnℓq]; nlinarith [hJXeq, hqn]
  -- `m/n ≥ 1/(n(ℓ-q))`  ⟺  `m(ℓ-q) ≥ 1`
  have hMdom : 1 / ((2 * (t : ℝ) + 1) * (ℓ - q)) ≤ MN := by
    rw [hMNdef, div_le_div_iff₀ hnℓq hnR]
    have hmℓq : (1 : ℝ) ≤ (2 * (t : ℝ) + 3) * (ℓ - q) := by
      have h : (1 : ℝ) / (2 * (t : ℝ) + 3) ≤ ℓ - q := by linarith [hℓ']
      have := mul_le_mul_of_nonneg_left h hmp.le
      rwa [mul_one_div, div_self (ne_of_gt hmp)] at this
    nlinarith [hmℓq, hnR]
  -- assemble
  have hstep1 : JV / ((2 * (t : ℝ) + 1) * (ℓ - q)) ≤ MN * JV := by
    rw [div_eq_mul_one_div]
    calc JV * (1 / ((2 * (t : ℝ) + 1) * (ℓ - q)))
        ≤ JV * MN := mul_le_mul_of_nonneg_left hMdom hJVnn
      _ = MN * JV := by ring
  have hWterm : 0 ≤ MN * JW := mul_nonneg hMN.le hJWnn
  have hexpand : MN * (JV + JW) - JX = (MN * JV - JX) + MN * JW := by ring
  rw [hexpand]
  linarith [hWterm, le_trans hJXle hstep1]

/-- **`thm:r1` — the full `r = 1` diagonal positivity (all lengths).**  For every odd `m ≥ 3`,
`q ∈ [0,1/3]`, `ℓ ∈ [−1/2,1/2]`, `P̃_{m,1}(q,ℓ) ≥ 0`.  Assembles the case partition:
`ℓ ≤ 0` (`diagKernel_nonneg_le_zero`), `ℓ ≥ q+1/m` (`diagKernel_nonneg_ibp_r1`), and the middle band
`0 < ℓ < q+1/m` split by length — `m = 3` (`diagKernel_nonneg_two_r_ge`, `2r ≥ n`), `m = 5`
(`diagKernel_nonneg_r1_five`), and `m ≥ 7` (`diagKernel_nonneg_r1_of_integral` + `r1_integral_nonneg`). -/
theorem diagKernel_nonneg_r1 {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) {q ℓ : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 3) (hℓl : -(1 / 2) ≤ ℓ) (hℓu : ℓ ≤ 1 / 2) :
    0 ≤ diagKernel m 1 q ℓ := by
  obtain ⟨t, rfl⟩ : ∃ t, m = 2 * t + 3 := by
    obtain ⟨k, rfl⟩ := hm; exact ⟨k - 1, by omega⟩
  rcases le_or_gt ℓ 0 with hℓ0 | hℓ0
  · -- `ℓ ≤ 0`
    exact diagKernel_nonneg_le_zero (t := t) (by norm_num) (by omega) q ℓ (by linarith) hℓ0
  · rcases le_or_gt (q + 1 / ((2 * t + 3 : ℕ) : ℝ)) ℓ with hge | hlt
    · -- `ℓ ≥ q + 1/m`
      exact diagKernel_nonneg_ibp_r1 hq0 (by linarith) (by linarith) hge
    · -- `0 < ℓ < q + 1/m`
      rcases Nat.lt_or_ge t 2 with ht2 | ht2
      · interval_cases t
        · exact diagKernel_nonneg_two_r_ge (t := 0) (by norm_num) (by norm_num) (by norm_num) q ℓ
        · exact diagKernel_nonneg_r1_five q ℓ
      · exact diagKernel_nonneg_r1_of_integral (by omega) q ℓ hℓ0
          (r1_integral_nonneg ht2 hq0 hq hℓ0 hlt)

end OddCycleBound.HighDensity
