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

/-- Derivative of the linear form `V(y) = qy + ℓ(1-y)`: `V' = q − ℓ`. -/
lemma Vderiv (q ℓ x : ℝ) : HasDerivAt (fun y => q * y + ℓ * (1 - y)) (q - ℓ) x := by
  have h1 : HasDerivAt (fun y : ℝ => q * y) q x := by simpa using (hasDerivAt_id x).const_mul q
  have h2 : HasDerivAt (fun y : ℝ => ℓ * (1 - y)) (-ℓ) x := by
    simpa using (((hasDerivAt_id x).const_sub (1 : ℝ)).const_mul ℓ)
  have h3 : HasDerivAt (fun y : ℝ => q * y + ℓ * (1 - y)) (q + -ℓ) x := h1.add h2
  simpa only [sub_eq_add_neg] using h3

/-- Nonnegativity of a weighted `V`-power integral for `q,ℓ ≥ 0`: `V(x) = qx+ℓ(1-x) ≥ 0` on `[0,1]`. -/
lemma weighted_V_nonneg (a b n : ℕ) {q ℓ : ℝ} (hq0 : 0 ≤ q) (hℓ0 : 0 ≤ ℓ) :
    0 ≤ ∫ x in (0:ℝ)..1, x ^ a * (1 - x) ^ b * (q * x + ℓ * (1 - x)) ^ n := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  exact mul_nonneg (mul_nonneg (pow_nonneg hx.1 _) (pow_nonneg (by linarith [hx.2]) _))
    (pow_nonneg (by nlinarith [hx.1, hx.2]) _)

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

/-! ### General `r` (`r ≥ 2`) — `thm:ibp` -/

/-- **Beta symmetry with the general weight (`E[Wⁿ] ≥ 0`).**  For odd `n = 2t+1`, `r ≥ 1`, `ℓ ≤ 1−q`:
`∫₀¹ x^{r-1}(1-x)^{r-1}·W(x)ⁿ ≥ 0`.  Reflect `x ↦ 1-x` (the weight `x^{r-1}(1-x)^{r-1}` is symmetric);
`W(x)+W(1-x) = 1−q−ℓ ≥ 0`, so `W(x)ⁿ+W(1-x)ⁿ ≥ 0` and the common weight is nonnegative. -/
lemma weighted_W_nonneg (r t : ℕ) {q ℓ : ℝ} (hW : 0 ≤ 1 - q - ℓ) :
    0 ≤ ∫ x in (0:ℝ)..1, x ^ (r - 1) * (1 - x) ^ (r - 1)
        * ((1 - q) * x + (-ℓ) * (1 - x)) ^ (2 * t + 1) := by
  set f : ℝ → ℝ := fun y => y ^ (r - 1) * (1 - y) ^ (r - 1)
      * ((1 - q) * y + (-ℓ) * (1 - y)) ^ (2 * t + 1) with hf
  have hcont : Continuous f := by rw [hf]; fun_prop
  have hcont' : Continuous (fun x => f (1 - x)) := by rw [hf]; fun_prop
  have hrefl : (∫ x in (0:ℝ)..1, f (1 - x)) = ∫ x in (0:ℝ)..1, f x := by
    simpa using intervalIntegral.integral_comp_sub_left f (1 : ℝ)
  have hpt : 0 ≤ ∫ x in (0:ℝ)..1, (f x + f (1 - x)) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    rw [hf]
    simp only [show ∀ y : ℝ, (1 : ℝ) - (1 - y) = y from fun y => by ring]
    have hxw : 0 ≤ x ^ (r - 1) * (1 - x) ^ (r - 1) :=
      mul_nonneg (pow_nonneg hx.1 _) (pow_nonneg (by linarith [hx.2]) _)
    have hodd : 0 ≤ ((1 - q) * x + (-ℓ) * (1 - x)) ^ (2 * t + 1)
        + ((1 - q) * (1 - x) + (-ℓ) * x) ^ (2 * t + 1) := by
      apply odd_add_pow_nonneg ⟨t, by ring⟩
      have he : ((1 - q) * x + (-ℓ) * (1 - x)) + ((1 - q) * (1 - x) + (-ℓ) * x) = 1 - q - ℓ := by ring
      rw [he]; exact hW
    have hsum : x ^ (r - 1) * (1 - x) ^ (r - 1) * ((1 - q) * x + (-ℓ) * (1 - x)) ^ (2 * t + 1)
        + (1 - x) ^ (r - 1) * x ^ (r - 1) * ((1 - q) * (1 - x) + (-ℓ) * x) ^ (2 * t + 1)
        = x ^ (r - 1) * (1 - x) ^ (r - 1)
            * (((1 - q) * x + (-ℓ) * (1 - x)) ^ (2 * t + 1)
              + ((1 - q) * (1 - x) + (-ℓ) * x) ^ (2 * t + 1)) := by ring
    rw [hsum]
    exact mul_nonneg hxw hodd
  rw [intervalIntegral.integral_add (hcont.intervalIntegrable 0 1) (hcont'.intervalIntegrable 0 1),
    hrefl] at hpt
  linarith

/-- **The IBP identity (`r ≥ 2`).**  For `V(x) = qx+ℓ(1-x)`, `n = 2t+1`, the FTC applied to
`G(x) = xʳ(1-x)^{r-1}·Vⁿ` (whose boundary values vanish for `r ≥ 2`) gives
`n(ℓ−q)·∫₀¹ xʳ(1-x)^{r-1}Vⁿ⁻¹ = r·∫₀¹ x^{r-1}(1-x)^{r-1}Vⁿ − (r−1)·∫₀¹ xʳ(1-x)^{r-2}Vⁿ`.
Dropping the last (nonnegative) term yields the paper's `E[ΞVⁿ⁻¹] ≤ (r/(n(ℓ−q)))E[Vⁿ]`. -/
lemma jXV_ibp_identity {r t : ℕ} (hr : 2 ≤ r) (q ℓ : ℝ) :
    (2 * (t : ℝ) + 1) * (ℓ - q)
        * (∫ x in (0:ℝ)..1, x ^ r * (1 - x) ^ (r - 1) * (q * x + ℓ * (1 - x)) ^ (2 * t))
      = (r : ℝ) * (∫ x in (0:ℝ)..1,
            x ^ (r - 1) * (1 - x) ^ (r - 1) * (q * x + ℓ * (1 - x)) ^ (2 * t + 1))
        - ((r : ℝ) - 1) * (∫ x in (0:ℝ)..1,
            x ^ r * (1 - x) ^ (r - 2) * (q * x + ℓ * (1 - x)) ^ (2 * t + 1)) := by
  -- G(x) = xʳ (1-x)^{r-1} Vⁿ  and its product-rule derivative
  have hGderiv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun y => y ^ r * (1 - y) ^ (r - 1) * (q * y + ℓ * (1 - y)) ^ (2 * t + 1))
        (((r : ℝ) * x ^ (r - 1) * (1 - x) ^ (r - 1)
              + x ^ r * ((↑(r - 1) : ℝ) * (1 - x) ^ (r - 2) * (-1)))
            * (q * x + ℓ * (1 - x)) ^ (2 * t + 1)
          + x ^ r * (1 - x) ^ (r - 1)
              * ((↑(2 * t + 1) : ℝ) * (q * x + ℓ * (1 - x)) ^ (2 * t) * (q - ℓ))) x := by
    intro x _
    have ha : HasDerivAt (fun y : ℝ => y ^ r) ((r : ℝ) * x ^ (r - 1)) x := hasDerivAt_pow r x
    have hb : HasDerivAt (fun y : ℝ => (1 - y) ^ (r - 1))
        ((↑(r - 1) : ℝ) * (1 - x) ^ (r - 2) * (-1)) x := by
      have h := ((hasDerivAt_id x).const_sub (1 : ℝ)).pow (r - 1)
      simp only [show r - 1 - 1 = r - 2 from by omega] at h
      exact_mod_cast h
    have hc : HasDerivAt (fun y : ℝ => (q * y + ℓ * (1 - y)) ^ (2 * t + 1))
        ((↑(2 * t + 1) : ℝ) * (q * x + ℓ * (1 - x)) ^ (2 * t) * (q - ℓ)) x := by
      have h := (Vderiv q ℓ x).pow (2 * t + 1)
      simp only [Nat.add_sub_cancel] at h
      exact_mod_cast h
    exact (ha.mul hb).mul hc
  have hint : IntervalIntegrable
      (fun x => ((r : ℝ) * x ^ (r - 1) * (1 - x) ^ (r - 1)
            + x ^ r * ((↑(r - 1) : ℝ) * (1 - x) ^ (r - 2) * (-1)))
          * (q * x + ℓ * (1 - x)) ^ (2 * t + 1)
        + x ^ r * (1 - x) ^ (r - 1)
            * ((↑(2 * t + 1) : ℝ) * (q * x + ℓ * (1 - x)) ^ (2 * t) * (q - ℓ))) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hGderiv hint
  -- boundary values `G(1) = G(0) = 0`
  have hr1 : r - 1 ≠ 0 := by omega
  have hr0 : r ≠ 0 := by omega
  have hbdry : (fun y => y ^ r * (1 - y) ^ (r - 1) * (q * y + ℓ * (1 - y)) ^ (2 * t + 1)) (1 : ℝ)
      - (fun y => y ^ r * (1 - y) ^ (r - 1) * (q * y + ℓ * (1 - y)) ^ (2 * t + 1)) (0 : ℝ) = 0 := by
    simp [zero_pow hr0, zero_pow hr1]
  rw [hbdry] at hftc
  -- rewrite the messy integrand into the clean three-term sum, then split
  rw [show (fun x => ((r : ℝ) * x ^ (r - 1) * (1 - x) ^ (r - 1)
            + x ^ r * ((↑(r - 1) : ℝ) * (1 - x) ^ (r - 2) * (-1)))
          * (q * x + ℓ * (1 - x)) ^ (2 * t + 1)
        + x ^ r * (1 - x) ^ (r - 1)
            * ((↑(2 * t + 1) : ℝ) * (q * x + ℓ * (1 - x)) ^ (2 * t) * (q - ℓ)))
      = (fun x => ((r : ℝ) * (x ^ (r - 1) * (1 - x) ^ (r - 1) * (q * x + ℓ * (1 - x)) ^ (2 * t + 1))
            + (-((r : ℝ) - 1)) * (x ^ r * (1 - x) ^ (r - 2) * (q * x + ℓ * (1 - x)) ^ (2 * t + 1)))
          + (2 * (t : ℝ) + 1) * (q - ℓ)
              * (x ^ r * (1 - x) ^ (r - 1) * (q * x + ℓ * (1 - x)) ^ (2 * t))) from by
        funext x; push_cast [Nat.cast_sub (show 1 ≤ r from by omega)]; ring,
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1),
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hftc
  linarith [hftc]

/-- **`thm:ibp`, general `r ≥ 2`.**  For odd `n = 2t+1` (`m = n + 2r`), `q ∈ [0,1/2]`, `ℓ ≤ 1−q`,
and `ℓ ≥ q + r/m`, the diagonal kernel `P̃_{m,r}(q,ℓ) ≥ 0`.  Via `gform_eq`:
`I = (m/n)(J_V + J_W) − J_{xVⁿ⁻¹} ≥ 0`, using `J_W ≥ 0` (`weighted_W_nonneg`), `J_V ≥ 0`, and the IBP
bound `J_{xVⁿ⁻¹} ≤ (r/(n(ℓ−q)))J_V` (`jXV_ibp_identity` + `K ≥ 0`), with `ℓ ≥ q+r/m ⟹ m ≥ r/(ℓ−q)`. -/
theorem diagKernel_nonneg_ibp {m r t : ℕ} (hr : 2 ≤ r) (ht : m - 2 * r = 2 * t + 1)
    {q ℓ : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (hℓp : ℓ ≤ 1 - q)
    (hℓ : q + (r : ℝ) / m ≤ ℓ) :
    0 ≤ diagKernel m r q ℓ := by
  have hr0 : r ≠ 0 := by omega
  have hn1 : 1 ≤ m - 2 * r := by omega
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hNpos : (0 : ℝ) < 2 * (t : ℝ) + 1 := by positivity
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r from by omega)
  have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrm0 : (0 : ℝ) < (r : ℝ) / m := div_pos hrpos hmR
  have hℓq : q < ℓ := lt_of_lt_of_le (by linarith [hrm0]) hℓ
  have hd : (0 : ℝ) < ℓ - q := by linarith
  have hℓ0 : 0 < ℓ := lt_of_le_of_lt hq0 hℓq
  -- `m(ℓ−q) ≥ r`  from  `ℓ ≥ q + r/m`
  have hmr : (r : ℝ) ≤ (m : ℝ) * (ℓ - q) := by
    rw [mul_comm]; exact (div_le_iff₀ hmR).mp (by linarith [hℓ])
  rw [gform_eq hr0 hn1]
  apply mul_nonneg (Cmr_pos hr0 hn1).le
  rw [ht, Nat.add_sub_cancel]
  push_cast
  set MN := (m : ℝ) / (2 * (t : ℝ) + 1) with hMNdef
  have hMN : 0 < MN := by rw [hMNdef]; positivity
  set JV := ∫ x in (0:ℝ)..1,
    x ^ (r - 1) * (1 - x) ^ (r - 1) * (q * x + ℓ * (1 - x)) ^ (2 * t + 1) with hJV
  set JW := ∫ x in (0:ℝ)..1,
    x ^ (r - 1) * (1 - x) ^ (r - 1) * ((1 - q) * x + (-ℓ) * (1 - x)) ^ (2 * t + 1) with hJW
  set JX := ∫ x in (0:ℝ)..1, x ^ r * (1 - x) ^ (r - 1) * (q * x + ℓ * (1 - x)) ^ (2 * t) with hJX
  set K := ∫ x in (0:ℝ)..1, x ^ r * (1 - x) ^ (r - 2) * (q * x + ℓ * (1 - x)) ^ (2 * t + 1) with hK
  -- split the gform integral into `MN·JV + MN·JW − JX`
  have hsplit : (∫ x in (0:ℝ)..1, x ^ (r - 1) * (1 - x) ^ (r - 1)
        * (MN * ((q * x + ℓ * (1 - x)) ^ (2 * t + 1)
              + ((1 - q) * x + (-ℓ) * (1 - x)) ^ (2 * t + 1))
            - x * (q * x + ℓ * (1 - x)) ^ (2 * t)))
      = MN * JV + MN * JW - JX := by
    rw [show (fun x => x ^ (r - 1) * (1 - x) ^ (r - 1)
          * (MN * ((q * x + ℓ * (1 - x)) ^ (2 * t + 1)
                + ((1 - q) * x + (-ℓ) * (1 - x)) ^ (2 * t + 1))
              - x * (q * x + ℓ * (1 - x)) ^ (2 * t)))
        = (fun x => (MN * (x ^ (r - 1) * (1 - x) ^ (r - 1) * (q * x + ℓ * (1 - x)) ^ (2 * t + 1))
              + MN * (x ^ (r - 1) * (1 - x) ^ (r - 1) * ((1 - q) * x + (-ℓ) * (1 - x)) ^ (2 * t + 1)))
            - x ^ r * (1 - x) ^ (r - 1) * (q * x + ℓ * (1 - x)) ^ (2 * t)) from by
          funext x
          rw [show x ^ r = x ^ (r - 1) * x from by rw [← pow_succ, Nat.sub_add_cancel (by omega)]]
          ring,
      intervalIntegral.integral_sub
        (Continuous.intervalIntegrable (by fun_prop) 0 1)
        (Continuous.intervalIntegrable (by fun_prop) 0 1),
      intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 1)
        (Continuous.intervalIntegrable (by fun_prop) 0 1),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hsplit]
  -- the facts
  have hJVnn : 0 ≤ JV := weighted_V_nonneg (r - 1) (r - 1) (2 * t + 1) hq0 hℓ0.le
  have hJWnn : 0 ≤ JW := weighted_W_nonneg r t (by linarith)
  have hKnn : 0 ≤ K := weighted_V_nonneg r (r - 2) (2 * t + 1) hq0 hℓ0.le
  have hid : (2 * (t : ℝ) + 1) * (ℓ - q) * JX = (r : ℝ) * JV - ((r : ℝ) - 1) * K :=
    jXV_ibp_identity hr q ℓ
  -- IBP bound: `n(ℓ−q)·JX ≤ r·JV`, hence `N·JX ≤ M·JV`
  have hXbound : (2 * (t : ℝ) + 1) * (ℓ - q) * JX ≤ (r : ℝ) * JV := by
    have : 0 ≤ ((r : ℝ) - 1) * K := mul_nonneg (by linarith [hr2R]) hKnn
    linarith [hid]
  have hND : (2 * (t : ℝ) + 1) * JX ≤ (m : ℝ) * JV := by
    have h2 : (r : ℝ) * JV ≤ (m : ℝ) * (ℓ - q) * JV := by nlinarith [hmr, hJVnn]
    have h3 : (2 * (t : ℝ) + 1) * (ℓ - q) * JX ≤ (m : ℝ) * (ℓ - q) * JV := le_trans hXbound h2
    have h5 : 0 ≤ ((m : ℝ) * JV - (2 * (t : ℝ) + 1) * JX) * (ℓ - q) := by nlinarith [h3]
    nlinarith [h5, hd]
  have hfin : JX ≤ MN * JV := by
    rw [hMNdef, div_mul_eq_mul_div, le_div_iff₀ hNpos]
    linarith [hND]
  have hWterm : 0 ≤ MN * JW := mul_nonneg hMN.le hJWnn
  linarith [hfin, hWterm]

end OddCycleBound.HighDensity
