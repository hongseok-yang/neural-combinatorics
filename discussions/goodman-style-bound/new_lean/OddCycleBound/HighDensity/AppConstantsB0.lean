/-
# High-density theorem — `app:constants`, the `rpow` factor bound `B₀(θ) ≥ 201/200` (`eq:constant-A`)

`B₀(θ) = (7/6)^{1-2θ}·(8-24θ)^{-θ}·(1/2+θ)/(5/12+θ)`.  Unlike `B₁`, `B₀` is **near-tight** (its minimum
on `[0,1/6]` is exactly `201/200 = 4/∛63`, at `θ = 1/6`), so the subdivision method fails; we follow the
paper's derivative route.  Writing `g = log B₀` (a sum of elementary logs, via `Real.log_rpow`/`log_div`),
we show `g` is antitone on `[0,1/6]` — its derivative is `≤ 0` because the log lower bound
`2(x-1)/(x+1) ≤ log x` (`log_lower`, proved by FTC) reduces `g' ≤ 0` to a rational inequality (`Rbound`,
a cleared quartic closed by `nlinarith`).  Hence `B₀(θ) ≥ B₀(1/6) = 4/∛63 ≥ 201/200` (`B0_endpoint`,
`800³ ≥ 201³·63`, verified by raising to the 6th power).
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory intervalIntegral

namespace OddCycleBound.HighDensity

/-- **Log lower bound** `2(x-1)/(x+1) ≤ log x` for `x ≥ 1`.  FTC on `f(x) = log x − 2(x-1)/(x+1)`,
`f(1)=0`, `f'(x) = (x-1)²/(x(x+1)²) ≥ 0`. -/
lemma log_lower {x : ℝ} (hx : 1 ≤ x) : 2 * (x - 1) / (x + 1) ≤ Real.log x := by
  have hf : ∀ t ∈ Set.uIcc (1:ℝ) x,
      HasDerivAt (fun s => Real.log s - 2 * (s - 1) / (s + 1)) ((t - 1) ^ 2 / (t * (t + 1) ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have ht1 : 0 < t + 1 := by linarith
    have hlog := Real.hasDerivAt_log (ne_of_gt ht0)
    have hn : HasDerivAt (fun s : ℝ => 2 * (s - 1)) 2 t := by
      have := ((hasDerivAt_id t).sub_const 1).const_mul 2; simpa using this
    have hd : HasDerivAt (fun s : ℝ => s + 1) 1 t := (hasDerivAt_id t).add_const 1
    have hrat := hn.div hd (ne_of_gt ht1)
    rw [show (2 * (t + 1) - 2 * (t - 1) * 1) / (t + 1) ^ 2 = 4 / (t + 1) ^ 2 from by ring] at hrat
    have := hlog.sub hrat
    rw [show t⁻¹ - 4 / (t + 1) ^ 2 = (t - 1) ^ 2 / (t * (t + 1) ^ 2) from by field_simp; ring] at this
    exact this
  have hint : IntervalIntegrable (fun t => (t - 1) ^ 2 / (t * (t + 1) ^ 2)) volume 1 x := by
    apply ContinuousOn.intervalIntegrable; rw [Set.uIcc_of_le hx]
    refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => ?_)
    have ht0 : 0 < t := by linarith [ht.1]
    positivity
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hf hint
  have hnn : 0 ≤ ∫ t in (1:ℝ)..x, (t - 1) ^ 2 / (t * (t + 1) ^ 2) := by
    apply intervalIntegral.integral_nonneg hx
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    positivity
  rw [Real.log_one] at hftc
  linarith [hftc, hnn]

/-- The cleared rational bound behind `g' ≤ 0` (after `log_lower` is applied): a quartic ≤ 0 on
`[0,1/6]`. -/
lemma Rbound {θ : ℝ} (h0 : 0 ≤ θ) (h16 : θ ≤ 1 / 6) :
    -4 / 13 - 2 * (7 - 24 * θ) / (9 - 24 * θ) + 24 * θ / (8 - 24 * θ) + 1 / (1 / 2 + θ)
        - 1 / (5 / 12 + θ) ≤ 0 := by
  have hd1 : (0:ℝ) < 9 - 24 * θ := by linarith
  have hd2 : (0:ℝ) < 8 - 24 * θ := by linarith
  have hd3 : (0:ℝ) < 1 / 2 + θ := by linarith
  have hd4 : (0:ℝ) < 5 / 12 + θ := by linarith
  rw [show (-4 / 13 - 2 * (7 - 24 * θ) / (9 - 24 * θ) + 24 * θ / (8 - 24 * θ) + 1 / (1 / 2 + θ)
        - 1 / (5 / 12 + θ))
      = (-4 * (9 - 24 * θ) * (8 - 24 * θ) * (1 / 2 + θ) * (5 / 12 + θ)
          - 2 * 13 * (7 - 24 * θ) * (8 - 24 * θ) * (1 / 2 + θ) * (5 / 12 + θ)
          + 24 * θ * 13 * (9 - 24 * θ) * (1 / 2 + θ) * (5 / 12 + θ)
          + 13 * (9 - 24 * θ) * (8 - 24 * θ) * (5 / 12 + θ)
          - 13 * (9 - 24 * θ) * (8 - 24 * θ) * (1 / 2 + θ))
        / (13 * (9 - 24 * θ) * (8 - 24 * θ) * (1 / 2 + θ) * (5 / 12 + θ)) from by field_simp]
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith [h0, h16, mul_pos hd3 hd4, mul_pos hd1 hd2, mul_nonneg h0 h0,
      mul_nonneg (mul_nonneg h0 h0) h0, mul_pos (mul_pos hd1 hd2) (mul_pos hd3 hd4)]
  · exact le_of_lt (by positivity)

/-- `g = log B₀`, as a sum of elementary logs. -/
noncomputable def g (θ : ℝ) : ℝ :=
  (1 - 2 * θ) * Real.log (7 / 6) - θ * Real.log (8 - 24 * θ) + Real.log (1 / 2 + θ)
    - Real.log (5 / 12 + θ)

/-- `g' θ` on the interior `(0,1/6)`. -/
lemma gderiv {θ : ℝ} (h0 : 0 < θ) (h16 : θ < 1 / 6) :
    HasDerivAt g (-2 * Real.log (7 / 6) - Real.log (8 - 24 * θ) + 24 * θ / (8 - 24 * θ)
      + 1 / (1 / 2 + θ) - 1 / (5 / 12 + θ)) θ := by
  have hd2 : (0:ℝ) < 8 - 24 * θ := by linarith
  have hd3 : (0:ℝ) < 1 / 2 + θ := by linarith
  have hd4 : (0:ℝ) < 5 / 12 + θ := by linarith
  have t1 : HasDerivAt (fun θ => (1 - 2 * θ) * Real.log (7 / 6)) (-2 * Real.log (7 / 6)) θ := by
    have := (((hasDerivAt_id θ).const_mul 2).const_sub 1).mul_const (Real.log (7 / 6)); simpa using this
  have hlog8 : HasDerivAt (fun θ => Real.log (8 - 24 * θ)) (-24 / (8 - 24 * θ)) θ := by
    have := (((hasDerivAt_id θ).const_mul 24).const_sub 8).log (ne_of_gt hd2); simpa using this
  have t2 : HasDerivAt (fun θ => θ * Real.log (8 - 24 * θ))
      (Real.log (8 - 24 * θ) - 24 * θ / (8 - 24 * θ)) θ := by
    have h := (hasDerivAt_id θ).mul hlog8
    simp only [id_eq] at h
    rw [show (1:ℝ) * Real.log (8 - 24 * θ) + θ * (-24 / (8 - 24 * θ))
        = Real.log (8 - 24 * θ) - 24 * θ / (8 - 24 * θ) from by ring] at h
    exact h
  have t3 : HasDerivAt (fun θ => Real.log (1 / 2 + θ)) (1 / (1 / 2 + θ)) θ := by
    have := ((hasDerivAt_id θ).const_add (1 / 2)).log (ne_of_gt hd3); simpa using this
  have t4 : HasDerivAt (fun θ => Real.log (5 / 12 + θ)) (1 / (5 / 12 + θ)) θ := by
    have := ((hasDerivAt_id θ).const_add (5 / 12)).log (ne_of_gt hd4); simpa using this
  rw [show (-2 * Real.log (7 / 6) - Real.log (8 - 24 * θ) + 24 * θ / (8 - 24 * θ) + 1 / (1 / 2 + θ)
        - 1 / (5 / 12 + θ))
      = (-2 * Real.log (7 / 6) - (Real.log (8 - 24 * θ) - 24 * θ / (8 - 24 * θ)) + 1 / (1 / 2 + θ))
        - 1 / (5 / 12 + θ) from by ring]
  exact ((t1.sub t2).add t3).sub t4

/-- `g' θ ≤ 0` on `[0,1/6]` (via `log_lower` on `8-24θ` and `7/6`, then `Rbound`). -/
lemma gderiv_nonpos {θ : ℝ} (h0 : 0 ≤ θ) (h16 : θ ≤ 1 / 6) :
    -2 * Real.log (7 / 6) - Real.log (8 - 24 * θ) + 24 * θ / (8 - 24 * θ) + 1 / (1 / 2 + θ)
        - 1 / (5 / 12 + θ) ≤ 0 := by
  have hlog76 : (2:ℝ) / 13 ≤ Real.log (7 / 6) := by
    have := log_lower (show (1:ℝ) ≤ 7 / 6 by norm_num)
    rwa [show 2 * ((7 / 6:ℝ) - 1) / ((7 / 6) + 1) = 2 / 13 from by norm_num] at this
  have hlog8 : 2 * (7 - 24 * θ) / (9 - 24 * θ) ≤ Real.log (8 - 24 * θ) := by
    have := log_lower (show (1:ℝ) ≤ 8 - 24 * θ by linarith)
    rwa [show 2 * ((8 - 24 * θ) - 1) / ((8 - 24 * θ) + 1) = 2 * (7 - 24 * θ) / (9 - 24 * θ)
      from by ring] at this
  linarith [hlog76, hlog8, Rbound h0 h16]

/-- `g` is antitone on `[0,1/6]`. -/
lemma g_antitone : AntitoneOn g (Set.Icc (0:ℝ) (1 / 6)) := by
  have h8 : ∀ x ∈ Set.Icc (0:ℝ) (1 / 6), (8 - 24 * x) ≠ 0 :=
    fun x hx => ne_of_gt (by have := hx.2; linarith)
  have h3 : ∀ x ∈ Set.Icc (0:ℝ) (1 / 6), (1 / 2 + x) ≠ 0 :=
    fun x hx => ne_of_gt (by have := hx.1; linarith)
  have h4 : ∀ x ∈ Set.Icc (0:ℝ) (1 / 6), (5 / 12 + x) ≠ 0 :=
    fun x hx => ne_of_gt (by have := hx.1; linarith)
  have hcont : ContinuousOn g (Set.Icc (0:ℝ) (1 / 6)) := by
    have cl8 : ContinuousOn (fun x => Real.log (8 - 24 * x)) (Set.Icc (0:ℝ) (1 / 6)) :=
      (by fun_prop : ContinuousOn (fun x:ℝ => 8 - 24 * x) _).log h8
    have cl3 : ContinuousOn (fun x => Real.log (1 / 2 + x)) (Set.Icc (0:ℝ) (1 / 6)) :=
      (by fun_prop : ContinuousOn (fun x:ℝ => 1 / 2 + x) _).log h3
    have cl4 : ContinuousOn (fun x => Real.log (5 / 12 + x)) (Set.Icc (0:ℝ) (1 / 6)) :=
      (by fun_prop : ContinuousOn (fun x:ℝ => 5 / 12 + x) _).log h4
    unfold g
    exact ((((by fun_prop : ContinuousOn (fun x:ℝ => (1 - 2 * x) * Real.log (7 / 6)) _)).sub
      ((by fun_prop : ContinuousOn (fun x:ℝ => x) _).mul cl8)).add cl3).sub cl4
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 (1 / 6)) hcont
  · intro x hx
    rw [interior_Icc, Set.mem_Ioo] at hx
    exact (gderiv hx.1 hx.2).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc, Set.mem_Ioo] at hx
    rw [(gderiv hx.1 hx.2).deriv]
    exact gderiv_nonpos hx.1.le hx.2.le

/-- `B₀(θ) = (7/6)^{1-2θ}·(8-24θ)^{-θ}·(1/2+θ)/(5/12+θ)`. -/
noncomputable def B0 (θ : ℝ) : ℝ :=
  (7 / 6) ^ (1 - 2 * θ) * (8 - 24 * θ) ^ (-θ) * ((1 / 2 + θ) / (5 / 12 + θ))

/-- `log B₀ = g` (via `Real.log_rpow`/`log_mul`/`log_div`). -/
lemma log_B0_eq {θ : ℝ} (h0 : 0 ≤ θ) (h16 : θ ≤ 1 / 6) : Real.log (B0 θ) = g θ := by
  have hd2 : (0:ℝ) < 8 - 24 * θ := by linarith
  have hd3 : (0:ℝ) < 1 / 2 + θ := by linarith
  have hd4 : (0:ℝ) < 5 / 12 + θ := by linarith
  have hA : (0:ℝ) < (7 / 6:ℝ) ^ (1 - 2 * θ) := Real.rpow_pos_of_pos (by norm_num) _
  have hB : (0:ℝ) < (8 - 24 * θ) ^ (-θ) := Real.rpow_pos_of_pos hd2 _
  have hC : (0:ℝ) < (1 / 2 + θ) / (5 / 12 + θ) := div_pos hd3 hd4
  unfold B0 g
  rw [Real.log_mul (mul_pos hA hB).ne' hC.ne', Real.log_mul hA.ne' hB.ne',
      Real.log_rpow (by norm_num), Real.log_rpow hd2, Real.log_div (ne_of_gt hd3) (ne_of_gt hd4)]
  ring

/-- `B₀(1/6) = 4/∛63 ≥ 201/200` (raise to the 6th power: `(201/200)^6 ≤ (7/6)^4·(1/4)·(8/7)^6`). -/
lemma B0_endpoint : (201:ℝ) / 200 ≤ B0 (1 / 6) := by
  unfold B0
  have hA : (0:ℝ) < (7 / 6:ℝ) ^ ((1:ℝ) - 2 * (1 / 6)) := Real.rpow_pos_of_pos (by norm_num) _
  have hB : (0:ℝ) < (8 - 24 * (1 / 6):ℝ) ^ (-(1 / 6:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hXpos : (0:ℝ) < (7 / 6:ℝ) ^ ((1:ℝ) - 2 * (1 / 6)) * (8 - 24 * (1 / 6)) ^ (-(1 / 6:ℝ))
      * ((1 / 2 + 1 / 6) / (5 / 12 + 1 / 6)) :=
    mul_pos (mul_pos hA hB) (by norm_num)
  apply le_of_pow_le_pow_left₀ (n := 6) (by norm_num) hXpos.le
  rw [mul_pow, mul_pow, ← Real.rpow_natCast ((7 / 6:ℝ) ^ ((1:ℝ) - 2 * (1 / 6))) 6,
      ← Real.rpow_natCast ((8 - 24 * (1 / 6):ℝ) ^ (-(1 / 6:ℝ))) 6, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num),
      show ((1:ℝ) - 2 * (1 / 6)) * ((6:ℕ):ℝ) = ((4:ℕ):ℝ) from by norm_num,
      show (-(1 / 6:ℝ)) * ((6:ℕ):ℝ) = ((-1:ℤ):ℝ) from by norm_num,
      Real.rpow_natCast, Real.rpow_intCast]
  norm_num

/-- **`eq:constant-A` factor bound `B₀(θ) ≥ 201/200`** for `0 ≤ θ ≤ 1/6` (`g` antitone + endpoint). -/
lemma B0_ge {θ : ℝ} (h0 : 0 ≤ θ) (h16 : θ ≤ 1 / 6) : (201:ℝ) / 200 ≤ B0 θ := by
  have hd2 : (0:ℝ) < 8 - 24 * θ := by linarith
  have hd3 : (0:ℝ) < 1 / 2 + θ := by linarith
  have hd4 : (0:ℝ) < 5 / 12 + θ := by linarith
  have hB0θ : 0 < B0 θ := by
    unfold B0
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos hd2 _)) (div_pos hd3 hd4)
  have hB016 : 0 < B0 (1 / 6) := lt_of_lt_of_le (by norm_num) B0_endpoint
  have hge : g (1 / 6) ≤ g θ := g_antitone ⟨h0, h16⟩ ⟨by norm_num, by norm_num⟩ h16
  have hmono : B0 (1 / 6) ≤ B0 θ := by
    rw [← Real.exp_log hB016, ← Real.exp_log hB0θ, log_B0_eq (by norm_num) (by norm_num),
        log_B0_eq h0 h16]
    exact Real.exp_le_exp.mpr hge
  linarith [hmono, B0_endpoint]

end OddCycleBound.HighDensity
