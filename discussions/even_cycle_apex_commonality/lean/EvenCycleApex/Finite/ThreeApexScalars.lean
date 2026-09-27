import EvenCycleApex.Finite.ThreeApexMoments

/-!
# Scalar comparisons for three apices

Blueprint `lem:codegree-moments` (`Z_s = E C_σ^s`, `Z₃ ≥ R₄^{3/2}`), `cor:reference-mean` (the
three-apex chain `E(Q♯₃)⁴ ≥ 𝒥₀ ≥ Z₃ ≥ R₄^{3/2} ≥ R₄ ≥ 1`), `lem:amplification`
(`R₄^{3/2} ≥ R₄ + 4br`), `lem:auxiliary-D` (`𝒟 = 2𝒥₀ − R₄ − 4p₃ − 1 ≥ 0`) and
`lem:majority-bounds` (`|𝒫| ≤ 2`, `E 𝒫 = 3m − τ`).
-/

open Finset

namespace EvenCycleApex

/-! ### `lem:amplification`, the real inequality -/

/-- `z³ − z² ≥ z'³ − z'²` for `z ≥ z' ≥ 1`. -/
private lemma cube_sub_sq_mono {z z' : ℝ} (h1 : 1 ≤ z') (h : z' ≤ z) :
    z' ^ 3 - z' ^ 2 ≤ z ^ 3 - z ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 h)
    (sub_nonneg.2 (h1.trans h)), mul_nonneg (sub_nonneg.2 h) (sq_nonneg z')]

/-- **Fourth-cycle amplification** (real form).  For `a, b, r ≥ 0` and `R = 1 + 2a + 4b + r⁴`,
`R + 4br ≤ √R³`. -/
theorem amplification_real {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r) :
    (1 + 2 * a + 4 * b + r ^ 4) + 4 * b * r ≤ Real.sqrt (1 + 2 * a + 4 * b + r ^ 4) ^ 3 := by
  set R := 1 + 2 * a + 4 * b + r ^ 4 with hR
  have hR1 : 1 ≤ R := by rw [hR]; nlinarith [pow_nonneg hr 4]
  set z := Real.sqrt R with hz
  have hz1 : 1 ≤ z := by rw [hz]; exact Real.one_le_sqrt.mpr hR1
  have hzR : z ^ 2 = R := Real.sq_sqrt (by linarith)
  rcases le_or_gt r (1 / 2) with hr2 | hr2
  · -- `z³ − z² = z²(z − 1) ≥ (z² − 1)/2 = (R − 1)/2 ≥ 2b ≥ 4br`
    have hz0 : 0 ≤ (z - 1) * (z - 1) * (2 * z + 1) :=
      mul_nonneg (mul_nonneg (sub_nonneg.2 hz1) (sub_nonneg.2 hz1)) (by linarith)
    have hkey : (z ^ 2 - 1) / 2 ≤ z ^ 3 - z ^ 2 := by nlinarith [hz0]
    have hb2 : 4 * b * r ≤ 2 * b := by nlinarith
    have hR' : 4 * b ≤ R - 1 := by rw [hR]; nlinarith [pow_nonneg hr 4]
    nlinarith [hkey, hb2, hR', hzR]
  · -- reduce to `R' = 1 + 4b + r⁴`, then `x³ − (1+r)x² + r + r⁵ ≥ 0`
    set R' := 1 + 4 * b + r ^ 4 with hR'
    have hR'1 : 1 ≤ R' := by rw [hR']; nlinarith [pow_nonneg hr 4]
    set x := Real.sqrt R' with hx
    have hx1 : 1 ≤ x := by rw [hx]; exact Real.one_le_sqrt.mpr hR'1
    have hxR : x ^ 2 = R' := Real.sq_sqrt (by linarith)
    have hxz : x ≤ z := by
      rw [hx, hz]
      exact Real.sqrt_le_sqrt (by rw [hR, hR']; linarith)
    have hmono := cube_sub_sq_mono hx1 hxz
    -- `x³ − Ax² ≥ −4A³/27` with `A = 1 + r`, and `r + r⁵ ≥ 4(1 + r)³/27` for `r ≥ 1/2`
    have hA : (x - 2 * (1 + r) / 3) ^ 2 * (x + (1 + r) / 3) ≥ 0 := by positivity
    have hpoly : 27 * r ^ 5 - 4 * r ^ 3 - 12 * r ^ 2 + 15 * r - 4 ≥ 0 := by
      set t := r - 1 / 2 with ht
      have ht0 : 0 ≤ t := by linarith
      have : 27 * r ^ 5 - 4 * r ^ 3 - 12 * r ^ 2 + 15 * r - 4
          = 27 * t ^ 5 + 135 / 2 * t ^ 4 + 127 / 2 * t ^ 3 + 63 / 4 * t ^ 2 + 135 / 16 * t + 27 / 32 := by
        rw [ht]; ring
      rw [this]
      positivity
    have h4br : 4 * b * r = r * (x ^ 2 - 1 - r ^ 4) := by rw [hxR, hR']; ring
    nlinarith

namespace FiniteKernel

variable {d : ℕ} (K : FiniteKernel d)

/-! ### Codegree moments -/

/-- The codegree `C_σ(x, y) = E_t S_σ(t, x) S_σ(t, y)`. -/
def codeg (b : Bool) (x y : Fin d) : ℝ := ∑ t, K.w t * K.S (colour b) t x * K.S (colour b) t y

lemma codeg_nonneg (b : Bool) (x y : Fin d) : 0 ≤ K.codeg b x y :=
  sum_nonneg fun t _ => mul_nonneg (mul_nonneg (K.w_nonneg t) (K.S_nonneg (colour_cases b) t x))
    (K.S_nonneg (colour_cases b) t y)

/-- **`Z_s = E C_σ^s`** over a uniform colour and two host coordinates. -/
theorem Z_eq_codeg (s : ℕ) :
    K.Z s = ∑ b : Bool, ∑ x, ∑ y, (1 / 2 * (K.w x * K.w y)) * K.codeg b x y ^ s := by
  rw [Z, E, Fintype.sum_prod_type]
  refine sum_congr rfl fun b _ => ?_
  have hsq : ∀ z : Fin s → Fin d, K.condD (b, z) ^ 2 = ∑ x, ∑ y, K.w x * K.w y *
      ∏ j, (K.S (colour b) (z j) x * K.S (colour b) (z j) y) := by
    intro z
    simp only [condD, condH]
    rw [sq, sum_mul_sum]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    rw [prod_mul_distrib]
    ring
  have hpow : ∀ x y : Fin d, K.codeg b x y ^ s
      = ∑ z : Fin s → Fin d, (∏ j, K.w (z j)) *
          ∏ j, (K.S (colour b) (z j) x * K.S (colour b) (z j) y) := by
    intro x y
    rw [codeg, ← Fin.prod_const, Fintype.prod_sum]
    refine sum_congr rfl fun z _ => ?_
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun j _ => by ring
  simp only [prob, hsq, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [hpow, mul_sum]
  exact sum_congr rfl fun z _ => by ring

/-- The weights `½ w(x) w(y)` of the codegree sums add up to one. -/
private lemma sum_codeg_weights :
    ∑ _b : Bool, ∑ x, ∑ y, (1 / 2 * (K.w x * K.w y) : ℝ) = 1 := by
  simp only [← mul_sum, ← sum_mul, K.w_sum, Fintype.sum_bool]
  norm_num

/-- **`Z₃ ≥ R₄^{3/2}`** (Jensen at exponent `3/2` for `C_σ ≥ 0`, with `Z₂ = R₄`). -/
theorem Z_three_ge : K.R 4 ^ ((3 : ℝ) / 2) ≤ K.Z 3 := by
  have hJ := moment_monotone (univ : Finset (Bool × Fin d × Fin d))
    (fun i => 1 / 2 * (K.w i.2.1 * K.w i.2.2)) (fun i => K.codeg i.1 i.2.1 i.2.2)
    (fun i _ => by have := K.w_nonneg i.2.1; have := K.w_nonneg i.2.2; positivity)
    (by simp only [Fintype.sum_prod_type]; exact K.sum_codeg_weights)
    (fun i _ => K.codeg_nonneg _ _ _) (p := 2) (q := 3) (by norm_num) (by norm_num)
  have h2 : ∑ i : Bool × Fin d × Fin d,
      1 / 2 * (K.w i.2.1 * K.w i.2.2) * K.codeg i.1 i.2.1 i.2.2 ^ (2 : ℝ) = K.Z 2 := by
    rw [Z_eq_codeg, Fintype.sum_prod_type]
    refine sum_congr rfl fun b _ => ?_
    rw [Fintype.sum_prod_type]
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by rw [Real.rpow_two]
  have h3 : ∑ i : Bool × Fin d × Fin d,
      1 / 2 * (K.w i.2.1 * K.w i.2.2) * K.codeg i.1 i.2.1 i.2.2 ^ (3 : ℝ) = K.Z 3 := by
    rw [Z_eq_codeg, Fintype.sum_prod_type]
    refine sum_congr rfl fun b _ => ?_
    rw [Fintype.sum_prod_type]
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h2, h3, K.Z_two] at hJ
  exact hJ

/-! ### `cor:reference-mean`, three apices -/

lemma E_sub (F G : Sample d 3 → ℝ) : K.E (fun ω => F ω - G ω) = K.E F - K.E G := by
  simp only [E, mul_sub, sum_sub_distrib]

lemma E_const_mul (c : ℝ) (F : Sample d 3 → ℝ) : K.E (fun ω => c * F ω) = c * K.E F := by
  simp only [E, mul_sum]
  exact sum_congr rfl fun ω _ => by ring

lemma J0_eq_two_EPi_sub_Z : K.J0 = 2 * K.EPi 3 - K.Z 3 := by
  rw [J0, EPi, Z, ← K.E_const_mul, ← K.E_sub]
  rfl

/-- **`cor:reference-mean`** (three apices): `E(Q♯₃)⁴ ≥ 𝒥₀ ≥ Z₃ ≥ R₄^{3/2} ≥ R₄ ≥ 1`. -/
theorem reference_mean_bounds :
    1 ≤ K.R 4 ∧ K.R 4 ≤ K.R 4 ^ ((3 : ℝ) / 2) ∧ K.R 4 ^ ((3 : ℝ) / 2) ≤ K.Z 3 ∧ K.Z 3 ≤ K.J0 ∧
      K.J0 ≤ K.E (fun ω : Sample d 3 => K.condQs ω ^ 4) := by
  have hR := K.one_le_R_four
  refine ⟨hR, ?_, K.Z_three_ge, ?_, ?_⟩
  · calc K.R 4 = K.R 4 ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ K.R 4 ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hR (by norm_num)
  · rw [J0_eq_two_EPi_sub_Z]
    linarith [K.EPi_three_ge_Z_three]
  · exact K.E_mono fun ω => K.condQs_four_ge ω

/-! ### `lem:amplification` and `lem:auxiliary-D` -/

lemma r_pow_four : K.r ^ 4 = K.c := by
  rw [r, ← Real.rpow_natCast, ← Real.rpow_mul K.c_nonneg]
  norm_num

/-- **`lem:amplification`.**  `R₄^{3/2} ≥ R₄ + 4br`. -/
theorem fourth_cycle_amplification : K.R 4 + 4 * K.b * K.r ≤ K.R 4 ^ ((3 : ℝ) / 2) := by
  have h := amplification_real K.a_nonneg K.b_nonneg K.r_nonneg
  rw [K.r_pow_four, ← K.R_four] at h
  have hR0 : 0 ≤ K.R 4 := by linarith [K.one_le_R_four]
  rwa [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hR0,
    show (1 / 2 : ℝ) * ((3 : ℕ) : ℝ) = 3 / 2 by norm_num] at h

/-- The auxiliary scalar `𝒟 = 2𝒥₀ − R₄ − 4p₃ − 1`. -/
noncomputable def auxD : ℝ := 2 * K.J0 - K.R 4 - 4 * K.p3 - 1

/-- **`lem:auxiliary-D`.**  `𝒟 ≥ 0`. -/
theorem auxiliary_scalar_nonnegative : 0 ≤ K.auxD := by
  obtain ⟨hR1, hR32, hZ, hJ, -⟩ := K.reference_mean_bounds
  obtain ⟨-, -, hneg⟩ := K.fourth_colour_traces
  have hr : (1 + -1 * K.m) ^ 4 ≤ K.rσ4 (-1) := K.colour_cycle_ge (by decide) (by norm_num) (-1)
  have hpoly : 1 ≤ (1 - K.m) ^ 4 + 4 * K.m := by
    nlinarith [sq_nonneg (K.m * (K.m - 2)), sq_nonneg K.m]
  rw [auxD]
  nlinarith

/-! ### `lem:majority-bounds` -/

/-- `|𝒫| ≤ 2` pointwise. -/
theorem abs_majority_le (z : Fin 3 → Fin d) : |K.majority z| ≤ 2 := by
  have h1 := abs_le.mp (K.U_abs_le (z 0) (z 1))
  have h2 := abs_le.mp (K.U_abs_le (z 0) (z 2))
  have h3 := abs_le.mp (K.U_abs_le (z 1) (z 2))
  rw [majority, abs_le]
  set x := K.U (z 0) (z 1)
  set y := K.U (z 0) (z 2)
  set t := K.U (z 1) (z 2)
  have a1 : 0 ≤ 1 - x := by linarith
  have a2 : 0 ≤ 1 + x := by linarith
  have b1 : 0 ≤ 1 - y := by linarith
  have b2 : 0 ≤ 1 + y := by linarith
  have c1 : 0 ≤ 1 - t := by linarith
  have c2 : 0 ≤ 1 + t := by linarith
  constructor
  · nlinarith [mul_nonneg (mul_nonneg a2 b2) c2, mul_nonneg (mul_nonneg a1 b2) c2,
      mul_nonneg (mul_nonneg a2 b1) c2, mul_nonneg (mul_nonneg a2 b2) c1]
  · nlinarith [mul_nonneg (mul_nonneg a1 b1) c1, mul_nonneg (mul_nonneg a2 b1) c1,
      mul_nonneg (mul_nonneg a1 b2) c1, mul_nonneg (mul_nonneg a1 b1) c2]

/-- `μ = 3m − τ`. -/
noncomputable def μ : ℝ := 3 * K.m - K.τ

/-- **`E 𝒫 = μ`.** -/
theorem E_majority : K.E (fun ω : Sample d 3 => K.majority ω.2) = K.μ := by
  rw [E_eq_colours, add_self_div_two]
  simp only [majority, sum_fun_fin_succ, Fintype.sum_unique, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have hout : ∀ A : ℝ, ∑ c, K.w c * A = A := fun A => by rw [← sum_mul, K.w_sum, one_mul]
  have e1 : ∑ a, ∑ b, ∑ c, K.w a * K.w b * K.w c * K.U a b = K.m := by
    rw [m_eq_double_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [← hout (K.w a * K.U a b * K.w b)]
    exact sum_congr rfl fun c _ => by ring
  have e2 : ∑ a, ∑ b, ∑ c, K.w a * K.w b * K.w c * K.U a c = K.m := by
    rw [m_eq_double_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun c _ => ?_
    rw [← hout (K.w a * K.U a c * K.w c)]
    exact sum_congr rfl fun b _ => by ring
  have e3 : ∑ a, ∑ b, ∑ c, K.w a * K.w b * K.w c * K.U b c = K.m := by
    rw [m_eq_double_sum, ← hout (∑ i, ∑ j, K.w i * K.U i j * K.w j)]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun c _ => by ring
  have e4 : ∑ a, ∑ b, ∑ c, K.w a * K.w b * K.w c * (K.U a b * K.U a c * K.U b c) = K.τ := by
    rw [τ]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
    rw [K.U_symm a c]
    ring
  calc _ = ∑ a, ∑ b, ∑ c, (K.w a * K.w b * K.w c * K.U a b + K.w a * K.w b * K.w c * K.U a c
        + K.w a * K.w b * K.w c * K.U b c
        - K.w a * K.w b * K.w c * (K.U a b * K.U a c * K.U b c)) :=
        sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => by ring
    _ = K.μ := by
        simp only [sum_add_distrib, sum_sub_distrib]
        rw [e1, e2, e3, e4, μ]
        ring

end FiniteKernel

end EvenCycleApex
