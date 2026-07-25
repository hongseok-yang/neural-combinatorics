import OddCycleBound.PathDensity

/-!
# Integral-form positivity certificates (Φ₅, Φ₇ in the integral moments)

The Φ₅/Φ₇ positivity certificates are derived for the **integral moments**
`specMoment U μ j = ∫ g · Aʲ g`, using only the integral sum-of-squares lemmas — so the certificate
side is fully grounded in the integral definition of the graphon.

The degree-2 SOS `sos2` (a Hankel form `[s_{i+j}] ⪰ 0`, proved as `∫ (square) ≥ 0`) is the
engine; `specMoment_sos_five` and `specMoment_sos_seven` are then pure polynomial algebra in the `specMoment`.
-/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

/-- `s₀ = ∫ g² ≥ 0`. -/
lemma specMoment_zero_nonneg (hU : IsGraphon U μ) : 0 ≤ specMoment U μ 0 := by
  rw [specMoment]
  refine integral_nonneg fun x => ?_
  show 0 ≤ degCentered U μ x * compressIter U μ 0 x
  rw [compressIter_zero]
  exact mul_self_nonneg _

/-- **Degree-2 sum-of-squares** in the integral moments: the Hankel form `[s_{i+j}]` is PSD,
proved as `∫ (c₂h₂ + c₁h₁ + c₀h₀)² ≥ 0`. -/
lemma sos2 (hU : IsGraphon U μ) (c2 c1 c0 : ℝ) :
    0 ≤ c2 ^ 2 * specMoment U μ 4 + 2 * c2 * c1 * specMoment U μ 3 + (2 * c2 * c0 + c1 ^ 2) * specMoment U μ 2
        + 2 * c1 * c0 * specMoment U μ 1 + c0 ^ 2 * specMoment U μ 0 := by
  have hnn : 0 ≤ ∫ x, (c2 * compressIter U μ 2 x + c1 * compressIter U μ 1 x + c0 * compressIter U μ 0 x) ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  have m22 : ∫ x, compressIter U μ 2 x * compressIter U μ 2 x ∂μ = specMoment U μ 4 := moment hU 2 2
  have m21 : ∫ x, compressIter U μ 2 x * compressIter U μ 1 x ∂μ = specMoment U μ 3 := moment hU 1 2
  have m20 : ∫ x, compressIter U μ 2 x * compressIter U μ 0 x ∂μ = specMoment U μ 2 := moment hU 0 2
  have m11 : ∫ x, compressIter U μ 1 x * compressIter U μ 1 x ∂μ = specMoment U μ 2 := moment hU 1 1
  have m10 : ∫ x, compressIter U μ 1 x * compressIter U μ 0 x ∂μ = specMoment U μ 1 := moment hU 0 1
  have m00 : ∫ x, compressIter U μ 0 x * compressIter U μ 0 x ∂μ = specMoment U μ 0 := moment hU 0 0
  have t22 : Integrable (fun x => c2 ^ 2 * (compressIter U μ 2 x * compressIter U μ 2 x)) μ :=
    ((good_compressIter hU 2).mul (good_compressIter hU 2)).integrable.const_mul _
  have t21 : Integrable (fun x => 2 * c2 * c1 * (compressIter U μ 2 x * compressIter U μ 1 x)) μ :=
    ((good_compressIter hU 2).mul (good_compressIter hU 1)).integrable.const_mul _
  have t20 : Integrable (fun x => 2 * c2 * c0 * (compressIter U μ 2 x * compressIter U μ 0 x)) μ :=
    ((good_compressIter hU 2).mul (good_compressIter hU 0)).integrable.const_mul _
  have t11 : Integrable (fun x => c1 ^ 2 * (compressIter U μ 1 x * compressIter U μ 1 x)) μ :=
    ((good_compressIter hU 1).mul (good_compressIter hU 1)).integrable.const_mul _
  have t10 : Integrable (fun x => 2 * c1 * c0 * (compressIter U μ 1 x * compressIter U μ 0 x)) μ :=
    ((good_compressIter hU 1).mul (good_compressIter hU 0)).integrable.const_mul _
  have t00 : Integrable (fun x => c0 ^ 2 * (compressIter U μ 0 x * compressIter U μ 0 x)) μ :=
    ((good_compressIter hU 0).mul (good_compressIter hU 0)).integrable.const_mul _
  have iR4 : Integrable (fun x => 2 * c1 * c0 * (compressIter U μ 1 x * compressIter U μ 0 x)
      + c0 ^ 2 * (compressIter U μ 0 x * compressIter U μ 0 x)) μ := t10.add t00
  have iR3 : Integrable (fun x => c1 ^ 2 * (compressIter U μ 1 x * compressIter U μ 1 x)
      + (2 * c1 * c0 * (compressIter U μ 1 x * compressIter U μ 0 x)
        + c0 ^ 2 * (compressIter U μ 0 x * compressIter U μ 0 x))) μ := t11.add iR4
  have iR2 : Integrable (fun x => 2 * c2 * c0 * (compressIter U μ 2 x * compressIter U μ 0 x)
      + (c1 ^ 2 * (compressIter U μ 1 x * compressIter U μ 1 x)
        + (2 * c1 * c0 * (compressIter U μ 1 x * compressIter U μ 0 x)
          + c0 ^ 2 * (compressIter U μ 0 x * compressIter U μ 0 x)))) μ := t20.add iR3
  have iR1 : Integrable (fun x => 2 * c2 * c1 * (compressIter U μ 2 x * compressIter U μ 1 x)
      + (2 * c2 * c0 * (compressIter U μ 2 x * compressIter U μ 0 x)
        + (c1 ^ 2 * (compressIter U μ 1 x * compressIter U μ 1 x)
          + (2 * c1 * c0 * (compressIter U μ 1 x * compressIter U μ 0 x)
            + c0 ^ 2 * (compressIter U μ 0 x * compressIter U μ 0 x))))) μ := t21.add iR2
  have hexp : ∫ x, (c2 * compressIter U μ 2 x + c1 * compressIter U μ 1 x + c0 * compressIter U μ 0 x) ^ 2 ∂μ
      = c2 ^ 2 * specMoment U μ 4 + 2 * c2 * c1 * specMoment U μ 3 + (2 * c2 * c0 + c1 ^ 2) * specMoment U μ 2
        + 2 * c1 * c0 * specMoment U μ 1 + c0 ^ 2 * specMoment U μ 0 := by
    calc ∫ x, (c2 * compressIter U μ 2 x + c1 * compressIter U μ 1 x + c0 * compressIter U μ 0 x) ^ 2 ∂μ
        = ∫ x, (c2 ^ 2 * (compressIter U μ 2 x * compressIter U μ 2 x)
            + (2 * c2 * c1 * (compressIter U μ 2 x * compressIter U μ 1 x)
              + (2 * c2 * c0 * (compressIter U μ 2 x * compressIter U μ 0 x)
                + (c1 ^ 2 * (compressIter U μ 1 x * compressIter U μ 1 x)
                  + (2 * c1 * c0 * (compressIter U μ 1 x * compressIter U μ 0 x)
                    + c0 ^ 2 * (compressIter U μ 0 x * compressIter U μ 0 x)))))) ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_); ring
      _ = c2 ^ 2 * (∫ x, compressIter U μ 2 x * compressIter U μ 2 x ∂μ)
            + (2 * c2 * c1 * (∫ x, compressIter U μ 2 x * compressIter U μ 1 x ∂μ)
              + (2 * c2 * c0 * (∫ x, compressIter U μ 2 x * compressIter U μ 0 x ∂μ)
                + (c1 ^ 2 * (∫ x, compressIter U μ 1 x * compressIter U μ 1 x ∂μ)
                  + (2 * c1 * c0 * (∫ x, compressIter U μ 1 x * compressIter U μ 0 x ∂μ)
                    + c0 ^ 2 * (∫ x, compressIter U μ 0 x * compressIter U μ 0 x ∂μ))))) := by
          rw [integral_add t22 iR1, integral_add t21 iR2, integral_add t20 iR3,
            integral_add t11 iR4, integral_add t10 t00,
            integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
            integral_const_mul, integral_const_mul]
      _ = c2 ^ 2 * specMoment U μ 4 + 2 * c2 * c1 * specMoment U μ 3 + (2 * c2 * c0 + c1 ^ 2) * specMoment U μ 2
            + 2 * c1 * c0 * specMoment U μ 1 + c0 ^ 2 * specMoment U μ 0 := by
          rw [m22, m21, m20, m11, m10, m00]; ring
  rw [hexp] at hnn; exact hnn

/-! ### The C₅ certificate in integral moments -/

/-- `Φ₅ ≥ 0` (integral form): the completed-square certificate of `paper.tex` over `specMoment`. -/
lemma specMoment_sos_five (hU : IsGraphon U μ) (q : ℝ) :
    0 ≤ 4 * (specMoment U μ 0) ^ 2 + 4 * specMoment U μ 2 + (8 * q - 5) * specMoment U μ 1
        + (12 * q ^ 2 - 15 * q + 5) * specMoment U μ 0 := by
  have h1 := sos2 hU 0 1 ((8 * q - 5) / 8)
  have h2 := specMoment_zero_nonneg hU
  nlinarith [h1, h2, sq_nonneg (specMoment U μ 0), mul_nonneg h2 (sq_nonneg (q - 5 / 8))]

/-! ### The C₇ certificate in integral moments -/

lemma specMoment_sos_seven_Lpart (hU : IsGraphon U μ) (q : ℝ) (hq1 : q ≤ 1 / 2) :
    0 ≤ 6 * specMoment U μ 4 + (12 * q - 7) * specMoment U μ 3 + (18 * q ^ 2 - 21 * q + 7) * specMoment U μ 2
        + (24 * q ^ 3 - 42 * q ^ 2 + 28 * q - 7) * specMoment U μ 1
        + (30 * q ^ 4 - 70 * q ^ 3 + 70 * q ^ 2 - 35 * q + 7) * specMoment U μ 0 := by
  have hD : (0 : ℝ) < 288 * q ^ 2 - 336 * q + 119 := by nlinarith [sq_nonneg (12 * q - 7)]
  have hs0 := specMoment_zero_nonneg hU
  have hy : (0 : ℝ) ≤ 1 / 2 - q := by linarith
  have hN : (0 : ℝ) ≤ 5184 * q ^ 6 - 18144 * q ^ 5 + 28602 * q ^ 4 - 25802 * q ^ 3
      + 13874 * q ^ 2 - 4165 * q + 539 := by
    nlinarith [hy, pow_nonneg hy 3, pow_nonneg hy 4, pow_nonneg hy 5, pow_nonneg hy 6,
      sq_nonneg (1 / 2 - q), mul_nonneg hy (sq_nonneg (1 / 2 - q))]
  have hSq1 := sos2 hU 12 (12 * q - 7) 0
  have hSq2 := sos2 hU 0 (288 * q ^ 2 - 336 * q + 119)
    (12 * (24 * q ^ 3 - 42 * q ^ 2 + 28 * q - 7))
  have hc : (0 : ℝ) < 24 * (288 * q ^ 2 - 336 * q + 119) := by positivity
  rw [← mul_nonneg_iff_of_pos_left hc]
  nlinarith [mul_nonneg hD.le hSq1, hSq2, mul_nonneg hN hs0]

lemma specMoment_sos_seven_B (hU : IsGraphon U μ) (q : ℝ) :
    0 ≤ 12 * specMoment U μ 2 + (36 * q - 21) * specMoment U μ 1 + (36 * q ^ 2 - 42 * q + 14) * specMoment U μ 0 := by
  have hs0 := specMoment_zero_nonneg hU
  have h144 : (0 : ℝ) ≤ 144 * q ^ 2 - 168 * q + 77 := by nlinarith [sq_nonneg (12 * q - 7)]
  have hSqB := sos2 hU 0 24 (36 * q - 21)
  have hc : (0 : ℝ) < (48 : ℝ) := by norm_num
  rw [← mul_nonneg_iff_of_pos_left hc]
  nlinarith [hSqB, mul_nonneg h144 hs0]

/-- `Φ₇ ≥ 0` (integral form), valid for `0 ≤ q ≤ ½`. -/
lemma specMoment_sos_seven (hU : IsGraphon U μ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    0 ≤ 6 * specMoment U μ 4 + (12 * q - 7) * specMoment U μ 3 + (18 * q ^ 2 - 21 * q + 7) * specMoment U μ 2
        + (24 * q ^ 3 - 42 * q ^ 2 + 28 * q - 7) * specMoment U μ 1
        + (30 * q ^ 4 - 70 * q ^ 3 + 70 * q ^ 2 - 35 * q + 7) * specMoment U μ 0
        + 12 * specMoment U μ 0 * specMoment U μ 2 + (36 * q - 21) * specMoment U μ 0 * specMoment U μ 1
        + (36 * q ^ 2 - 42 * q + 14) * (specMoment U μ 0) ^ 2 + 6 * (specMoment U μ 0) ^ 3
        + 6 * (specMoment U μ 1) ^ 2 := by
  have hLpart := specMoment_sos_seven_Lpart hU q hq1
  have hB := specMoment_sos_seven_B hU q
  have hs0 := specMoment_zero_nonneg hU
  nlinarith [hLpart, hB, hs0, sq_nonneg (specMoment U μ 1), mul_nonneg hs0 hB,
    mul_nonneg hs0 (sq_nonneg (specMoment U μ 0))]

end OddCycleBound
