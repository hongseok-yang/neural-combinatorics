import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# A weighted integral Cauchy--Schwarz inequality

The clique-density argument needs Cauchy--Schwarz in the elementary form

`(∫ A η)² ≤ (∫ A) (∫ A η²)`

for a nonnegative integrable weight `A`.  We prove it directly by integrating
`A (η - c)²`; this avoids introducing square roots of graphon products.
-/

open MeasureTheory

namespace PureChordal

/-- Weighted integral Cauchy--Schwarz: `(∫ A η)² ≤ (∫ A)(∫ A η²)` for a
nonnegative integrable weight `A`.  Proved directly by integrating `A (η - c)²`,
avoiding square roots of graphon products. -/
theorem integral_mul_sq_le_integral_mul_integral_mul_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A η : α → ℝ}
    (hA : Integrable A μ)
    (hAη : Integrable (fun x => A x * η x) μ)
    (hAη2 : Integrable (fun x => A x * η x ^ 2) μ)
    (hA0 : ∀ x, 0 ≤ A x) :
    (∫ x, A x * η x ∂μ) ^ 2
      ≤ (∫ x, A x ∂μ) * ∫ x, A x * η x ^ 2 ∂μ := by
  let a := ∫ x, A x ∂μ
  let b := ∫ x, A x * η x ∂μ
  let c := ∫ x, A x * η x ^ 2 ∂μ
  have ha0 : 0 ≤ a := by
    exact integral_nonneg hA0
  by_cases ha : a = 0
  · have hAae : A =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg hA0 hA).mp ha
    have hb : b = 0 := by
      dsimp [b]
      calc
        (∫ x, A x * η x ∂μ) = ∫ _x, (0 : ℝ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hAae] with x hx
          simp [hx]
        _ = 0 := by simp
    simp [a, b, ha, hb]
  · have ha_pos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
    let q : ℝ := b / a
    have hquad_int : Integrable (fun x => A x * (η x - q) ^ 2) μ := by
      have hfun :
          (fun x => A x * (η x - q) ^ 2) =
            (fun x => A x * η x ^ 2) -
              (fun x => (2 * q) * (A x * η x)) +
                (fun x => q ^ 2 * A x) := by
        funext x
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      rw [hfun]
      exact (hAη2.sub (hAη.const_mul (2 * q))).add (hA.const_mul (q ^ 2))
    have hquad_nonneg :
        0 ≤ ∫ x, A x * (η x - q) ^ 2 ∂μ := by
      exact integral_nonneg fun x => mul_nonneg (hA0 x) (sq_nonneg _)
    have hquad_eq :
        (∫ x, A x * (η x - q) ^ 2 ∂μ) =
          c - (2 * q) * b + q ^ 2 * a := by
      have hfun :
          (fun x => A x * (η x - q) ^ 2) =
            (fun x => A x * η x ^ 2) -
              (fun x => (2 * q) * (A x * η x)) +
                (fun x => q ^ 2 * A x) := by
        funext x
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      calc
        (∫ x, A x * (η x - q) ^ 2 ∂μ) =
            ∫ x, (A x * η x ^ 2 - (2 * q) * (A x * η x)) +
              q ^ 2 * A x ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with x
            ring
        _ = (∫ x, A x * η x ^ 2 - (2 * q) * (A x * η x) ∂μ) +
              ∫ x, q ^ 2 * A x ∂μ := by
            exact integral_add
              (hAη2.sub (hAη.const_mul (2 * q)))
              (hA.const_mul (q ^ 2))
        _ = ((∫ x, A x * η x ^ 2 ∂μ) -
              ∫ x, (2 * q) * (A x * η x) ∂μ) +
              ∫ x, q ^ 2 * A x ∂μ := by
            rw [integral_sub hAη2 (hAη.const_mul (2 * q))]
        _ = c - (2 * q) * b + q ^ 2 * a := by
            rw [integral_const_mul, integral_const_mul]
    rw [hquad_eq] at hquad_nonneg
    dsimp [q] at hquad_nonneg
    have ha_ne : a ≠ 0 := ne_of_gt ha_pos
    field_simp [ha_ne] at hquad_nonneg
    dsimp [a, b, c] at *
    nlinarith

end PureChordal
