import OddCycleBound.IntermediateRegion.Scalar.Definitions

/-!
# Scalar algebra for the leading_eigenvalue ceiling

This file separates the exact algebraic consequence of forced variance from
the graphon/eigenfunction argument that supplies the variance inequality.
-/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

/-- Forced variance plus the Hilbert--Schmidt bound implies the quadratic
leading_eigenvalue ceiling. -/
theorem quadratic_ceiling_of_variance_lower_bound
    {q alpha g2 : Real}
    (hq : (1 : Real) / 3 < q)
    (halpha : q < alpha)
    (halpha_half : alpha < (1 : Real) / 2)
    (hforced : alpha * (alpha - q) ^ 2 / (2 * (1 - 2 * alpha)) ≤ g2)
    (hbound : alpha ^ 2 + 2 * g2 ≤ (1 - q) * q) :
    alpha ^ 2 + q * alpha - q ≤ 0 := by
  have hden : 0 < 2 * (1 - 2 * alpha) := by linarith
  have hforced' :
      alpha * (alpha - q) ^ 2 ≤ 2 * (1 - 2 * alpha) * g2 :=
    by simpa [mul_comm, mul_left_comm, mul_assoc] using
      (div_le_iff₀ hden).mp hforced
  have hnonneg : 0 ≤ 1 - 2 * alpha := by linarith
  have hbound' : 2 * g2 ≤ (1 - q) * q - alpha ^ 2 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hbound' hnonneg
  have hmain :
      alpha * (alpha - q) ^ 2 ≤
        (1 - 2 * alpha) * ((1 - q) * q - alpha ^ 2) := by
    calc
      alpha * (alpha - q) ^ 2 ≤ 2 * (1 - 2 * alpha) * g2 := hforced'
      _ = (1 - 2 * alpha) * (2 * g2) := by ring
      _ ≤ (1 - 2 * alpha) * ((1 - q) * q - alpha ^ 2) := hmul
  have hfactor :
      (1 - alpha - q) * (alpha ^ 2 + q * alpha - q) ≤ 0 := by
    have hid :
        alpha * (alpha - q) ^ 2 -
            (1 - 2 * alpha) * ((1 - q) * q - alpha ^ 2) =
          (1 - alpha - q) * (alpha ^ 2 + q * alpha - q) := by ring
    rw [← hid]
    linarith
  have hpositive : 0 < 1 - alpha - q := by
    have hqhalf : q < (1 : Real) / 2 := by linarith
    linarith
  exact nonpos_of_mul_nonpos_right hfactor hpositive

/-- Quadratic form of the leading_eigenvalue ceiling implies the explicit square-root
radius used by `AdmissibleParams`. -/
theorem alpha_le_leadingEigenvalueRadius_of_quadratic
    {q alpha : Real}
    (hq : 0 ≤ q) (halpha : 0 ≤ alpha)
    (hquad : alpha ^ 2 + q * alpha - q ≤ 0) :
    alpha ≤ leadingEigenvalueRadius q := by
  have hsq : (2 * alpha + q) ^ 2 ≤ q ^ 2 + 4 * q := by
    nlinarith
  have hsqrt : 2 * alpha + q ≤ Real.sqrt (q ^ 2 + 4 * q) :=
    Real.le_sqrt_of_sq_le hsq
  unfold leadingEigenvalueRadius
  linarith

/-- Combined algebraic leading_eigenvalue ceiling in the exact form used by the scalar
admissibility structure. -/
theorem leadingEigenvalueRadius_of_variance_lower_bound
    {q alpha g2 : Real}
    (hq : (1 : Real) / 3 < q)
    (halpha : q < alpha)
    (halpha_half : alpha < (1 : Real) / 2)
    (hforced : alpha * (alpha - q) ^ 2 / (2 * (1 - 2 * alpha)) ≤ g2)
    (hbound : alpha ^ 2 + 2 * g2 ≤ (1 - q) * q) :
    alpha ≤ leadingEigenvalueRadius q := by
  have hquad := quadratic_ceiling_of_variance_lower_bound hq halpha halpha_half
    hforced hbound
  exact alpha_le_leadingEigenvalueRadius_of_quadratic (by linarith) (by linarith) hquad

end OddCycleBound.IntermediateRegion.Scalar
