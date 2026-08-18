import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Coefficientwise positivity for real formal power series

This file contains the small ordered-algebra layer used in the dependence-
polynomial root argument.  In particular, a power series with zero constant
coefficient and nonnegative coefficients has a coefficientwise nonnegative
geometric sum.
-/

open scoped PowerSeries.WithPiTopology

namespace PowerSeries

/-- Every coefficient of a real formal power series is nonnegative. -/
def CoeffNonneg (f : PowerSeries ℝ) : Prop :=
  ∀ n, 0 ≤ coeff n f

theorem coeffNonneg_mk {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) :
    CoeffNonneg (mk a) := by
  intro n
  simpa using ha n

theorem coeffNonneg_zero : CoeffNonneg (0 : PowerSeries ℝ) := by
  intro n
  simp

theorem coeffNonneg_one : CoeffNonneg (1 : PowerSeries ℝ) := by
  intro n
  simp only [coeff_one]
  split_ifs <;> norm_num

theorem coeffNonneg_X : CoeffNonneg (X : PowerSeries ℝ) := by
  intro n
  simp only [coeff_X]
  split_ifs <;> norm_num

theorem CoeffNonneg.add {f g : PowerSeries ℝ}
    (hf : CoeffNonneg f) (hg : CoeffNonneg g) : CoeffNonneg (f + g) := by
  intro n
  rw [map_add]
  exact add_nonneg (hf n) (hg n)

theorem CoeffNonneg.mul {f g : PowerSeries ℝ}
    (hf : CoeffNonneg f) (hg : CoeffNonneg g) : CoeffNonneg (f * g) := by
  intro n
  rw [coeff_mul]
  exact Finset.sum_nonneg fun ij _ => mul_nonneg (hf ij.1) (hg ij.2)

theorem CoeffNonneg.pow {f : PowerSeries ℝ} (hf : CoeffNonneg f) :
    ∀ k : ℕ, CoeffNonneg (f ^ k)
  | 0 => by simpa using coeffNonneg_one
  | k + 1 => by simpa [pow_succ] using (hf.pow k).mul hf

/-- The formal geometric sum of a coefficientwise nonnegative series is
coefficientwise nonnegative.  The zero-constant-term hypothesis is precisely
what makes the family of powers summable in the product topology. -/
theorem coeffNonneg_tsum_pow {f : PowerSeries ℝ}
    (hconst : f.constantCoeff = 0) (hf : CoeffNonneg f) :
    CoeffNonneg (∑' k : ℕ, f ^ k) := by
  have hs : Summable (f ^ ·) :=
    WithPiTopology.summable_pow_of_constantCoeff_eq_zero hconst
  have hsum : HasSum (f ^ ·) (∑' k : ℕ, f ^ k) := hs.hasSum
  intro n
  have hcoeff :=
    ((WithPiTopology.hasSum_iff_hasSum_coeff ℝ).mp hsum) n
  rw [← hcoeff.tsum_eq]
  exact tsum_nonneg fun k => hf.pow k n

/-- Positivity step behind the vertex-deletion proof for ratios of dependence
polynomials.  If `D = A - X * B` and `B / A` is coefficientwise nonnegative,
then `A / D` is the geometric series in `X * (B / A)`, hence is also
coefficientwise nonnegative. -/
theorem coeffNonneg_mul_inv_of_eq_sub_X_mul
    {A B D : PowerSeries ℝ}
    (hA : constantCoeff A ≠ 0)
    (hD : D = A - X * B)
    (hBA : CoeffNonneg (B * A⁻¹)) :
    CoeffNonneg (A * D⁻¹) := by
  let R : PowerSeries ℝ := B * A⁻¹
  let F : PowerSeries ℝ := X * R
  let Q : PowerSeries ℝ := ∑' k : ℕ, F ^ k
  have hR : CoeffNonneg R := by simpa [R] using hBA
  have hF : CoeffNonneg F := coeffNonneg_X.mul hR
  have hFconst : constantCoeff F = 0 := by simp [F]
  have hQ : CoeffNonneg Q := by
    simpa [Q] using coeffNonneg_tsum_pow hFconst hF
  have hfactor : D = A * (1 - F) := by
    rw [hD]
    apply Eq.symm
    calc
      A * (1 - F) = A - A * F := by ring
      _ = A - X * B * (A * A⁻¹) := by
        congr 1
        simp only [F, R]
        ring
      _ = A - X * B := by rw [PowerSeries.mul_inv_cancel A hA, mul_one]
  have honeF : constantCoeff (1 - F) ≠ 0 := by
    simp [hFconst]
  have hQinv : Q = (1 - F)⁻¹ := by
    apply (PowerSeries.eq_inv_iff_mul_eq_one honeF).2
    exact WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hFconst
  have hAD : A * D⁻¹ = Q := by
    rw [hfactor, PowerSeries.mul_inv_rev]
    calc
      A * ((1 - F)⁻¹ * A⁻¹) = (A * A⁻¹) * (1 - F)⁻¹ := by ring
      _ = (1 - F)⁻¹ := by rw [PowerSeries.mul_inv_cancel A hA, one_mul]
      _ = Q := hQinv.symm
  rw [hAD]
  exact hQ

/-- Coefficientwise nonnegativity is transitive for formal ratios. -/
theorem coeffNonneg_ratio_trans {A B C : PowerSeries ℝ}
    (hB : constantCoeff B ≠ 0)
    (hAB : CoeffNonneg (A * B⁻¹))
    (hBC : CoeffNonneg (B * C⁻¹)) :
    CoeffNonneg (A * C⁻¹) := by
  have hprod := hAB.mul hBC
  have heq : (A * B⁻¹) * (B * C⁻¹) = A * C⁻¹ := by
    calc
      (A * B⁻¹) * (B * C⁻¹) = A * (B⁻¹ * B) * C⁻¹ := by ring
      _ = A * C⁻¹ := by rw [PowerSeries.inv_mul_cancel B hB, mul_one]
  rw [heq] at hprod
  exact hprod

end PowerSeries
