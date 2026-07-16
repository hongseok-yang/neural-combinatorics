/-
# High-density theorem — finite spectral support

This file isolates E1 from the construction of the finite compression model. Once P supplies
nonzero eigenvectors for the finitely many atoms and the compression norm bound `‖A‖ ≤ 1/2`, the
support conclusion is an elementary operator-norm argument.
-/

import Mathlib.Analysis.Normed.Operator.Basic

namespace OddCycleBound.HighDensity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An eigenvalue of a real bounded operator is bounded in absolute value by the operator norm. -/
lemma abs_eigenvalue_le_opNorm (A : E →L[ℝ] E) {lam : ℝ} {v : E}
    (hv : v ≠ 0) (heigen : A v = lam • v) : |lam| ≤ ‖A‖ := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hmul : |lam| * ‖v‖ ≤ ‖A‖ * ‖v‖ := by
    calc
      |lam| * ‖v‖ = ‖lam • v‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = ‖A v‖ := congrArg norm heigen.symm
      _ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
  exact le_of_mul_le_mul_right hmul hvpos

/-- **E1, abstract form.** Every eigenvalue of an operator of norm at most `1/2` belongs to the
required support interval. -/
theorem eigenvalue_mem_halfInterval (A : E →L[ℝ] E) {lam : ℝ} {v : E}
    (hA : ‖A‖ ≤ (1 : ℝ) / 2) (hv : v ≠ 0) (heigen : A v = lam • v) :
    lam ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) := by
  have habs : |lam| ≤ (1 : ℝ) / 2 := (abs_eigenvalue_le_opNorm A hv heigen).trans hA
  constructor <;> linarith [neg_abs_le lam, le_abs_self lam]

/-- Indexed form used directly by a finite atomic representation. -/
theorem atomicSupport_of_eigenpairs {ι : Type*} (A : E →L[ℝ] E)
    (lam : ι → ℝ) (v : ι → E) (hA : ‖A‖ ≤ (1 : ℝ) / 2)
    (hv : ∀ i, v i ≠ 0) (heigen : ∀ i, A (v i) = lam i • v i) :
    ∀ i, lam i ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) := by
  intro i
  exact eigenvalue_mem_halfInterval A hA (hv i) (heigen i)

end OddCycleBound.HighDensity
