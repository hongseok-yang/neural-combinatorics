import OddCycleBound.IntermediateRegion.CouplingBounds

/-!
# Refined trace bound at a the intermediate region leading_eigenvalue

This file isolates the trace half of the master-defect estimate.  One
complement-compression eigenvalue is retained exactly, while every other odd
power is charged to the Hilbert--Schmidt radius left after that leading_eigenvalue
square has been removed.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.DenseRegion

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega -> Omega -> Real}

/-- Spectral form of the refined leading_eigenvalue trace estimate.  The possible
zero eigenspace is absent from both sides and therefore needs no special
treatment. -/
theorem centered_trace_leading_eigenvalue_lower_bound
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    {m : Nat} (hm : Odd m) (hm3 : 3 <= m) :
    let alpha := complementEigenvalue hW i
    let L := leadingEigenvalueSafeRadius hW i
    (-alpha ^ m - L ^ (m - 2) *
        (centeredTraceSq hW - alpha ^ 2) <=
      trace mu (compPow mu (centeredKernel W mu) (m - 1))) := by
  dsimp only
  let alpha := complementEigenvalue hW i
  let L := leadingEigenvalueSafeRadius hW i
  let correction := alpha ^ m - L ^ (m - 2) * alpha ^ 2
  have hseries :=
    centered_trace_compPow_hasSum_eigen_pow_of_ge_three hW hm3
  have hsquare := centeredEigenvalue_square_summable hW
  have hscaled : Summable (fun j : CenteredEigenIndex hW =>
      -L ^ (m - 2) * centeredEigenvalue hW j ^ 2) :=
    hsquare.mul_left (-L ^ (m - 2))
  have hcorrection : Summable (fun j : CenteredEigenIndex hW =>
      if j = i then correction else 0) := by
    exact (hasSum_ite_eq i correction).summable
  have hlower : Summable (fun j : CenteredEigenIndex hW =>
      -L ^ (m - 2) * centeredEigenvalue hW j ^ 2 -
        if j = i then correction else 0) :=
    hscaled.sub hcorrection
  have hpoint : forall j : CenteredEigenIndex hW,
      -L ^ (m - 2) * centeredEigenvalue hW j ^ 2 -
          (if j = i then correction else 0) <=
        centeredEigenvalue hW j ^ m := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [if_pos]
      have heigen : centeredEigenvalue hW i = -alpha := by
        simp [alpha, complementEigenvalue]
      rw [heigen, hm.neg_pow]
      dsimp [correction]
      ring_nf
      exact le_rfl
    · simp only [if_neg hji, sub_zero]
      have hle : complementEigenvalue hW j <= L :=
        (le_abs_self _).trans
          (abs_complementEigenvalue_le_leadingEigenvalueSafeRadius hW hji)
      have hodd := odd_pow_le_q_pow_mul_sq
        (leadingEigenvalueSafeRadius_nonneg hW i) hle hm hm3
      have hneg := neg_le_neg hodd
      simpa [L, complementEigenvalue, hm.neg_pow] using hneg
  have hcompare :
      (∑' j : CenteredEigenIndex hW,
        (-L ^ (m - 2) * centeredEigenvalue hW j ^ 2 -
          if j = i then correction else 0)) <=
        ∑' j : CenteredEigenIndex hW, centeredEigenvalue hW j ^ m :=
    Summable.tsum_le_tsum hpoint hlower hseries.summable
  have hcorrectionSum :
      (∑' j : CenteredEigenIndex hW,
        if j = i then correction else 0) = correction := by
    simpa using
      (tsum_ite_eq i (fun _ : CenteredEigenIndex hW => correction))
  rw [hscaled.tsum_sub hcorrection, tsum_mul_left, hcorrectionSum] at hcompare
  change -L ^ (m - 2) * centeredTraceSq hW - correction <=
    ∑' j : CenteredEigenIndex hW, centeredEigenvalue hW j ^ m at hcompare
  calc
    -alpha ^ m - L ^ (m - 2) *
          (centeredTraceSq hW - alpha ^ 2) =
        -L ^ (m - 2) * centeredTraceSq hW - correction := by
          dsimp [correction]
          ring
    _ <= ∑' j : CenteredEigenIndex hW,
        centeredEigenvalue hW j ^ m := hcompare
    _ = trace mu (compPow mu (centeredKernel W mu) (m - 1)) :=
      hseries.tsum_eq

/-- The trace estimate in the form used by the master defect.  The centered
degree bound pays twice for the coupling vector. -/
theorem centered_trace_leading_eigenvalue_defect_lower_bound
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    {m : Nat} (hm : Odd m) (hm3 : 3 <= m) :
    let alpha := complementEigenvalue hW i
    let L := leadingEigenvalueSafeRadius hW i
    (-alpha ^ m - L ^ m +
        2 * L ^ (m - 2) * ‖centeredDegreeL2 hW‖ ^ 2 <=
      trace mu (compPow mu (centeredKernel W mu) (m - 1))) := by
  dsimp only
  let alpha := complementEigenvalue hW i
  let L := leadingEigenvalueSafeRadius hW i
  have htrace := centered_trace_leading_eigenvalue_lower_bound hW i hm hm3
  have hbound := centeredTraceSq_add_degree_bound hW
  have hLsq := leadingEigenvalueSafeRadius_sq hW i
  have hrem :
      centeredTraceSq hW - alpha ^ 2 <=
        L ^ 2 - 2 * ‖centeredDegreeL2 hW‖ ^ 2 := by
    dsimp [alpha, L] at hLsq ⊢
    nlinarith
  have hpowNonneg : 0 <= L ^ (m - 2) :=
    pow_nonneg (leadingEigenvalueSafeRadius_nonneg hW i) _
  have hmul := mul_le_mul_of_nonneg_left hrem hpowNonneg
  have hpower : L ^ m = L ^ (m - 2) * L ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  calc
    -alpha ^ m - L ^ m +
          2 * L ^ (m - 2) * ‖centeredDegreeL2 hW‖ ^ 2 =
        -alpha ^ m - L ^ (m - 2) *
          (L ^ 2 - 2 * ‖centeredDegreeL2 hW‖ ^ 2) := by
            rw [hpower]
            ring
    _ <= -alpha ^ m - L ^ (m - 2) *
          (centeredTraceSq hW - alpha ^ 2) := by
            linarith
    _ <= trace mu (compPow mu (centeredKernel W mu) (m - 1)) := htrace

end OddCycleBound.IntermediateRegion
