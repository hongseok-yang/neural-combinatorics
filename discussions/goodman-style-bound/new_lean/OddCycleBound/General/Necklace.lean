import OddCycleBound.Necklace

/-!
# Regression: the general necklace identity specialises to the explicit `C₅`/`C₇` forms

The general-`m` necklace identity `complTrace_necklace` (and its supporting `mixedTrace_telescope`,
`pairing_pathIter_zero`) now live in `Necklace.lean`.  This file keeps two regression `example`s
checking that `complTrace_necklace` specialises, by `simp`/`norm_num`, to the hand-unrolled
four-term (`C₅`) and six-term (`C₇`) inner-product forms.
-/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

/-! ### Regression: the hand-unrolled `ccomp5/7_necklace` are special cases -/

example (hU : IsGraphon U μ) :
    trace μ (compPow μ (compl U) 4)
      = mean μ (complIter U μ 4) - pairing μ (pathIter U μ 1) (complIter U μ 3)
        + pairing μ (pathIter U μ 2) (complIter U μ 2) - pairing μ (pathIter U μ 3) (complIter U μ 1)
        + pathDensity U μ 4 - trace μ (compPow μ U 4) := by
  have h := complTrace_necklace hU 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pairing_pathIter_zero] at h
  norm_num at h
  rw [h]; ring

example (hU : IsGraphon U μ) :
    trace μ (compPow μ (compl U) 6)
      = mean μ (complIter U μ 6) - pairing μ (pathIter U μ 1) (complIter U μ 5)
        + pairing μ (pathIter U μ 2) (complIter U μ 4) - pairing μ (pathIter U μ 3) (complIter U μ 3)
        + pairing μ (pathIter U μ 4) (complIter U μ 2) - pairing μ (pathIter U μ 5) (complIter U μ 1)
        + pathDensity U μ 6 - trace μ (compPow μ U 6) := by
  have h := complTrace_necklace hU 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pairing_pathIter_zero] at h
  norm_num at h
  rw [h]; ring

end OddCycleBound
