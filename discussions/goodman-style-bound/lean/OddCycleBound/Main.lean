import OddCycleBound.BoundsC5C7
import OddCycleBound.BasicBounds
import OddCycleBound.C9
import OddCycleBound.C11
import OddCycleBound.C13
import OddCycleBound.LowBand.C9Spectral
import OddCycleBound.Conditional

/-!
# Main graphon-facing results

This file is the public facade for the main odd-cycle bounds.  It intentionally
contains only headline graphon statements, phrased directly with
`edgeDensity`, `trace`, and `compPow`.
-/

open MeasureTheory

namespace OddCycleBound

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω -> Ω -> Real}

/-- **`C₅` Goodman-type bound.**  For every graphon `W` with edge density `p`,
`t(C₅,W) ≥ p⁵ - p(1-p)⁴`. -/
theorem C5_bound (hW : IsGraphon W μ) :
    trace μ (compPow μ W 4) >=
      edgeDensity W μ ^ 5 - edgeDensity W μ * (1 - edgeDensity W μ) ^ 4 := by
  have h := C5_integral (isGraphon_compl hW)
  rw [compl_compl, edgeDensity_compl hW] at h
  have e : 1 - (1 - edgeDensity W μ) = edgeDensity W μ := by ring
  rw [e] at h
  exact h

/-- **`C₇` Goodman-type bound.**  For every graphon `W` with edge density `p`,
`t(C₇,W) ≥ p⁷ - p(1-p)⁶`. -/
theorem C7_bound (hW : IsGraphon W μ) :
    trace μ (compPow μ W 6) >=
      edgeDensity W μ ^ 7 - edgeDensity W μ * (1 - edgeDensity W μ) ^ 6 := by
  have h := C7_integral_all (isGraphon_compl hW)
  rw [compl_compl, edgeDensity_compl hW] at h
  have e : 1 - (1 - edgeDensity W μ) = edgeDensity W μ := by ring
  rw [e] at h
  exact h

/-- **Path-range `C9` bound.**  If `p >= 1003 / 2000`, then
`t(C9,W) >= p^9 - p(1-p)^8`. -/
theorem C9_path_bound (hW : IsGraphon W μ)
    (hp : 1003 / 2000 <= edgeDensity W μ) :
    trace μ (compPow μ W 8) >=
      edgeDensity W μ ^ 9 - edgeDensity W μ * (1 - edgeDensity W μ) ^ 8 := by
  have hq : edgeDensity (compl W) μ <= 997 / 2000 := by
    rw [edgeDensity_compl hW]
    linarith
  have h := C9_path_integral (isGraphon_compl hW) hq
  rw [compl_compl, edgeDensity_compl hW] at h
  have e : 1 - (1 - edgeDensity W μ) = edgeDensity W μ := by ring
  rw [e] at h
  exact h

/-- **Path-range `C11` bound.**  If `p >= 103 / 200`, then
`t(C11,W) >= p^11 - p(1-p)^10`. -/
theorem C11_path_bound (hW : IsGraphon W μ)
    (hp : 103 / 200 <= edgeDensity W μ) :
    trace μ (compPow μ W 10) >=
      edgeDensity W μ ^ 11 - edgeDensity W μ * (1 - edgeDensity W μ) ^ 10 := by
  have hq : edgeDensity (compl W) μ <= 97 / 200 := by
    rw [edgeDensity_compl hW]
    linarith
  have h := C11_path_integral (isGraphon_compl hW) hq
  rw [compl_compl, edgeDensity_compl hW] at h
  have e : 1 - (1 - edgeDensity W μ) = edgeDensity W μ := by ring
  rw [e] at h
  exact h

/-- **Path-range `C13` bound.**  If `p >= 519 / 1000`, then
`t(C13,W) >= p^13 - p(1-p)^12`. -/
theorem C13_path_bound (hW : IsGraphon W μ)
    (hp : 519 / 1000 <= edgeDensity W μ) :
    trace μ (compPow μ W 12) >=
      edgeDensity W μ ^ 13 - edgeDensity W μ * (1 - edgeDensity W μ) ^ 12 := by
  have hq : edgeDensity (compl W) μ <= 481 / 1000 := by
    rw [edgeDensity_compl hW]
    linarith
  have h := C13_path_integral (isGraphon_compl hW) hq
  rw [compl_compl, edgeDensity_compl hW] at h
  have e : 1 - (1 - edgeDensity W μ) = edgeDensity W μ := by ring
  rw [e] at h
  exact h

/-- Direct triangle-density lower bound up to an edge-density cutoff.

For an upper endpoint `rho`, this is the Razborov/Reiher branch needed on
`1 / 2 < edgeDensity W μ <= rho`, stated only with `edgeDensity`, `trace`,
and `compPow`. -/
def TriangleDensityLowerBoundUpTo (rho : Real) : Prop :=
  ∀ {Ω' : Type u} [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {W' : Ω' -> Ω' -> Real},
    IsGraphon W' μ' ->
    1 / 2 < edgeDensity W' μ' ->
    edgeDensity W' μ' <= rho ->
    let c := (1 - Real.sqrt (4 - 6 * edgeDensity W' μ')) / 3
    (3 / 2) * c * (1 - c) ^ 2 <= trace μ' (compPow μ' W' 2)

/-- **Conditional all-density `C9` bound from the direct Razborov/Reiher
triangle-density branch.**

The hypothesis is stated directly in graphon terms: on the C9 low band it gives
the triangle lower bound as an inequality involving only `edgeDensity` and
`trace μ (compPow μ W 2)`. -/
theorem C9_conditional_bound
    (hW : IsGraphon W μ)
    (htri : TriangleDensityLowerBoundUpTo.{u} (1003 / 2000)) :
    trace μ (compPow μ W 8) >=
      edgeDensity W μ ^ 9 - edgeDensity W μ * (1 - edgeDensity W μ) ^ 8 := by
  have htriDirect :
      LowBand.InfiniteSpectral.C9RazborovTriangleDensityDirectTheorem.{u} := by
    intro Ω' _ μ' _ W' hW' hgt' hle'
    exact htri hW' hgt' hle'
  by_cases hlow : edgeDensity W μ <= 1 / 2
  · have htr := trace_compPow_nonneg (W := W) hW 8
    have hrhs := rhs9_nonpos_of_le_half (W := W) hW hlow
    exact le_trans hrhs htr
  · have hgt : 1 / 2 < edgeDensity W μ := by linarith
    by_cases hpath : 1003 / 2000 <= edgeDensity W μ
    · exact C9_path_bound hW hpath
    · have hle : edgeDensity W μ <= 1003 / 2000 := by linarith
      let S :=
        (Classical.choice
          (LowBand.InfiniteSpectral.c9GraphonBudgetTraceSpectralData_lowBand
            hW hgt hle)).toC9SpectralData hW
      have htriParam :
          LowBand.InfiniteSpectral.RazborovTriangleLower W μ :=
        LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.of_direct
          htriDirect hW hgt hle
      exact S.c9_cycle_bound_of_razborov htriParam hgt hle

/-- **Conditional all-density `C11` bound from the direct Razborov/Reiher
triangle-density branch.** -/
theorem C11_conditional_bound
    (hW : IsGraphon W μ)
    (htri : TriangleDensityLowerBoundUpTo.{u} (103 / 200)) :
    trace μ (compPow μ W 10) >=
      edgeDensity W μ ^ 11 - edgeDensity W μ * (1 - edgeDensity W μ) ^ 10 := by
  have htriParam :
      1 / 2 < edgeDensity W μ -> edgeDensity W μ <= 103 / 200 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W μ := by
    intro hgt hle
    let p := edgeDensity W μ
    let c := (1 - Real.sqrt (4 - 6 * p)) / 3
    refine ⟨c, ?_, ?_, ?_, ?_⟩
    · have harg0 : 0 <= 4 - 6 * p := by
        nlinarith [hle, (show (103 : Real) / 200 < 2 / 3 by norm_num)]
      have hs_sq : (Real.sqrt (4 - 6 * p)) ^ 2 = 4 - 6 * p :=
        Real.sq_sqrt harg0
      have hs_sq_le_one : (Real.sqrt (4 - 6 * p)) ^ 2 <= (1 : Real) ^ 2 := by
        rw [hs_sq]
        nlinarith
      have hs_le_one : Real.sqrt (4 - 6 * p) <= 1 := by
        nlinarith [Real.sqrt_nonneg (4 - 6 * p),
          sq_nonneg (Real.sqrt (4 - 6 * p) - 1)]
      dsimp [c]
      nlinarith
    · have hs0 : 0 <= Real.sqrt (4 - 6 * p) := Real.sqrt_nonneg _
      dsimp [c]
      nlinarith
    · have harg0 : 0 <= 4 - 6 * p := by
        nlinarith [hle, (show (103 : Real) / 200 < 2 / 3 by norm_num)]
      have hs_sq : (Real.sqrt (4 - 6 * p)) ^ 2 = 4 - 6 * p :=
        Real.sq_sqrt harg0
      dsimp [c, p]
      nlinarith
    · dsimp [c, p]
      exact htri hW hgt hle
  exact C11_bound_of_razborov_theorem hW htriParam

/-- **Conditional near-bipartite `C13` bound from the direct Razborov/Reiher
triangle-density branch.**

The extra hypothesis is the visible edge-density range `p <= 51 / 100`; no
spectral, frontier, or negative-mass assumptions are exposed. -/
theorem C13_conditional_bound
    (hW : IsGraphon W μ)
    (htri : TriangleDensityLowerBoundUpTo.{u} (51 / 100))
    (hnear : edgeDensity W μ <= 51 / 100) :
    trace μ (compPow μ W 12) >=
      edgeDensity W μ ^ 13 - edgeDensity W μ * (1 - edgeDensity W μ) ^ 12 := by
  have htriParam :
      1 / 2 < edgeDensity W μ -> edgeDensity W μ <= 51 / 100 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W μ := by
    intro hgt hle
    let p := edgeDensity W μ
    let c := (1 - Real.sqrt (4 - 6 * p)) / 3
    refine ⟨c, ?_, ?_, ?_, ?_⟩
    · have harg0 : 0 <= 4 - 6 * p := by
        nlinarith [hle, (show (51 : Real) / 100 < 2 / 3 by norm_num)]
      have hs_sq : (Real.sqrt (4 - 6 * p)) ^ 2 = 4 - 6 * p :=
        Real.sq_sqrt harg0
      have hs_sq_le_one : (Real.sqrt (4 - 6 * p)) ^ 2 <= (1 : Real) ^ 2 := by
        rw [hs_sq]
        nlinarith
      have hs_le_one : Real.sqrt (4 - 6 * p) <= 1 := by
        nlinarith [Real.sqrt_nonneg (4 - 6 * p),
          sq_nonneg (Real.sqrt (4 - 6 * p) - 1)]
      dsimp [c]
      nlinarith
    · have hs0 : 0 <= Real.sqrt (4 - 6 * p) := Real.sqrt_nonneg _
      dsimp [c]
      nlinarith
    · have harg0 : 0 <= 4 - 6 * p := by
        nlinarith [hle, (show (51 : Real) / 100 < 2 / 3 by norm_num)]
      have hs_sq : (Real.sqrt (4 - 6 * p)) ^ 2 = 4 - 6 * p :=
        Real.sq_sqrt harg0
      dsimp [c, p]
      nlinarith
    · dsimp [c, p]
      exact htri hW hgt hle
  exact C13_nearbipartite_bound_of_razborov_theorem hW htriParam hnear

end OddCycleBound
