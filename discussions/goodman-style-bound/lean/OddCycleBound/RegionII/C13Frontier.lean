import OddCycleBound.RegionII.C13MomentPositivity
import OddCycleBound.RegionII.C13PathIdentity
import OddCycleBound.BasicBounds

/-!
# The unconditional C13 frontier window

The no-frontier branch is handled by the general Region II spectral estimate.
In the frontier branch, the exact C13 Bernstein certificates give
nonnegativity of the complemented moment defect, and the density-independent
path identity converts that defect into the desired cycle bound.
-/

open MeasureTheory

noncomputable section

namespace OddCycleBound.RegionII

open OddCycleBound.HighDensity

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

/-- The Region II C13 bound on the complete certified frontier window. -/
theorem C13_frontier_bound
    (hW : IsGraphon W μ)
    (hp_lo : 51 / 100 ≤ edgeDensity W μ)
    (hp_hi : edgeDensity W μ ≤ 519 / 1000) :
    trace μ (compPow μ W 12) ≥
      edgeDensity W μ ^ 13 -
        edgeDensity W μ * (1 - edgeDensity W μ) ^ 12 := by
  classical
  have hp : (1 : ℝ) / 2 < edgeDensity W μ := by
    norm_num at hp_lo ⊢
    linarith
  by_cases hno : ∀ i : CenteredEigenIndex hW,
      complementEigenvalue hW i ≤ 1 - edgeDensity W μ
  · simpa [cycleDensity] using
      (no_frontier_odd_cycle_bound hW (m := 13) (by decide) (by norm_num) hp hno)
  · simp only [not_forall, not_le] at hno
    obtain ⟨i, hfront⟩ := hno
    have hqlo : 481 / 1000 ≤ 1 - edgeDensity W μ := by
      norm_num at hp_hi ⊢
      linarith
    have hqhi : 1 - edgeDensity W μ ≤ 49 / 100 := by
      norm_num at hp_lo ⊢
      linarith
    have hphi := c13_momentPhi_specMoment_compl_nonneg
      hW i hqlo hqhi hfront
    have hphiU :
        0 ≤ momentPhi 13 (edgeDensity (compl W) μ)
          (specMoment (compl W) μ) := by
      rw [OddCycleBound.edgeDensity_compl hW]
      exact hphi
    have hpath := c13_path_bound_of_momentPhi_nonneg
      (isGraphon_compl hW) hphiU
    rw [OddCycleBound.compl_compl,
      OddCycleBound.edgeDensity_compl hW] at hpath
    simpa using hpath

end OddCycleBound.RegionII
