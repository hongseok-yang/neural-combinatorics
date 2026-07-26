import PureChordal.Main
import PureChordal.Examples.Diamond
import PureChordal.Examples.GoldnerHarary

namespace PureChordal

open MeasureTheory

/-- The diamond bound `t(K₄-e,W) ≥ p(2p-1)²` for `p ≥ 1/2`. -/
theorem diamond_homDensity_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (W : Graphon Ω μ)
    (hp : (1 / 2 : ℝ) ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W * (2 * cliqueDensity 2 W - 1) ^ 2 ≤
      homDensity diamondGraph W := by
  rw [← diamond_certificateBound]
  apply diamondDecomp.certificateBound_le_homDensity W (by omega)
  norm_num
  exact hp

/-- The Goldner--Harary bound
`t(GH,W) ≥ p(2p-1)(3p-2)⁸` for `p ≥ 2/3`. -/
theorem goldnerHarary_homDensity_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (W : Graphon Ω μ)
    (hp : (2 / 3 : ℝ) ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W * (2 * cliqueDensity 2 W - 1) *
        (3 * cliqueDensity 2 W - 2) ^ 8 ≤
      homDensity goldnerHararyGraph W := by
  rw [← goldnerHarary_certificateBound]
  apply goldnerHararyDecomp.certificateBound_le_homDensity W (by omega)
  norm_num
  exact hp

end PureChordal
