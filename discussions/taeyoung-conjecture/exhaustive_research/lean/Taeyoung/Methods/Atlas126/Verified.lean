import Taeyoung.Methods.Atlas126.AVerified
import Taeyoung.Methods.Atlas126.CVerified
import Taeyoung.Methods.Atlas126.JunctionVerified
import Taeyoung.Methods.Atlas126.HighVerified
import Taeyoung.Methods.Atlas126.Low
import Taeyoung.Methods.Atlas126.High

open MeasureTheory

namespace Taeyoung.Methods.Atlas126

open Taeyoung Taeyoung.Methods

theorem graph126_bound_verified {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (W : Graphon Ω μ)
    (hp0 : (1/2 : ℝ) ≤ cliqueDensity 2 W) :
    target (cliqueDensity 2 W) ≤ homDensity graph126 W := by
  rcases le_total (cliqueDensity 2 W) (2/3 : ℝ) with hpLow | hpHigh
  · exact graph126_bound_low_of_planes W hp0 hpLow
      (fun hx0 hx1 => polynomialPlaneA hx0 hx1)
      (fun hx0 hx1 => polynomialPlaneC hx0 hx1)
      (fun hx0 hx1 => polynomialPlaneJ hx0 hx1)
  · exact graph126_bound_high_of_plane W hpHigh
      (polynomialPlaneHigh hpHigh (cliqueDensity_le_one 2 W))

theorem satisfiesLowerBound_126 : SatisfiesLowerBound graph126 := by
  apply satisfiesLowerBound_126_of_bound
  intro Ω _ μ _ W hp
  exact graph126_bound_verified W hp

end Taeyoung.Methods.Atlas126
