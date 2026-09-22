import Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Low
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Middle.Certificate
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Upper.Certificate
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas171
open MeasureTheory Taeyoung
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem graphon_bound (W : Graphon Ω μ) (hp : (1 : Real)/2 ≤ cliqueDensity 2 W) :
    target171 (cliqueDensity 2 W) ≤ homDensity graph171 W := by
  by_cases hlow : cliqueDensity 2 W ≤ (5 : Real)/8
  · exact Low.graphon_bound W hp hlow
  have hstart : (5 : Real)/8 ≤ cliqueDensity 2 W := le_of_lt (lt_of_not_ge hlow)
  by_cases h0 : cliqueDensity 2 W ≤ (2 : Real)/3
  · exact Middle.graphon_bound W hstart h0
  have hlow0 : (2 : Real)/3 ≤ cliqueDensity 2 W := le_of_lt (lt_of_not_ge h0)
  exact Upper.graphon_bound W hlow0
    (by simpa only [div_one] using cliqueDensity_le_one 2 W)

theorem satisfiesLowerBound_171 : SatisfiesLowerBound graph171 :=
  satisfiesLowerBound_171_of_bound (fun W hp => graphon_bound W hp)
#print axioms satisfiesLowerBound_171
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas171
