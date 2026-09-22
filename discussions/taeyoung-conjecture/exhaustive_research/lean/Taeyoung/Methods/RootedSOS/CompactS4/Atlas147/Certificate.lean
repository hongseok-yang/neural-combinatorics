import Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower.Certificate
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Upper.Certificate
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas147
open MeasureTheory Taeyoung
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem graphon_bound (W : Graphon Ω μ) (hp : (1 : Real)/2 ≤ cliqueDensity 2 W) :
    target147 (cliqueDensity 2 W) ≤ homDensity graph147 W := by
  by_cases h0 : cliqueDensity 2 W ≤ (2 : Real)/3
  · exact Lower.graphon_bound W hp h0
  have hlow0 : (2 : Real)/3 ≤ cliqueDensity 2 W := le_of_lt (lt_of_not_ge h0)
  exact Upper.graphon_bound W hlow0
    (by simpa only [div_one] using cliqueDensity_le_one 2 W)

theorem satisfiesLowerBound_147 : SatisfiesLowerBound graph147 :=
  satisfiesLowerBound_147_of_bound (fun W hp => graphon_bound W hp)
#print axioms satisfiesLowerBound_147
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas147
