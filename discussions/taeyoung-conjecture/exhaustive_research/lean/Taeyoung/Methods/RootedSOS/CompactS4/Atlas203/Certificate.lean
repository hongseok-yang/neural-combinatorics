import Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.UpperCertificate
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.LowerCertificate
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas203
open MeasureTheory Taeyoung
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem graphon_bound (W : Graphon Ω μ) (hp : (2 : Real)/3 ≤ cliqueDensity 2 W) :
    target203 (cliqueDensity 2 W) ≤ homDensity graph203 W := by
  by_cases h : cliqueDensity 2 W ≤ (3 : Real)/4
  · exact Lower.lower_graphon_bound W hp h
  · exact upper_graphon_bound W (le_of_lt (lt_of_not_ge h))
theorem satisfiesLowerBound_203 : SatisfiesLowerBound graph203 :=
  satisfiesLowerBound_203_of_bound (fun W hp => graphon_bound W hp)
#print axioms satisfiesLowerBound_203
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas203
