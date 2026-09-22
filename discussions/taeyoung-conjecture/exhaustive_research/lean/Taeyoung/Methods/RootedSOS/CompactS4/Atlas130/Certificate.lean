import Taeyoung.Methods.RootedSOS.CompactS4.Atlas130.UpperCertificate
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas130.LowerCertificate
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas130
open MeasureTheory Taeyoung
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem graphon_bound (W : Graphon Ω μ) (hp : (1 : Real)/2 ≤ cliqueDensity 2 W) :
    target130 (cliqueDensity 2 W) ≤ homDensity graph130 W := by
  by_cases h : cliqueDensity 2 W ≤ (2 : Real)/3
  · exact Lower.lower_graphon_bound W hp h
  · exact upper_graphon_bound W (le_of_lt (lt_of_not_ge h))
theorem satisfiesLowerBound_130 : SatisfiesLowerBound graph130 :=
  satisfiesLowerBound_130_of_bound (fun W hp => graphon_bound W hp)
#print axioms satisfiesLowerBound_130
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas130
