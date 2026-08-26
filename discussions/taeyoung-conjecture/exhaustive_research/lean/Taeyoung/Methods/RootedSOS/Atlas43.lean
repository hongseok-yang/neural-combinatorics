import Taeyoung.Methods.RootedSOS.Atlas43CoefficientProof
import Taeyoung.Methods.RootedSOS.House

/-!
# Final interface for the Atlas 43 rooted SOS certificate

All positivity and interval reasoning is complete.  The proposition
`CertificateIdentity` deliberately isolates the remaining machine-arithmetic
task: expanding the two Gram forms and checking the 91 exact coefficients.
Once that proposition is proved from the embedded certificate, the two
theorems below immediately deliver the graphon bound and catalogue status.
-/

open MeasureTheory

namespace Taeyoung.Methods.RootedSOS.Atlas43

open Taeyoung
open Taeyoung.Methods.RootedSOS.Atlas43Data
open Taeyoung.Methods.RootedSOS.Atlas43Flags
open Taeyoung.Methods.RootedSOS.Atlas43Coefficients
open Taeyoung.Methods.RootedSOS.House

/-- The sole remaining Atlas 43 certificate obligation.  Our integer Gram
factors scale the mathematical matrices by `D²`, hence the factor on the
right-hand side. -/
def CertificateIdentity : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Graphon Ω μ),
    certificateSOS W (2 * cliqueDensity 2 W - 1) =
      (factorDenominator : ℝ) ^ 2 *
        (homDensity houseGraph W - houseTarget (cliqueDensity 2 W))

/-- The embedded rational witness satisfies the complete analytic
certificate identity. -/
theorem certificateIdentity : CertificateIdentity := by
  intro Ω _ μ _ W
  exact certificate_identity μ W

/-- The checked coefficient identity implies the desired house inequality. -/
theorem house_bound_of_certificateIdentity (hcert : CertificateIdentity)
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    houseTarget (cliqueDensity 2 W) ≤ homDensity houseGraph W := by
  let p := cliqueDensity 2 W
  let u := 2 * p - 1
  have hu₀ : 0 ≤ u := by dsimp [u, p]; linarith
  have hp₁ : p ≤ 1 := cliqueDensity_le_one 2 W
  have hu₁ : u ≤ 1 := by dsimp [u]; linarith
  have hsos : 0 ≤ certificateSOS W u := certificateSOS_nonneg W u hu₀ hu₁
  have hid := hcert Ω μ W
  have hD : 0 < (factorDenominator : ℝ) ^ 2 := by
    rw [header_eq.2.1]
    norm_num
  dsimp [u, p] at hsos
  rw [hid] at hsos
  nlinarith

/-- Completing the 91 coefficient checks completes the Atlas 43 catalogue
row; no further analytic or chromatic argument is required. -/
theorem satisfiesLowerBound_house_of_certificateIdentity
    (hcert : CertificateIdentity) : SatisfiesLowerBound houseGraph :=
  satisfiesLowerBound_house_of_bound (house_bound_of_certificateIdentity hcert)

/-- Atlas 43 is fully verified by the checked rooted-SOS certificate. -/
theorem satisfiesLowerBound_house : SatisfiesLowerBound houseGraph :=
  satisfiesLowerBound_house_of_certificateIdentity certificateIdentity

end Taeyoung.Methods.RootedSOS.Atlas43
