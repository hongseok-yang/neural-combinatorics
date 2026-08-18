import Taeyoung.Foundation.Status
import Taeyoung.Methods.OddCycleC5.C5Bound

/-!
# Public interface for the finite `C₅` method

The analytic theorem below is fully checked for arbitrary probability spaces
and graphons.  The later Atlas module records separately whether its finite
graph encoding and common homomorphism-density interface have been bridged.
-/

open MeasureTheory

namespace Taeyoung.Methods.OddCycleC5

namespace Internal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- A graphon from the shared foundation satisfies the hypotheses of the
short-cycle integral development. -/
theorem ofFoundation (W : Taeyoung.Graphon Ω μ) : IsGraphon W.toFun μ where
  meas := W.measurable
  nonneg := W.nonneg
  le_one := W.le_one
  symm := W.symm

end Internal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- Fully verified analytic `C₅` inequality for a shared-foundation graphon.
The density symbols here are those of the extracted integral development; a
separate finite-graph bridge connects them to `homDensity`. -/
theorem c5_shortCycle_bound (W : Taeyoung.Graphon Ω μ) :
    Internal.cycleDensity μ W.toFun 5 ≥
      Internal.edgeDensity W.toFun μ ^ 5 -
        Internal.edgeDensity W.toFun μ *
          (1 - Internal.edgeDensity W.toFun μ) ^ 4 :=
  Internal.cycleDensity_five_bound (Internal.ofFoundation W)

end Taeyoung.Methods.OddCycleC5
