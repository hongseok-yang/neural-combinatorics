import OddCycleBound.RegionII.Scalar.ZoneCSmall
import OddCycleBound.RegionII.Scalar.TuranCorner
import OddCycleBound.RegionII.Certificate.ZoneCTreeSound

/-!
# Assembly of the Region-II scalar inequality

This module dispatches every admissible odd cycle length `m >= 15` to the
small-`e` analytic zones, the closed Zone-B certificate, the closed moderate
Zone-C certificate, or the analytic Turan corner.  The non-strict certificate
domains make the shared boundary `xi = 1` and the frontier ceiling explicit.
-/

noncomputable section

namespace OddCycleBound.RegionII.Scalar

namespace AdmissibleParams

variable (P : AdmissibleParams)

/-- The complete scalar Huber inequality for every admissible Region-II
parameter tuple and every odd `m >= 15`. -/
theorem scalar_huber_bound :
    P.R <= P.C * psi P.xi P.rho := by
  by_cases heSmall : P.e <= 1 / 60
  · rcases le_total 1 P.xi with hxi | hxi
    · exact P.zoneA_bound heSmall hxi
    · exact P.zoneC_small_bound heSmall hxi
  · have heLo : 1 / 60 <= P.e := le_of_not_ge heSmall
    rcases le_total 1 P.xi with hxi | hxi
    · exact P.zoneB_bound heLo hxi P.kappa_le_max
    · by_cases heCorner : 1 / 3 - 1 / 1000 < P.e
      · exact P.turan_corner_bound heCorner
      · have heHi : P.e <= 1 / 3 - 1 / 1000 := le_of_not_gt heCorner
        exact Certificate.zoneC_certificate_sound_interior
          P heLo heHi hxi P.kappa_le_max

end AdmissibleParams

end OddCycleBound.RegionII.Scalar
