import Taeyoung.Methods.RootedSOS.Atlas43Flags
import Taeyoung.Methods.RootedSOS.FixedDensity

namespace Taeyoung.Methods.RootedSOS.Atlas43FixedDensity

open Taeyoung.Methods.RootedSOS
open Taeyoung.Methods.RootedSOS.Atlas43Flags

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem decompositions_rows_32 : ∀ (a : Fin 8) (b : Fin 64),
    decompositionValid (gluedOrdinaryGraph
      ⟨32 + a.1, by omega⟩ b) = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43FixedDensity
