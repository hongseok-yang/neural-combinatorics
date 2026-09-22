import Taeyoung.Methods.RootedSOS.S4ClassificationLookupChunk000_016Base

namespace Taeyoung.Methods.RootedSOS.S4Classification.LookupChunk000_016

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem lookup_witness_row_014 : ∀ left right : Fin 16,
    lookupWitnessValid 14 left right = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.S4Classification.LookupChunk000_016
