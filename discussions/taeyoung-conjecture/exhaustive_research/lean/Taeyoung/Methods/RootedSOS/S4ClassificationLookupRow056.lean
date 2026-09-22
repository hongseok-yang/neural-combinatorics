import Taeyoung.Methods.RootedSOS.S4ClassificationLookupChunk051_056Base

namespace Taeyoung.Methods.RootedSOS.S4Classification.LookupChunk051_056

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem lookup_witness_row_056 : ∀ left right : Fin 16,
    lookupWitnessValid 5 left right = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.S4Classification.LookupChunk051_056
