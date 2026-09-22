import Taeyoung.Methods.RootedSOS.S4ClassificationLookupChunk017_033Base

namespace Taeyoung.Methods.RootedSOS.S4Classification.LookupChunk017_033

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem lookup_witness_row_032 : ∀ left right : Fin 16,
    lookupWitnessValid 15 left right = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.S4Classification.LookupChunk017_033
