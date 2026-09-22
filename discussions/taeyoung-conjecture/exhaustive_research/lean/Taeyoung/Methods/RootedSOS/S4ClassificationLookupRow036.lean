import Taeyoung.Methods.RootedSOS.S4ClassificationLookupChunk034_050Base

namespace Taeyoung.Methods.RootedSOS.S4Classification.LookupChunk034_050

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem lookup_witness_row_036 : ∀ left right : Fin 16,
    lookupWitnessValid 2 left right = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.S4Classification.LookupChunk034_050
