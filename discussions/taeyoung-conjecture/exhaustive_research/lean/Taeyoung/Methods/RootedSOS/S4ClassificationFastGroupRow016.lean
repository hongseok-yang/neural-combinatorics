import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupBase

namespace Taeyoung.Methods.RootedSOS.S4Classification

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem fast_group_row_016 : ∀ left right : Fin 16,
    fastGroupValid 16 left right = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.S4Classification
