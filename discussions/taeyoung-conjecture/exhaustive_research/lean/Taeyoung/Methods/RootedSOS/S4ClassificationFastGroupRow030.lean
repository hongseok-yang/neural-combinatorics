import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupBase

namespace Taeyoung.Methods.RootedSOS.S4Classification

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem fast_group_row_030 : ∀ left right : Fin 16,
    fastGroupValid 30 left right = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.S4Classification
