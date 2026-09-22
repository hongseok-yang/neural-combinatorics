import Taeyoung.Methods.RootedSOS.S4ClassificationGroupBase

namespace Taeyoung.Methods.RootedSOS.S4Classification

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem group_data_valid_109_142 :
    ∀ index : Fin 34,
      groupDataValid ⟨109 + index.1, by omega⟩ = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.S4Classification
