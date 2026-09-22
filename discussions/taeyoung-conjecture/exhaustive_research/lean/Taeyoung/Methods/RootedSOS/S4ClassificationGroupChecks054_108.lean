import Taeyoung.Methods.RootedSOS.S4ClassificationGroupBase

namespace Taeyoung.Methods.RootedSOS.S4Classification

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem group_data_valid_054_108 :
    ∀ index : Fin 55,
      groupDataValid ⟨54 + index.1, by omega⟩ = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.S4Classification
