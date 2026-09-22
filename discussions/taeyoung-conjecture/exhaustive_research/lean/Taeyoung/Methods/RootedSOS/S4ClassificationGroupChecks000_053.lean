import Taeyoung.Methods.RootedSOS.S4ClassificationGroupBase

namespace Taeyoung.Methods.RootedSOS.S4Classification

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem group_data_valid_000_053 :
    ∀ index : Fin 54,
      groupDataValid ⟨0 + index.1, by omega⟩ = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.S4Classification
