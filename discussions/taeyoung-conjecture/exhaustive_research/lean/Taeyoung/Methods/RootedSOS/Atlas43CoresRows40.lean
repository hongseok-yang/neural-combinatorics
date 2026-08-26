import Taeyoung.Methods.RootedSOS.Atlas43CoresBase

namespace Taeyoung.Methods.RootedSOS.Atlas43Cores

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem core_witnesses_rows_40 : ∀ (a : Fin 8) (b : Fin 64),
    coreWitnessValid ⟨40 + a.1, by omega⟩ b = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43Cores
