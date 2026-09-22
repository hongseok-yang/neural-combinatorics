import Taeyoung.Methods.RootedSOS.Atlas43RawGroupCellBase

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem scaled_correction1_row_024 :
    ∀ j : Fin 48, stagedCorrectionRational₁Valid 24 j = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
