import Taeyoung.Methods.RootedSOS.Atlas43RawGroupCellBase

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem scaled_correction0_row_103 :
    ∀ j : Fin 107, stagedCorrectionRational₀Valid 103 j = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
