import Taeyoung.Methods.RootedSOS.Atlas43RawGroupCellBase

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem scaled_correction0_row_031 :
    ∀ j : Fin 107, stagedCorrectionRational₀Valid 31 j = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
