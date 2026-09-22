import Taeyoung.Methods.RootedSOS.Atlas43RawGroupCellBase

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem scaled_group_cell_001_2 :
    rawGroupScaledCellValid 1 2 = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
