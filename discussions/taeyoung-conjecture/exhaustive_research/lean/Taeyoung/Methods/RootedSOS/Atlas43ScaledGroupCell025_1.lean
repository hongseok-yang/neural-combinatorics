import Taeyoung.Methods.RootedSOS.Atlas43RawGroupCellBase

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem scaled_group_cell_025_1 :
    rawGroupScaledCellValid 25 1 = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
