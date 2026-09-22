import Taeyoung.Methods.RootedSOS.Atlas43RawGroups

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem coefficient_cell_22_1 :
    (certificateCoefficient 22 1 ==
      targetCoefficient 22 1) = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
