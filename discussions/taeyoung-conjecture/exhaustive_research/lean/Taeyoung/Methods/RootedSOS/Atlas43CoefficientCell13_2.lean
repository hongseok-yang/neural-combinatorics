import Taeyoung.Methods.RootedSOS.Atlas43RawGroups

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem coefficient_cell_13_2 :
    (certificateCoefficient 13 2 ==
      targetCoefficient 13 2) = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
