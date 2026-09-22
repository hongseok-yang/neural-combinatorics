import Taeyoung.Methods.RootedSOS.Atlas43RawGroups

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem coefficient_cell_16_2 :
    (certificateCoefficient 16 2 ==
      targetCoefficient 16 2) = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
