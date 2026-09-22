import Taeyoung.Methods.RootedSOS.Atlas43RawGroupCellBase

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem exceptional_pair_weight1_05 :
    exceptionalPairWeight₁EncodingValid 5 = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
