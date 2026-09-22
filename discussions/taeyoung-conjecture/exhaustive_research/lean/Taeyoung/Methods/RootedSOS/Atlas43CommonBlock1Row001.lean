import Taeyoung.Methods.RootedSOS.Atlas43CoefficientBase

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem block1_witness_row_001 :
    block₁WitnessRowValid 1 = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
