import Taeyoung.Methods.RootedSOS.Atlas43CoefficientBase

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem block0_witness_row_080 :
    block₀WitnessRowValid 80 = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
