import Taeyoung.Methods.RootedSOS.Atlas43CoefficientBase

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem block0_witness_row_024 :
    block₀WitnessRowValid 24 = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
