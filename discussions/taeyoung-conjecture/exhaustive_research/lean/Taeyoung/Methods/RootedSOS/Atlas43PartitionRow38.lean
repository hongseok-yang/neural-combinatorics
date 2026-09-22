import Taeyoung.Methods.RootedSOS.Atlas43RawGroupCellBase

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem raw_group_partition_row_38 :
    ∀ b : Fin 64,
      claimedRawGroupIndex 38 b < 33 ∧
      sameRawGroup
        (rawGroupKey (claimedRawGroupIndexFin 38 b)).1
        (rawGroupKey (claimedRawGroupIndexFin 38 b)).2 38 b ∧
        ∀ other : Fin 33,
          sameRawGroup (rawGroupKey other).1 (rawGroupKey other).2 38 b →
            other = claimedRawGroupIndexFin 38 b := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
