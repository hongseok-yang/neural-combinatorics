import Taeyoung.Methods.RootedSOS.Atlas43RawGroupCellBase

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem raw_group_partition_row_63 :
    ∀ b : Fin 64,
      claimedRawGroupIndex 63 b < 33 ∧
      sameRawGroup
        (rawGroupKey (claimedRawGroupIndexFin 63 b)).1
        (rawGroupKey (claimedRawGroupIndexFin 63 b)).2 63 b ∧
        ∀ other : Fin 33,
          sameRawGroup (rawGroupKey other).1 (rawGroupKey other).2 63 b →
            other = claimedRawGroupIndexFin 63 b := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
