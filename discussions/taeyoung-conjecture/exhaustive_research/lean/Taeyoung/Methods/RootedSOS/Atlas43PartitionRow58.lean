import Taeyoung.Methods.RootedSOS.Atlas43RawGroupCellBase

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem raw_group_partition_row_58 :
    ∀ b : Fin 64,
      claimedRawGroupIndex 58 b < 33 ∧
      sameRawGroup
        (rawGroupKey (claimedRawGroupIndexFin 58 b)).1
        (rawGroupKey (claimedRawGroupIndexFin 58 b)).2 58 b ∧
        ∀ other : Fin 33,
          sameRawGroup (rawGroupKey other).1 (rawGroupKey other).2 58 b →
            other = claimedRawGroupIndexFin 58 b := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
