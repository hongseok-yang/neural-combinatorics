import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow00
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow01
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow02
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow03
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow04
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow05
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow06
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow07
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow08
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow09
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow10
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow11
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow12
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow13
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow14
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow15
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow16
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow17
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow18
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow19
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow20
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow21
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow22
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow23
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow24
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow25
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow26
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow27
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow28
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow29
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow30
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow31
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow32
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow33
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow34
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow35
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow36
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow37
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow38
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow39
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow40
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow41
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow42
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow43
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow44
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow45
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow46
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow47
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow48
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow49
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow50
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow51
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow52
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow53
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow54
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow55
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow56
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow57
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow58
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow59
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow60
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow61
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow62
import Taeyoung.Methods.RootedSOS.Atlas43PartitionRow63

/-! # Bounded-memory audit that the 33 raw groups partition all flag pairs -/

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem raw_group_index_checked (a b : Fin 64) :
    claimedRawGroupIndex a b < 33 ∧
      sameRawGroup
        (rawGroupKey (claimedRawGroupIndexFin a b)).1
        (rawGroupKey (claimedRawGroupIndexFin a b)).2 a b ∧
      ∀ other : Fin 33,
        sameRawGroup (rawGroupKey other).1 (rawGroupKey other).2 a b →
          other = claimedRawGroupIndexFin a b := by
  fin_cases a
  · exact raw_group_partition_row_00 b
  · exact raw_group_partition_row_01 b
  · exact raw_group_partition_row_02 b
  · exact raw_group_partition_row_03 b
  · exact raw_group_partition_row_04 b
  · exact raw_group_partition_row_05 b
  · exact raw_group_partition_row_06 b
  · exact raw_group_partition_row_07 b
  · exact raw_group_partition_row_08 b
  · exact raw_group_partition_row_09 b
  · exact raw_group_partition_row_10 b
  · exact raw_group_partition_row_11 b
  · exact raw_group_partition_row_12 b
  · exact raw_group_partition_row_13 b
  · exact raw_group_partition_row_14 b
  · exact raw_group_partition_row_15 b
  · exact raw_group_partition_row_16 b
  · exact raw_group_partition_row_17 b
  · exact raw_group_partition_row_18 b
  · exact raw_group_partition_row_19 b
  · exact raw_group_partition_row_20 b
  · exact raw_group_partition_row_21 b
  · exact raw_group_partition_row_22 b
  · exact raw_group_partition_row_23 b
  · exact raw_group_partition_row_24 b
  · exact raw_group_partition_row_25 b
  · exact raw_group_partition_row_26 b
  · exact raw_group_partition_row_27 b
  · exact raw_group_partition_row_28 b
  · exact raw_group_partition_row_29 b
  · exact raw_group_partition_row_30 b
  · exact raw_group_partition_row_31 b
  · exact raw_group_partition_row_32 b
  · exact raw_group_partition_row_33 b
  · exact raw_group_partition_row_34 b
  · exact raw_group_partition_row_35 b
  · exact raw_group_partition_row_36 b
  · exact raw_group_partition_row_37 b
  · exact raw_group_partition_row_38 b
  · exact raw_group_partition_row_39 b
  · exact raw_group_partition_row_40 b
  · exact raw_group_partition_row_41 b
  · exact raw_group_partition_row_42 b
  · exact raw_group_partition_row_43 b
  · exact raw_group_partition_row_44 b
  · exact raw_group_partition_row_45 b
  · exact raw_group_partition_row_46 b
  · exact raw_group_partition_row_47 b
  · exact raw_group_partition_row_48 b
  · exact raw_group_partition_row_49 b
  · exact raw_group_partition_row_50 b
  · exact raw_group_partition_row_51 b
  · exact raw_group_partition_row_52 b
  · exact raw_group_partition_row_53 b
  · exact raw_group_partition_row_54 b
  · exact raw_group_partition_row_55 b
  · exact raw_group_partition_row_56 b
  · exact raw_group_partition_row_57 b
  · exact raw_group_partition_row_58 b
  · exact raw_group_partition_row_59 b
  · exact raw_group_partition_row_60 b
  · exact raw_group_partition_row_61 b
  · exact raw_group_partition_row_62 b
  · exact raw_group_partition_row_63 b

theorem raw_group_partition_checked (a b : Fin 64) :
    ∃ group : Fin 33,
      sameRawGroup (rawGroupKey group).1 (rawGroupKey group).2 a b ∧
        ∀ other : Fin 33,
          sameRawGroup (rawGroupKey other).1 (rawGroupKey other).2 a b →
            other = group := by
  refine ⟨claimedRawGroupIndexFin a b, ?_, ?_⟩
  · exact (raw_group_index_checked a b).2.1
  · exact (raw_group_index_checked a b).2.2

theorem raw_group_isolated_le_two_checked (row : Fin 33) :
    (rawGroupKey row).2 ≤ 2 := by
  fin_cases row <;> decide

theorem raw_group_core_lt_53_checked (row : Fin 33) :
    (rawGroupKey row).1 < 53 := by
  fin_cases row <;> decide

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
