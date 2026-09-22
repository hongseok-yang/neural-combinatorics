import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow000
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow001
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow002
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow003
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow004
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow005
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow006
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow007
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow008
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow009
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow010
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow011
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow012
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow013
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow014
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow015
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow016
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow017
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow018
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow019
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow020
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow021
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow022
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow023
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow024
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow025
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow026
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow027
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow028
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow029
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow030
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow031
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow032
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow033
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow034
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow035
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow036
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow037
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow038
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow039
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow040
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow041
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow042
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow043
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow044
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow045
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow046
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow047
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow048
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow049
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow050
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow051
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow052
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow053
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow054
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow055
import Taeyoung.Methods.RootedSOS.S4ClassificationFastGroupRow056

namespace Taeyoung.Methods.RootedSOS.S4Classification

theorem all_fast_groups_valid :
    ∀ index : Fin 57, ∀ left right : Fin 16,
      fastGroupValid index left right = true := by
  intro index left right
  exact match hindex : index.1 with
  | 0 => by
      have hi : index = (0 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_000 left right
  | 1 => by
      have hi : index = (1 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_001 left right
  | 2 => by
      have hi : index = (2 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_002 left right
  | 3 => by
      have hi : index = (3 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_003 left right
  | 4 => by
      have hi : index = (4 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_004 left right
  | 5 => by
      have hi : index = (5 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_005 left right
  | 6 => by
      have hi : index = (6 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_006 left right
  | 7 => by
      have hi : index = (7 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_007 left right
  | 8 => by
      have hi : index = (8 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_008 left right
  | 9 => by
      have hi : index = (9 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_009 left right
  | 10 => by
      have hi : index = (10 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_010 left right
  | 11 => by
      have hi : index = (11 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_011 left right
  | 12 => by
      have hi : index = (12 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_012 left right
  | 13 => by
      have hi : index = (13 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_013 left right
  | 14 => by
      have hi : index = (14 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_014 left right
  | 15 => by
      have hi : index = (15 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_015 left right
  | 16 => by
      have hi : index = (16 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_016 left right
  | 17 => by
      have hi : index = (17 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_017 left right
  | 18 => by
      have hi : index = (18 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_018 left right
  | 19 => by
      have hi : index = (19 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_019 left right
  | 20 => by
      have hi : index = (20 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_020 left right
  | 21 => by
      have hi : index = (21 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_021 left right
  | 22 => by
      have hi : index = (22 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_022 left right
  | 23 => by
      have hi : index = (23 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_023 left right
  | 24 => by
      have hi : index = (24 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_024 left right
  | 25 => by
      have hi : index = (25 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_025 left right
  | 26 => by
      have hi : index = (26 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_026 left right
  | 27 => by
      have hi : index = (27 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_027 left right
  | 28 => by
      have hi : index = (28 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_028 left right
  | 29 => by
      have hi : index = (29 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_029 left right
  | 30 => by
      have hi : index = (30 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_030 left right
  | 31 => by
      have hi : index = (31 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_031 left right
  | 32 => by
      have hi : index = (32 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_032 left right
  | 33 => by
      have hi : index = (33 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_033 left right
  | 34 => by
      have hi : index = (34 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_034 left right
  | 35 => by
      have hi : index = (35 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_035 left right
  | 36 => by
      have hi : index = (36 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_036 left right
  | 37 => by
      have hi : index = (37 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_037 left right
  | 38 => by
      have hi : index = (38 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_038 left right
  | 39 => by
      have hi : index = (39 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_039 left right
  | 40 => by
      have hi : index = (40 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_040 left right
  | 41 => by
      have hi : index = (41 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_041 left right
  | 42 => by
      have hi : index = (42 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_042 left right
  | 43 => by
      have hi : index = (43 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_043 left right
  | 44 => by
      have hi : index = (44 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_044 left right
  | 45 => by
      have hi : index = (45 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_045 left right
  | 46 => by
      have hi : index = (46 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_046 left right
  | 47 => by
      have hi : index = (47 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_047 left right
  | 48 => by
      have hi : index = (48 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_048 left right
  | 49 => by
      have hi : index = (49 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_049 left right
  | 50 => by
      have hi : index = (50 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_050 left right
  | 51 => by
      have hi : index = (51 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_051 left right
  | 52 => by
      have hi : index = (52 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_052 left right
  | 53 => by
      have hi : index = (53 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_053 left right
  | 54 => by
      have hi : index = (54 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_054 left right
  | 55 => by
      have hi : index = (55 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_055 left right
  | 56 => by
      have hi : index = (56 : Fin 57) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using fast_group_row_056 left right
  | Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (k))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => by
      have hlt := index.isLt
      omega

end Taeyoung.Methods.RootedSOS.S4Classification
