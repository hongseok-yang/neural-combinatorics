import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow034
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow035
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow036
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow037
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow038
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow039
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow040
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow041
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow042
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow043
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow044
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow045
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow046
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow047
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow048
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow049
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow050

namespace Taeyoung.Methods.RootedSOS.S4Classification.LookupChunk034_050

theorem all_lookup_witnesses_valid :
    ∀ index : Fin 17, ∀ left right : Fin 16,
      lookupWitnessValid index left right = true := by
  intro index left right
  exact match hindex : index.1 with
  | 0 => by
      have hi : index = (0 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_034 left right
  | 1 => by
      have hi : index = (1 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_035 left right
  | 2 => by
      have hi : index = (2 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_036 left right
  | 3 => by
      have hi : index = (3 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_037 left right
  | 4 => by
      have hi : index = (4 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_038 left right
  | 5 => by
      have hi : index = (5 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_039 left right
  | 6 => by
      have hi : index = (6 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_040 left right
  | 7 => by
      have hi : index = (7 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_041 left right
  | 8 => by
      have hi : index = (8 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_042 left right
  | 9 => by
      have hi : index = (9 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_043 left right
  | 10 => by
      have hi : index = (10 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_044 left right
  | 11 => by
      have hi : index = (11 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_045 left right
  | 12 => by
      have hi : index = (12 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_046 left right
  | 13 => by
      have hi : index = (13 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_047 left right
  | 14 => by
      have hi : index = (14 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_048 left right
  | 15 => by
      have hi : index = (15 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_049 left right
  | 16 => by
      have hi : index = (16 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_050 left right
  | Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (k))))))))))))))))) => by
      have hlt := index.isLt
      omega

end Taeyoung.Methods.RootedSOS.S4Classification.LookupChunk034_050
