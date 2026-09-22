import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow017
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow018
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow019
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow020
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow021
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow022
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow023
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow024
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow025
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow026
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow027
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow028
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow029
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow030
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow031
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow032
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow033

namespace Taeyoung.Methods.RootedSOS.S4Classification.LookupChunk017_033

theorem all_lookup_witnesses_valid :
    ∀ index : Fin 17, ∀ left right : Fin 16,
      lookupWitnessValid index left right = true := by
  intro index left right
  exact match hindex : index.1 with
  | 0 => by
      have hi : index = (0 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_017 left right
  | 1 => by
      have hi : index = (1 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_018 left right
  | 2 => by
      have hi : index = (2 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_019 left right
  | 3 => by
      have hi : index = (3 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_020 left right
  | 4 => by
      have hi : index = (4 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_021 left right
  | 5 => by
      have hi : index = (5 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_022 left right
  | 6 => by
      have hi : index = (6 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_023 left right
  | 7 => by
      have hi : index = (7 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_024 left right
  | 8 => by
      have hi : index = (8 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_025 left right
  | 9 => by
      have hi : index = (9 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_026 left right
  | 10 => by
      have hi : index = (10 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_027 left right
  | 11 => by
      have hi : index = (11 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_028 left right
  | 12 => by
      have hi : index = (12 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_029 left right
  | 13 => by
      have hi : index = (13 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_030 left right
  | 14 => by
      have hi : index = (14 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_031 left right
  | 15 => by
      have hi : index = (15 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_032 left right
  | 16 => by
      have hi : index = (16 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_033 left right
  | Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (k))))))))))))))))) => by
      have hlt := index.isLt
      omega

end Taeyoung.Methods.RootedSOS.S4Classification.LookupChunk017_033
