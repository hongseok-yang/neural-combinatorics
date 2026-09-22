import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow000
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow001
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow002
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow003
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow004
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow005
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow006
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow007
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow008
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow009
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow010
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow011
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow012
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow013
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow014
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow015
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow016

namespace Taeyoung.Methods.RootedSOS.S4Classification.LookupChunk000_016

theorem all_lookup_witnesses_valid :
    ∀ index : Fin 17, ∀ left right : Fin 16,
      lookupWitnessValid index left right = true := by
  intro index left right
  exact match hindex : index.1 with
  | 0 => by
      have hi : index = (0 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_000 left right
  | 1 => by
      have hi : index = (1 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_001 left right
  | 2 => by
      have hi : index = (2 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_002 left right
  | 3 => by
      have hi : index = (3 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_003 left right
  | 4 => by
      have hi : index = (4 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_004 left right
  | 5 => by
      have hi : index = (5 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_005 left right
  | 6 => by
      have hi : index = (6 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_006 left right
  | 7 => by
      have hi : index = (7 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_007 left right
  | 8 => by
      have hi : index = (8 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_008 left right
  | 9 => by
      have hi : index = (9 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_009 left right
  | 10 => by
      have hi : index = (10 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_010 left right
  | 11 => by
      have hi : index = (11 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_011 left right
  | 12 => by
      have hi : index = (12 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_012 left right
  | 13 => by
      have hi : index = (13 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_013 left right
  | 14 => by
      have hi : index = (14 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_014 left right
  | 15 => by
      have hi : index = (15 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_015 left right
  | 16 => by
      have hi : index = (16 : Fin 17) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_016 left right
  | Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (k))))))))))))))))) => by
      have hlt := index.isLt
      omega

end Taeyoung.Methods.RootedSOS.S4Classification.LookupChunk000_016
