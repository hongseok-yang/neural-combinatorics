import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow051
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow052
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow053
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow054
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow055
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupRow056

namespace Taeyoung.Methods.RootedSOS.S4Classification.LookupChunk051_056

theorem all_lookup_witnesses_valid :
    ∀ index : Fin 6, ∀ left right : Fin 16,
      lookupWitnessValid index left right = true := by
  intro index left right
  exact match hindex : index.1 with
  | 0 => by
      have hi : index = (0 : Fin 6) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_051 left right
  | 1 => by
      have hi : index = (1 : Fin 6) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_052 left right
  | 2 => by
      have hi : index = (2 : Fin 6) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_053 left right
  | 3 => by
      have hi : index = (3 : Fin 6) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_054 left right
  | 4 => by
      have hi : index = (4 : Fin 6) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_055 left right
  | 5 => by
      have hi : index = (5 : Fin 6) := by
        apply Fin.ext
        exact hindex
      simpa [hi] using lookup_witness_row_056 left right
  | Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (k)))))) => by
      have hlt := index.isLt
      omega

end Taeyoung.Methods.RootedSOS.S4Classification.LookupChunk051_056
