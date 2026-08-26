import Taeyoung.Methods.RootedSOS.Atlas43FixedDensityRows00
import Taeyoung.Methods.RootedSOS.Atlas43FixedDensityRows08
import Taeyoung.Methods.RootedSOS.Atlas43FixedDensityRows16
import Taeyoung.Methods.RootedSOS.Atlas43FixedDensityRows24
import Taeyoung.Methods.RootedSOS.Atlas43FixedDensityRows32
import Taeyoung.Methods.RootedSOS.Atlas43FixedDensityRows40
import Taeyoung.Methods.RootedSOS.Atlas43FixedDensityRows48
import Taeyoung.Methods.RootedSOS.Atlas43FixedDensityRows56

/-!
# Fixed-density normalization for the Atlas 43 products

This finite audit checks that every one of the `64 × 64` glued products has
at most two isolated edge components and that the executable decomposition
finds a relabelling putting them in the standard final positions.
-/

namespace Taeyoung.Methods.RootedSOS.Atlas43FixedDensity

open Taeyoung.Methods.RootedSOS
open Taeyoung.Methods.RootedSOS.Atlas43Flags

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem all_decompositions_valid :
    ∀ a b : Fin 64, decompositionValid (gluedOrdinaryGraph a b) = true := by
  intro a b
  by_cases h0 : a.1 < 8
  · let k : Fin 8 := ⟨a.1 - 0, by omega⟩
    let a' : Fin 64 := ⟨0 + k.1, by omega⟩
    have ha : a' = a := by
      apply Fin.ext
      dsimp [a', k]
      omega
    rw [← ha]
    exact decompositions_rows_00 k b
  by_cases h1 : a.1 < 16
  · let k : Fin 8 := ⟨a.1 - 8, by omega⟩
    let a' : Fin 64 := ⟨8 + k.1, by omega⟩
    have ha : a' = a := by
      apply Fin.ext
      dsimp [a', k]
      omega
    rw [← ha]
    exact decompositions_rows_08 k b
  by_cases h2 : a.1 < 24
  · let k : Fin 8 := ⟨a.1 - 16, by omega⟩
    let a' : Fin 64 := ⟨16 + k.1, by omega⟩
    have ha : a' = a := by
      apply Fin.ext
      dsimp [a', k]
      omega
    rw [← ha]
    exact decompositions_rows_16 k b
  by_cases h3 : a.1 < 32
  · let k : Fin 8 := ⟨a.1 - 24, by omega⟩
    let a' : Fin 64 := ⟨24 + k.1, by omega⟩
    have ha : a' = a := by
      apply Fin.ext
      dsimp [a', k]
      omega
    rw [← ha]
    exact decompositions_rows_24 k b
  by_cases h4 : a.1 < 40
  · let k : Fin 8 := ⟨a.1 - 32, by omega⟩
    let a' : Fin 64 := ⟨32 + k.1, by omega⟩
    have ha : a' = a := by
      apply Fin.ext
      dsimp [a', k]
      omega
    rw [← ha]
    exact decompositions_rows_32 k b
  by_cases h5 : a.1 < 48
  · let k : Fin 8 := ⟨a.1 - 40, by omega⟩
    let a' : Fin 64 := ⟨40 + k.1, by omega⟩
    have ha : a' = a := by
      apply Fin.ext
      dsimp [a', k]
      omega
    rw [← ha]
    exact decompositions_rows_40 k b
  by_cases h6 : a.1 < 56
  · let k : Fin 8 := ⟨a.1 - 48, by omega⟩
    let a' : Fin 64 := ⟨48 + k.1, by omega⟩
    have ha : a' = a := by
      apply Fin.ext
      dsimp [a', k]
      omega
    rw [← ha]
    exact decompositions_rows_48 k b
  · let k : Fin 8 := ⟨a.1 - 56, by omega⟩
    let a' : Fin 64 := ⟨56 + k.1, by omega⟩
    have ha : a' = a := by
      apply Fin.ext
      dsimp [a', k]
      omega
    rw [← ha]
    exact decompositions_rows_56 k b

end Taeyoung.Methods.RootedSOS.Atlas43FixedDensity
