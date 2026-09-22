import Taeyoung.Methods.RootedSOS.S4ClassificationPairLookupBase
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupChunk000_016Base
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupChunk017_033Base
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupChunk034_050Base
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupChunk051_056Base

/-! Lightweight global definitions for the four split S4 lookup chunks. -/

namespace Taeyoung.Methods.RootedSOS.S4Classification

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

def unionIndexTable : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 0,
    31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 0,
    46, 47, 48, 49, 50, 51, 52, 0, 53, 54, 55, 0, 56, 0, 0, 0]

def unionIndex (mask : Nat) : Fin 57 :=
  ⟨((unionIndexTable[mask]?).getD 0) % 57, Nat.mod_lt _ (by decide)⟩

def unionMask (index : Fin 57) : Nat :=
  if h₀ : index.1 < 17 then
    LookupChunk000_016.labelUnion ⟨index.1, h₀⟩
  else if h₁ : index.1 < 34 then
    LookupChunk017_033.labelUnion ⟨index.1 - 17, by omega⟩
  else if h₂ : index.1 < 51 then
    LookupChunk034_050.labelUnion ⟨index.1 - 34, by omega⟩
  else
    LookupChunk051_056.labelUnion ⟨index.1 - 51, by omega⟩

def witnessGroup (index : Fin 57) (left right : Fin 16) : Fin 143 :=
  if h₀ : index.1 < 17 then
    LookupChunk000_016.witnessGroup ⟨index.1, h₀⟩ left right
  else if h₁ : index.1 < 34 then
    LookupChunk017_033.witnessGroup ⟨index.1 - 17, by omega⟩ left right
  else if h₂ : index.1 < 51 then
    LookupChunk034_050.witnessGroup ⟨index.1 - 34, by omega⟩ left right
  else
    LookupChunk051_056.witnessGroup ⟨index.1 - 51, by omega⟩ left right

def witnessPermutation (index : Fin 57) (left right : Fin 16) :
    List (Fin 6) :=
  if h₀ : index.1 < 17 then
    LookupChunk000_016.witnessPermutation ⟨index.1, h₀⟩ left right
  else if h₁ : index.1 < 34 then
    LookupChunk017_033.witnessPermutation ⟨index.1 - 17, by omega⟩ left right
  else if h₂ : index.1 < 51 then
    LookupChunk034_050.witnessPermutation ⟨index.1 - 34, by omega⟩ left right
  else
    LookupChunk051_056.witnessPermutation ⟨index.1 - 51, by omega⟩ left right

def allowedLabelMask (index : Fin 22) : Nat :=
  (S4Flags.allowedLabelMasks[index.1]?).getD 64

theorem allowed_label_union_selects (left right : Fin 22) :
    unionMask (unionIndex (allowedLabelMask left ||| allowedLabelMask right)) =
      allowedLabelMask left ||| allowedLabelMask right := by
  decide +kernel +revert

theorem allowedLabelMask_lt (index : Fin 22) : allowedLabelMask index < 64 := by
  decide +kernel +revert

def flagLabelSlot (a : Fin 352) : Fin 22 :=
  ⟨a.1 / 16, by omega⟩

theorem basisIndex_div_sixteen (a : Fin 352) :
    S4Flags.basisIndex a / 16 = allowedLabelMask (flagLabelSlot a) := by
  change
    (16 * (S4Flags.allowedLabelMasks[a.1 / 16]?).getD 64 + a.1 % 16) / 16 =
      (S4Flags.allowedLabelMasks[a.1 / 16]?).getD 64
  have hmod : a.1 % 16 < 16 := Nat.mod_lt _ (by decide)
  omega

def pairUnionIndex (a b : Fin 352) : Fin 57 :=
  unionIndex (pairLabelUnion a b)

def pairLeftBranchFin (a : Fin 352) : Fin 16 :=
  ⟨pairLeftBranch a, by
    unfold pairLeftBranch
    exact Nat.mod_lt _ (by decide)⟩

def pairRightBranchFin (b : Fin 352) : Fin 16 :=
  ⟨pairRightBranch b, by
    unfold pairRightBranch
    exact Nat.mod_lt _ (by decide)⟩

def pairWitnessGroup (a b : Fin 352) : Fin 143 :=
  witnessGroup (pairUnionIndex a b) (pairLeftBranchFin a) (pairRightBranchFin b)

def pairWitnessPermutation (a b : Fin 352) : List (Fin 6) :=
  witnessPermutation (pairUnionIndex a b)
    (pairLeftBranchFin a) (pairRightBranchFin b)

theorem pair_union_mask (a b : Fin 352) :
    unionMask (pairUnionIndex a b) = pairLabelUnion a b := by
  rw [pairUnionIndex, pairLabelUnion, basisIndex_div_sixteen,
    basisIndex_div_sixteen]
  exact allowed_label_union_selects (flagLabelSlot a) (flagLabelSlot b)

end Taeyoung.Methods.RootedSOS.S4Classification
