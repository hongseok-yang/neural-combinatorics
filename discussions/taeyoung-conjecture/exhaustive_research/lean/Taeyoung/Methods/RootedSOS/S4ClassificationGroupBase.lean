import Taeyoung.Methods.RootedSOS.S4YoungData
import Taeyoung.Methods.RootedSOS.S4Flags
import Taeyoung.Methods.RootedSOS.GraphCanonical
import Taeyoung.Foundation.DisjointUnion
import Taeyoung.Methods.RootedSOS.S4ClassificationGroups000_053Data
import Taeyoung.Methods.RootedSOS.S4ClassificationGroups054_108Data
import Taeyoung.Methods.RootedSOS.S4ClassificationGroups109_142Data

/-! Executable standard representatives for the 143 S4 graph groups. -/

namespace Taeyoung.Methods.RootedSOS.S4Classification

open Taeyoung Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def keyRaw (row : Nat) : Array Nat :=
  if row < 54 then
    (S4ClassificationGroups000_053Data.keys[row - 0]?).getD #[]
  else if row < 109 then
    (S4ClassificationGroups054_108Data.keys[row - 54]?).getD #[]
  else if row < 143 then
    (S4ClassificationGroups109_142Data.keys[row - 109]?).getD #[]
  else #[]

private def core6Raw (row : Nat) : Array (Array Bool) :=
  if row < 54 then
    (S4ClassificationGroups000_053Data.core6[row - 0]?).getD #[]
  else if row < 109 then
    (S4ClassificationGroups054_108Data.core6[row - 54]?).getD #[]
  else if row < 143 then
    (S4ClassificationGroups109_142Data.core6[row - 109]?).getD #[]
  else #[]

private def core4Raw (row : Nat) : Array (Array Bool) :=
  if row < 54 then
    (S4ClassificationGroups000_053Data.core4[row - 0]?).getD #[]
  else if row < 109 then
    (S4ClassificationGroups054_108Data.core4[row - 54]?).getD #[]
  else if row < 143 then
    (S4ClassificationGroups109_142Data.core4[row - 109]?).getD #[]
  else #[]

private def core2Raw (row : Nat) : Array (Array Bool) :=
  if row < 54 then
    (S4ClassificationGroups000_053Data.core2[row - 0]?).getD #[]
  else if row < 109 then
    (S4ClassificationGroups054_108Data.core2[row - 54]?).getD #[]
  else if row < 143 then
    (S4ClassificationGroups109_142Data.core2[row - 109]?).getD #[]
  else #[]

private def standardRaw (row : Nat) : Array (Array Bool) :=
  if row < 54 then
    (S4ClassificationGroups000_053Data.standard[row - 0]?).getD #[]
  else if row < 109 then
    (S4ClassificationGroups054_108Data.standard[row - 54]?).getD #[]
  else if row < 143 then
    (S4ClassificationGroups109_142Data.standard[row - 109]?).getD #[]
  else #[]

private def codeFromArray {n : Nat} (data : Array (Array Bool)) : AdjacencyCode n :=
  data.toList.map Array.toList

def groupKey (row : Fin 143) : Nat × Nat :=
  ((keyRaw row.1)[0]?.getD 0, (keyRaw row.1)[1]?.getD 0)

def coreCode6 (row : Fin 143) : AdjacencyCode 6 :=
  codeFromArray (core6Raw row.1)
def coreCode4 (row : Fin 143) : AdjacencyCode 4 :=
  codeFromArray (core4Raw row.1)
def coreCode2 (row : Fin 143) : AdjacencyCode 2 :=
  codeFromArray (core2Raw row.1)
def standardCode (row : Fin 143) : AdjacencyCode 6 :=
  codeFromArray (standardRaw row.1)

def coreGraph6 (row : Fin 143) : SimpleGraph (Fin 6) :=
  graphOfCode (coreCode6 row)
def coreGraph4 (row : Fin 143) : SimpleGraph (Fin 4) :=
  graphOfCode (coreCode4 row)
def coreGraph2 (row : Fin 143) : SimpleGraph (Fin 2) :=
  graphOfCode (coreCode2 row)

instance (row : Fin 143) : DecidableRel (coreGraph6 row).Adj := by
  unfold coreGraph6
  infer_instance
instance (row : Fin 143) : DecidableRel (coreGraph4 row).Adj := by
  unfold coreGraph4
  infer_instance
instance (row : Fin 143) : DecidableRel (coreGraph2 row).Adj := by
  unfold coreGraph2
  infer_instance

def standardGraph (row : Fin 143) : SimpleGraph (Fin 6) :=
  match (groupKey row).2 with
  | 0 => coreGraph6 row
  | 1 => disjointUnion (coreGraph4 row) (⊤ : SimpleGraph (Fin 2))
  | 2 => disjointUnion
      (disjointUnion (coreGraph2 row) (⊤ : SimpleGraph (Fin 2)))
      (⊤ : SimpleGraph (Fin 2))
  | _ => disjointUnion
      (disjointUnion (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 2)))
      (⊤ : SimpleGraph (Fin 2))

instance (row : Fin 143) : DecidableRel (standardGraph row).Adj := by
  unfold standardGraph
  split <;> infer_instance

private def singletonIf {α : Type*} [DecidableEq α]
    (condition : Bool) (value : α) : Finset α :=
  if condition then {value} else ∅

def labelEdgesFromMask (mask : Nat) : Finset (Sym2 (Fin 4)) :=
  singletonIf (mask.testBit 0) s(0, 1) ∪
    singletonIf (mask.testBit 1) s(0, 2) ∪
    singletonIf (mask.testBit 2) s(0, 3) ∪
    singletonIf (mask.testBit 3) s(1, 2) ∪
    singletonIf (mask.testBit 4) s(1, 3) ∪
    singletonIf (mask.testBit 5) s(2, 3)

def neighborsFromMask (mask : Nat) : Finset (Fin 4) :=
  singletonIf (mask.testBit 0) 0 ∪
    singletonIf (mask.testBit 1) 1 ∪
    singletonIf (mask.testBit 2) 2 ∪
    singletonIf (mask.testBit 3) 3

def labelGraphFromMask (mask : Nat) : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet ↑(labelEdgesFromMask mask)

instance (mask : Nat) : DecidableRel (labelGraphFromMask mask).Adj := by
  unfold labelGraphFromMask
  infer_instance

def lookupGraph (labelUnion leftBranch rightBranch : Nat) :
    SimpleGraph (Fin 6) :=
  gluedRootedFlagGraph (S4Flags.labelGraphFromMask labelUnion)
    (⊥ : SimpleGraph (Fin 4))
    (S4Flags.branchNeighborsFromMask leftBranch)
    (S4Flags.branchNeighborsFromMask rightBranch)

instance (labelUnion leftBranch rightBranch : Nat) :
    DecidableRel (lookupGraph labelUnion leftBranch rightBranch).Adj := by
  unfold lookupGraph
  infer_instance

def groupDataValid (row : Fin 143) : Bool :=
  groupKey row == S4YoungData.rawGroupKey row &&
  decide ((groupKey row).2 ≤ 3) &&
  decide (adjacencyCode (standardGraph row) = standardCode row) &&
  match (groupKey row).2 with
  | 0 => true
  | 1 => decide (adjacencyCode (coreGraph6 row) =
      adjacencyCode ((coreGraph4 row).map (Fin.castAdd 2)))
  | 2 => decide (adjacencyCode (coreGraph6 row) =
      adjacencyCode ((coreGraph2 row).map (Fin.castAdd 4)))
  | 3 => decide (adjacencyCode (coreGraph6 row) =
      adjacencyCode (⊥ : SimpleGraph (Fin 6)))
  | _ => false

end Taeyoung.Methods.RootedSOS.S4Classification
