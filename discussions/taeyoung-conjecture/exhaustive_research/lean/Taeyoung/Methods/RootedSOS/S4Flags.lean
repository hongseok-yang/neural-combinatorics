import Taeyoung.Methods.RootedSOS.FlagGram
import Mathlib.Data.Nat.Bitwise

/-!
# The common four-root, one-branch flag basis

All exact S4 interval certificates in this project use the same 352 raw
flags: every branch-to-label pattern and every labelled graph with at most two
of the six possible labelled edges.  The order agrees with the Python
certificate generator: the full ten-edge mask is `16 * labelMask + branchMask`
and accepted masks are retained in increasing order.
-/

open Finset

namespace Taeyoung.Methods.RootedSOS.S4Flags

open Taeyoung Taeyoung.Methods.RootedSOS

set_option maxHeartbeats 40000000

private def singletonIf {α : Type*} [DecidableEq α]
    (b : Bool) (x : α) : Finset α :=
  if b then {x} else ∅

private theorem singletonIf_or {α : Type*} [DecidableEq α]
    (left right : Bool) (x : α) :
    singletonIf (left || right) x =
      singletonIf left x ∪ singletonIf right x := by
  cases left <;> cases right <;> simp [singletonIf]

/-- Six-bit label masks having Hamming weight at most two. -/
def allowedLabelMasks : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12,
    16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48]

/-- Full ten-edge mask corresponding to a local basis index. -/
def basisIndex (a : Fin 352) : Nat :=
  16 * (allowedLabelMasks[a.1 / 16]?).getD 64 + a.1 % 16

/-- Label edges selected by a six-bit mask. -/
def labelEdgesFromMask (mask : Nat) : Finset (Sym2 (Fin 4)) :=
  singletonIf (mask.testBit 0) s(0, 1) ∪
    singletonIf (mask.testBit 1) s(0, 2) ∪
    singletonIf (mask.testBit 2) s(0, 3) ∪
    singletonIf (mask.testBit 3) s(1, 2) ∪
    singletonIf (mask.testBit 4) s(1, 3) ∪
    singletonIf (mask.testBit 5) s(2, 3)

/-- Branch neighbours selected by a four-bit mask. -/
def branchNeighborsFromMask (mask : Nat) : Finset (Fin 4) :=
  singletonIf (mask.testBit 0) 0 ∪
    singletonIf (mask.testBit 1) 1 ∪
    singletonIf (mask.testBit 2) 2 ∪
    singletonIf (mask.testBit 3) 3

/-- Label-edge part of a raw S4 flag. -/
def flagLabelEdges (a : Fin 352) : Finset (Sym2 (Fin 4)) :=
  labelEdgesFromMask (basisIndex a / 16)

/-- Branch-neighbour part of a raw S4 flag. -/
def flagBranchNeighbors (a : Fin 352) : Finset (Fin 4) :=
  branchNeighborsFromMask (basisIndex a % 16)

/-- Label graph of a raw S4 flag. -/
def flagLabelGraph (a : Fin 352) : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet ↑(flagLabelEdges a)

/-- Label graph selected directly by a mask. -/
def labelGraphFromMask (mask : Nat) : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet ↑(labelEdgesFromMask mask)

theorem labelEdgesFromMask_union (left right : Nat) :
    labelEdgesFromMask left ∪ labelEdgesFromMask right =
      labelEdgesFromMask (left ||| right) := by
  unfold labelEdgesFromMask
  simp only [Nat.testBit_lor, singletonIf_or]
  ac_rfl

instance flagLabelGraph_decidableAdj (a : Fin 352) :
    DecidableRel (flagLabelGraph a).Adj := by
  unfold flagLabelGraph
  infer_instance

instance labelGraphFromMask_decidableAdj (mask : Nat) :
    DecidableRel (labelGraphFromMask mask).Adj := by
  unfold labelGraphFromMask
  infer_instance

theorem labelGraphFromMask_sup (left right : Nat) :
    labelGraphFromMask left ⊔ labelGraphFromMask right =
      labelGraphFromMask (left ||| right) := by
  ext i j
  simp only [labelGraphFromMask, SimpleGraph.sup_adj,
    SimpleGraph.fromEdgeSet_adj]
  rw [← labelEdgesFromMask_union]
  simp only [Finset.coe_union, Set.mem_union]
  tauto

theorem flagLabelGraph_edgeFinset_all :
    ∀ a : Fin 352, (flagLabelGraph a).edgeFinset = flagLabelEdges a := by
  decide +kernel

/-- The ordinary six-vertex graph produced by one ordered raw flag pair. -/
def gluedGraph (a b : Fin 352) : SimpleGraph (Fin 6) :=
  gluedRootedFlagGraph (flagLabelGraph a) (flagLabelGraph b)
    (flagBranchNeighbors a) (flagBranchNeighbors b)

instance gluedGraph_decidableAdj (a b : Fin 352) :
    DecidableRel (gluedGraph a b).Adj := by
  unfold gluedGraph
  infer_instance

end Taeyoung.Methods.RootedSOS.S4Flags
