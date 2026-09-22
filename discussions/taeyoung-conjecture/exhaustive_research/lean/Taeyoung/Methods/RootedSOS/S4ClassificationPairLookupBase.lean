import Taeyoung.Methods.RootedSOS.S4ClassificationGroupBase
import Mathlib.Data.Nat.Bitwise

/-! Reduction of raw S4 flag pairs to the compressed graph lookup. -/

namespace Taeyoung.Methods.RootedSOS.S4Classification

set_option maxHeartbeats 40000000

def pairLabelUnion (a b : Fin 352) : Nat :=
  (S4Flags.basisIndex a / 16) ||| (S4Flags.basisIndex b / 16)

def pairLeftBranch (a : Fin 352) : Nat := S4Flags.basisIndex a % 16
def pairRightBranch (b : Fin 352) : Nat := S4Flags.basisIndex b % 16

def pairLookupValid (a b : Fin 352) : Bool :=
  decide (adjacencyCode (S4Flags.gluedGraph a b) =
    adjacencyCode
      (lookupGraph (pairLabelUnion a b) (pairLeftBranch a) (pairRightBranch b)))

theorem flagBranchNeighbors_eq_lookup (a : Fin 352) :
    S4Flags.flagBranchNeighbors a =
      S4Flags.branchNeighborsFromMask (S4Flags.basisIndex a % 16) := by
  rfl

theorem flagLabelGraph_sup_eq_lookup (a b : Fin 352) :
    S4Flags.flagLabelGraph a ⊔ S4Flags.flagLabelGraph b =
      S4Flags.labelGraphFromMask
        ((S4Flags.basisIndex a / 16) ||| (S4Flags.basisIndex b / 16)) := by
  change
    S4Flags.labelGraphFromMask (S4Flags.basisIndex a / 16) ⊔
        S4Flags.labelGraphFromMask (S4Flags.basisIndex b / 16) = _
  exact S4Flags.labelGraphFromMask_sup _ _

theorem gluedGraph_eq_lookupGraph (a b : Fin 352) :
    S4Flags.gluedGraph a b =
      lookupGraph (pairLabelUnion a b) (pairLeftBranch a) (pairRightBranch b) := by
  unfold S4Flags.gluedGraph lookupGraph gluedRootedFlagGraph
  simp only [sup_bot_eq]
  congr 1
  · exact flagLabelGraph_sup_eq_lookup a b

end Taeyoung.Methods.RootedSOS.S4Classification
