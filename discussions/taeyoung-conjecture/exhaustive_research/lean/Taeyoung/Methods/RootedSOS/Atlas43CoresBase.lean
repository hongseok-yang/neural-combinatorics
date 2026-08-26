import Taeyoung.Methods.RootedSOS.Atlas43FixedDensity
import Taeyoung.Methods.RootedSOS.Atlas43ClassificationData
import Taeyoung.Methods.RootedSOS.House

/-!
# Atlas 43 fixed-core representatives

The certificate groups glued products by unlabelled graph type.  The JSON
therefore carries an explicit five-vertex permutation from every normalized
core to the corresponding Graph Atlas representative, padded with isolated
vertices.  The row modules kernel-check all `64 × 64` witnesses.
-/

namespace Taeyoung.Methods.RootedSOS.Atlas43Cores

open Taeyoung
open Taeyoung.Methods.RootedSOS
open Taeyoung.Methods.RootedSOS.Atlas43ClassificationData
open Taeyoung.Methods.RootedSOS.Atlas43Flags
open Taeyoung.Methods.RootedSOS.Atlas43FixedDensity
open Taeyoung.Methods.RootedSOS.House

private def coreIdRow (a : Fin 64) : Array Nat :=
  coreIds[a.1]?.getD #[]

/-- Graph Atlas id assigned to a glued flag product. -/
def coreId (a b : Fin 64) : Nat :=
  (coreIdRow a)[b.1]?.getD 0

private def corePermutationRow (a : Fin 64) : Array (Array Nat) :=
  corePermutations[a.1]?.getD #[]

private def corePermutationRaw (a b : Fin 64) : Array Nat :=
  (corePermutationRow a)[b.1]?.getD #[]

/-- Old fixed-core vertices read in the Atlas representative's order. -/
def corePermutation (a b : Fin 64) : List (Fin 5) :=
  (corePermutationRaw a b).toList.map fun value ↦
    ⟨value % 5, Nat.mod_lt _ (by decide)⟩

/-- Padded five-vertex adjacency code for a Graph Atlas id. -/
def atlasCoreCode (id : Nat) : AdjacencyCode 5 :=
  ((atlasCodes[id]?.getD #[]).map Array.toList).toList

/-- Padded five-vertex Graph Atlas representative. -/
def atlasCoreGraph (id : Nat) : SimpleGraph (Fin 5) :=
  graphOfCode (atlasCoreCode id)

instance atlasCoreGraph_decidableAdj (id : Nat) :
    DecidableRel (atlasCoreGraph id).Adj := by
  unfold atlasCoreGraph
  infer_instance

/-- The finite proposition checked for every glued flag pair. -/
def coreWitnessValid (a b : Fin 64) : Bool :=
  let l := corePermutation a b
  decide (l.length = 5) && decide l.Nodup && decide (coreId a b < 53) &&
    decide (relabelCodeByList (fixedCoreGraphFin5 (gluedOrdinaryGraph a b)) l =
      atlasCoreCode (coreId a b))

/-- Relabelling from the Lean house labelling to Atlas representative 43. -/
def houseCorePermutation : List (Fin 5) :=
  housePermutation.toList.map fun value ↦
    ⟨value % 5, Nat.mod_lt _ (by decide)⟩

def houseWitnessValid : Bool :=
  decide (houseCorePermutation.length = 5) &&
    decide houseCorePermutation.Nodup &&
      decide (relabelCodeByList houseGraph houseCorePermutation = atlasCoreCode 43)

theorem house_witness_valid : houseWitnessValid = true := by
  decide +kernel

private theorem homDensity_graph_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (H K : SimpleGraph (Fin 5)) [dH : DecidableRel H.Adj]
    [dK : DecidableRel K.Adj]
    (W : Graphon Ω μ) (h : H = K) :
    homDensity H W = homDensity K W := by
  subst K
  have hd : dH = dK := Subsingleton.elim _ _
  subst dK
  rfl

theorem homDensity_house_eq_atlasCore (Ω : Type*) [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) :
    homDensity houseGraph W = homDensity (atlasCoreGraph 43) W := by
  have hv := house_witness_valid
  simp only [houseWitnessValid, Bool.and_eq_true, decide_eq_true_eq] at hv
  have hrel := homDensity_relabelCodeByList houseGraph houseCorePermutation
    hv.1.1 hv.1.2 W
  have hgraph : graphOfCode
      (relabelCodeByList houseGraph houseCorePermutation) = atlasCoreGraph 43 := by
    unfold atlasCoreGraph
    rw [hv.2]
  exact hrel.trans (homDensity_graph_eq _ _ W hgraph)

/-- Any checked pair witness identifies the normalized fixed core with its
padded Atlas representative at the level of homomorphism density. -/
theorem homDensity_fixedCore_eq_atlasCore_of_witness
    (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (a b : Fin 64) (W : Graphon Ω μ) (hv : coreWitnessValid a b = true) :
    homDensity (fixedCoreGraphFin5 (gluedOrdinaryGraph a b)) W =
      homDensity (atlasCoreGraph (coreId a b)) W := by
  simp only [coreWitnessValid, Bool.and_eq_true, decide_eq_true_eq] at hv
  have hrel := homDensity_relabelCodeByList
    (fixedCoreGraphFin5 (gluedOrdinaryGraph a b)) (corePermutation a b)
    hv.1.1.1 hv.1.1.2 W
  have hgraph : graphOfCode (relabelCodeByList
      (fixedCoreGraphFin5 (gluedOrdinaryGraph a b)) (corePermutation a b)) =
      atlasCoreGraph (coreId a b) := by
    unfold atlasCoreGraph
    rw [hv.2]
  exact hrel.trans (homDensity_graph_eq _ _ W hgraph)

end Taeyoung.Methods.RootedSOS.Atlas43Cores
