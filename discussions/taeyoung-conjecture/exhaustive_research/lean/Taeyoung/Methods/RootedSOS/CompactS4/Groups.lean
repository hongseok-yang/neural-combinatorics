import Taeyoung.Methods.RootedSOS.CompactS4.GroupsData
import Taeyoung.Methods.RootedSOS.S4ClassificationDensity

namespace Taeyoung.Methods.RootedSOS.CompactS4
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem lookupGroup_eq : ∀ index : Fin 57, ∀ left right : Fin 16,
    lookupGroup index left right = S4Classification.witnessGroup index left right := by
  decide +kernel

def pairGroup (a b : Fin 352) : Fin 143 :=
  lookupGroup (S4Classification.pairUnionIndex a b)
    (S4Classification.pairLeftBranchFin a) (S4Classification.pairRightBranchFin b)

theorem pairGroup_eq (a b : Fin 352) :
    pairGroup a b = S4Classification.pairWitnessGroup a b := by
  exact lookupGroup_eq _ _ _

theorem pair_density
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (a b : Fin 352) (W : Taeyoung.Graphon Ω μ) :
    Taeyoung.homDensity (S4Flags.gluedGraph a b) W =
      Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey (pairGroup a b)).2 *
        Taeyoung.homDensity (S4Classification.coreGraph6 (pairGroup a b)) W := by
  rw [pairGroup_eq]
  exact S4Classification.pair_density_classified a b W

#print axioms pair_density
end Taeyoung.Methods.RootedSOS.CompactS4
