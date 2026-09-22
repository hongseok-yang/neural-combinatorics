import Taeyoung.Methods.RootedSOS.S4ClassificationLookup
import Taeyoung.Methods.RootedSOS.FixedDensity

/-! Density consequences of the checked S4 six-vertex classification. -/

namespace Taeyoung.Methods.RootedSOS.S4Classification

open Taeyoung

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem witnessPermutation_length (index : Fin 57) (left right : Fin 16) :
    (witnessPermutation index left right).length = 6 := by
  by_cases h₀ : index.1 < 17
  · simp [witnessPermutation, h₀, LookupChunk000_016.witnessPermutation]
  by_cases h₁ : index.1 < 34
  · simp [witnessPermutation, h₀, h₁,
      LookupChunk017_033.witnessPermutation]
  by_cases h₂ : index.1 < 51
  · simp [witnessPermutation, h₀, h₁, h₂,
      LookupChunk034_050.witnessPermutation]
  · simp [witnessPermutation, h₀, h₁, h₂,
      LookupChunk051_056.witnessPermutation]

private theorem homDensity_graph_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] {n : Nat}
    (H K : SimpleGraph (Fin n)) [dH : DecidableRel H.Adj]
    [dK : DecidableRel K.Adj]
    (W : Graphon Ω μ) (h : H = K) :
    homDensity H W = homDensity K W := by
  subst K
  have hd : dH = dK := Subsingleton.elim _ _
  subst dK
  rfl

theorem standardGraph_density
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (row : Fin 143) (W : Graphon Ω μ) :
    homDensity (standardGraph row) W =
      cliqueDensity 2 W ^ (groupKey row).2 * homDensity (coreGraph6 row) W := by
  have hv := all_group_data_valid row
  have hisolated : (groupKey row).2 ≤ 3 := by
    have hv' := hv
    simp only [groupDataValid, Bool.and_eq_true, decide_eq_true_eq] at hv'
    exact hv'.1.1.2
  interval_cases hcount : (groupKey row).2
  · simp [standardGraph, hcount]
  · have hpadding : adjacencyCode (coreGraph6 row) =
        adjacencyCode ((coreGraph4 row).map (Fin.castAdd 2)) := by
      have hv' := hv
      simp only [groupDataValid, hcount, Bool.and_eq_true,
        decide_eq_true_eq] at hv'
      exact hv'.2
    have hcore : coreGraph6 row = (coreGraph4 row).map (Fin.castAdd 2) :=
      (adjacencyCode_eq_iff _ _).mp hpadding
    have hdcore : homDensity (coreGraph6 row) W = homDensity (coreGraph4 row) W :=
      (homDensity_graph_eq _ _ W hcore).trans
        (homDensity_map_castAdd (coreGraph4 row) 2 W)
    simp only [standardGraph, hcount, cliqueDensity, pow_one]
    rw [homDensity_disjointUnion, hdcore]
    ring
  · have hpadding : adjacencyCode (coreGraph6 row) =
        adjacencyCode ((coreGraph2 row).map (Fin.castAdd 4)) := by
      have hv' := hv
      simp only [groupDataValid, hcount, Bool.and_eq_true,
        decide_eq_true_eq] at hv'
      exact hv'.2
    have hcore : coreGraph6 row = (coreGraph2 row).map (Fin.castAdd 4) :=
      (adjacencyCode_eq_iff _ _).mp hpadding
    have hdcore : homDensity (coreGraph6 row) W = homDensity (coreGraph2 row) W :=
      (homDensity_graph_eq _ _ W hcore).trans
        (homDensity_map_castAdd (coreGraph2 row) 4 W)
    simp only [standardGraph, hcount, cliqueDensity, pow_two]
    rw [homDensity_disjointUnion, homDensity_disjointUnion, hdcore]
    ring
  · have hpadding : adjacencyCode (coreGraph6 row) =
        adjacencyCode (⊥ : SimpleGraph (Fin 6)) := by
      have hv' := hv
      simp only [groupDataValid, hcount, Bool.and_eq_true,
        decide_eq_true_eq] at hv'
      exact hv'.2
    have hcore : coreGraph6 row = (⊥ : SimpleGraph (Fin 6)) :=
      (adjacencyCode_eq_iff _ _).mp hpadding
    have hdcore : homDensity (coreGraph6 row) W = 1 :=
      (homDensity_graph_eq _ _ W hcore).trans (homDensity_bot_fin 6 W)
    simp only [standardGraph, hcount, cliqueDensity]
    rw [homDensity_disjointUnion, homDensity_disjointUnion, hdcore]
    ring

theorem pair_density_classified
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (a b : Fin 352) (W : Graphon Ω μ) :
    homDensity (S4Flags.gluedGraph a b) W =
      cliqueDensity 2 W ^ (groupKey (pairWitnessGroup a b)).2 *
        homDensity (coreGraph6 (pairWitnessGroup a b)) W := by
  have hwitness := pair_lookup_witness_valid a b
  have hrelabel := homDensity_relabelCodeByListFin
    (S4Flags.gluedGraph a b) (pairWitnessPermutation a b)
    (witnessPermutation_length (pairUnionIndex a b)
      (pairLeftBranchFin a) (pairRightBranchFin b)) hwitness.1 W
  have hcode :
      relabelCodeByListFin (S4Flags.gluedGraph a b)
          (pairWitnessPermutation a b) =
        standardCode (pairWitnessGroup a b) := hwitness.2
  have hv := all_group_data_valid (pairWitnessGroup a b)
  have hstandardCode :
      adjacencyCode (standardGraph (pairWitnessGroup a b)) =
        standardCode (pairWitnessGroup a b) := by
    have hv' := hv
    simp only [groupDataValid, Bool.and_eq_true, decide_eq_true_eq] at hv'
    exact hv'.1.2
  have hstandard :
      graphOfCode (standardCode (pairWitnessGroup a b)) =
        standardGraph (pairWitnessGroup a b) := by
    rw [← hstandardCode]
    exact graphOfCode_adjacencyCode _
  rw [hcode] at hrelabel
  have hdstandard :
      homDensity (graphOfCode (standardCode (pairWitnessGroup a b))) W =
        homDensity (standardGraph (pairWitnessGroup a b)) W :=
    homDensity_graph_eq _ _ W hstandard
  exact hrelabel.trans <| hdstandard.trans <|
    standardGraph_density (pairWitnessGroup a b) W

end Taeyoung.Methods.RootedSOS.S4Classification
