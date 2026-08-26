import Taeyoung.Methods.RootedSOS.Atlas43CoresRows00
import Taeyoung.Methods.RootedSOS.Atlas43CoresRows08
import Taeyoung.Methods.RootedSOS.Atlas43CoresRows16
import Taeyoung.Methods.RootedSOS.Atlas43CoresRows24
import Taeyoung.Methods.RootedSOS.Atlas43CoresRows32
import Taeyoung.Methods.RootedSOS.Atlas43CoresRows40
import Taeyoung.Methods.RootedSOS.Atlas43CoresRows48
import Taeyoung.Methods.RootedSOS.Atlas43CoresRows56

/-!
# Complete Atlas 43 core-classification audit

All 4,096 normalized glued products are explicitly relabelled to padded Graph
Atlas representatives.  Combined with fixed-density normalization, this is
the semantic grouping used by the 91 coefficient equations.
-/

namespace Taeyoung.Methods.RootedSOS.Atlas43Cores

open Taeyoung
open Taeyoung.Methods.RootedSOS
open Taeyoung.Methods.RootedSOS.Atlas43Flags
open Taeyoung.Methods.RootedSOS.Atlas43FixedDensity

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem all_core_witnesses_valid :
    ∀ a b : Fin 64, coreWitnessValid a b = true := by
  intro a b
  by_cases h₀ : a.1 < 8
  · let k : Fin 8 := ⟨a.1, h₀⟩
    let a' : Fin 64 := ⟨0 + k.1, by omega⟩
    have ha : a' = a := by ext; dsimp [a', k]; omega
    rw [← ha]
    exact core_witnesses_rows_00 k b
  by_cases h₁ : a.1 < 16
  · let k : Fin 8 := ⟨a.1 - 8, by omega⟩
    let a' : Fin 64 := ⟨8 + k.1, by omega⟩
    have ha : a' = a := by ext; dsimp [a', k]; omega
    rw [← ha]
    exact core_witnesses_rows_08 k b
  by_cases h₂ : a.1 < 24
  · let k : Fin 8 := ⟨a.1 - 16, by omega⟩
    let a' : Fin 64 := ⟨16 + k.1, by omega⟩
    have ha : a' = a := by ext; dsimp [a', k]; omega
    rw [← ha]
    exact core_witnesses_rows_16 k b
  by_cases h₃ : a.1 < 32
  · let k : Fin 8 := ⟨a.1 - 24, by omega⟩
    let a' : Fin 64 := ⟨24 + k.1, by omega⟩
    have ha : a' = a := by ext; dsimp [a', k]; omega
    rw [← ha]
    exact core_witnesses_rows_24 k b
  by_cases h₄ : a.1 < 40
  · let k : Fin 8 := ⟨a.1 - 32, by omega⟩
    let a' : Fin 64 := ⟨32 + k.1, by omega⟩
    have ha : a' = a := by ext; dsimp [a', k]; omega
    rw [← ha]
    exact core_witnesses_rows_32 k b
  by_cases h₅ : a.1 < 48
  · let k : Fin 8 := ⟨a.1 - 40, by omega⟩
    let a' : Fin 64 := ⟨40 + k.1, by omega⟩
    have ha : a' = a := by ext; dsimp [a', k]; omega
    rw [← ha]
    exact core_witnesses_rows_40 k b
  by_cases h₆ : a.1 < 56
  · let k : Fin 8 := ⟨a.1 - 48, by omega⟩
    let a' : Fin 64 := ⟨48 + k.1, by omega⟩
    have ha : a' = a := by ext; dsimp [a', k]; omega
    rw [← ha]
    exact core_witnesses_rows_48 k b
  · let k : Fin 8 := ⟨a.1 - 56, by omega⟩
    let a' : Fin 64 := ⟨56 + k.1, by omega⟩
    have ha : a' = a := by ext; dsimp [a', k]; omega
    rw [← ha]
    exact core_witnesses_rows_56 k b

theorem homDensity_fixedCore_eq_atlasCore
    (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (a b : Fin 64) (W : Graphon Ω μ) :
    homDensity (fixedCoreGraphFin5 (gluedOrdinaryGraph a b)) W =
      homDensity (atlasCoreGraph (coreId a b)) W :=
  homDensity_fixedCore_eq_atlasCore_of_witness Ω μ a b W
    (all_core_witnesses_valid a b)

/-- Semantic fixed-density identity for each glued Atlas 43 flag product. -/
theorem homDensity_gluedOrdinaryGraph_eq_atlasCore
    (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (a b : Fin 64) (W : Graphon Ω μ) :
    homDensity (gluedOrdinaryGraph a b) W =
      cliqueDensity 2 W ^ isolatedEdgeCountFin5 (gluedOrdinaryGraph a b) *
        homDensity (atlasCoreGraph (coreId a b)) W := by
  calc
    homDensity (gluedOrdinaryGraph a b) W =
        cliqueDensity 2 W ^ isolatedEdgeCountFin5 (gluedOrdinaryGraph a b) *
          homDensity (fixedCoreGraphFin5 (gluedOrdinaryGraph a b)) W :=
      homDensity_fixedCore_of_valid (gluedOrdinaryGraph a b) W
        (all_decompositions_valid a b)
    _ = _ := by rw [homDensity_fixedCore_eq_atlasCore Ω μ a b W]

end Taeyoung.Methods.RootedSOS.Atlas43Cores
