import Taeyoung.Methods.RootedSOS.S4YoungBasisData
import Taeyoung.Methods.RootedSOS.S4Young4Data
import Taeyoung.Methods.RootedSOS.S4Young31Data
import Taeyoung.Methods.RootedSOS.S4Young22Data
import Taeyoung.Methods.RootedSOS.S4Young211Data
import Taeyoung.Methods.RootedSOS.S4Young1111Data
import Taeyoung.Methods.RootedSOS.S4PulledGroups000_011Data
import Taeyoung.Methods.RootedSOS.S4PulledGroups012_023Data
import Taeyoung.Methods.RootedSOS.S4PulledGroups024_035Data
import Taeyoung.Methods.RootedSOS.S4PulledGroups036_047Data
import Taeyoung.Methods.RootedSOS.S4PulledGroups048_059Data
import Taeyoung.Methods.RootedSOS.S4PulledGroups060_071Data
import Taeyoung.Methods.RootedSOS.S4PulledGroups072_083Data
import Taeyoung.Methods.RootedSOS.S4PulledGroups084_095Data
import Taeyoung.Methods.RootedSOS.S4PulledGroups096_107Data
import Taeyoung.Methods.RootedSOS.S4PulledGroups108_119Data
import Taeyoung.Methods.RootedSOS.S4PulledGroups120_131Data
import Taeyoung.Methods.RootedSOS.S4PulledGroups132_142Data

/-!
# Common exact Young-symmetrizer data for the S4 certificates

Each JSON sidecar is decoded and checked in a separate module.  This umbrella
only dispatches to cached constants, keeping its own elaboration memory small.
-/

namespace Taeyoung.Methods.RootedSOS.S4YoungData

abbrev basisIndices : Array Nat := S4YoungBasisData.basisIndices
abbrev young4 : Array (Array Int) := S4Young4Data.data
abbrev young31 : Array (Array Int) := S4Young31Data.data
abbrev young22 : Array (Array Int) := S4Young22Data.data
abbrev young211 : Array (Array Int) := S4Young211Data.data
abbrev young1111 : Array (Array Int) := S4Young1111Data.data
abbrev rawGroupKeys : Array (Array Nat) := S4YoungBasisData.rawGroupKeys

def T4Int (a : Fin 352) (i : Fin 32) : Int := S4Young4Data.entry a i
def T31Int (a : Fin 352) (i : Fin 52) : Int := S4Young31Data.entry a i
def T22Int (a : Fin 352) (i : Fin 34) : Int := S4Young22Data.entry a i
def T211Int (a : Fin 352) (i : Fin 30) : Int := S4Young211Data.entry a i
def T1111Int (a : Fin 352) (i : Fin 6) : Int := S4Young1111Data.entry a i

noncomputable def T4 (a : Fin 352) (i : Fin 32) : ℝ := T4Int a i
noncomputable def T31 (a : Fin 352) (i : Fin 52) : ℝ := T31Int a i
noncomputable def T22 (a : Fin 352) (i : Fin 34) : ℝ := T22Int a i
noncomputable def T211 (a : Fin 352) (i : Fin 30) : ℝ := T211Int a i
noncomputable def T1111 (a : Fin 352) (i : Fin 6) : ℝ := T1111Int a i

def rawGroupKey (row : Fin 143) : Nat × Nat :=
  S4YoungBasisData.rawGroupKey row

/-- Sparse triples `(i,j,value)` for one Young-pulled raw graph group. -/
def pulledGroupEntries (row : Fin 143) (block : Fin 5) : Array (Array Int) :=
  if row.1 < 12 then
    S4PulledGroups000_011Data.groupEntries row.1 block.1
  else if row.1 < 24 then
    S4PulledGroups012_023Data.groupEntries (row.1 - 12) block.1
  else if row.1 < 36 then
    S4PulledGroups024_035Data.groupEntries (row.1 - 24) block.1
  else if row.1 < 48 then
    S4PulledGroups036_047Data.groupEntries (row.1 - 36) block.1
  else if row.1 < 60 then
    S4PulledGroups048_059Data.groupEntries (row.1 - 48) block.1
  else if row.1 < 72 then
    S4PulledGroups060_071Data.groupEntries (row.1 - 60) block.1
  else if row.1 < 84 then
    S4PulledGroups072_083Data.groupEntries (row.1 - 72) block.1
  else if row.1 < 96 then
    S4PulledGroups084_095Data.groupEntries (row.1 - 84) block.1
  else if row.1 < 108 then
    S4PulledGroups096_107Data.groupEntries (row.1 - 96) block.1
  else if row.1 < 120 then
    S4PulledGroups108_119Data.groupEntries (row.1 - 108) block.1
  else if row.1 < 132 then
    S4PulledGroups120_131Data.groupEntries (row.1 - 120) block.1
  else
    S4PulledGroups132_142Data.groupEntries (row.1 - 132) block.1

def shapeValid : Bool :=
  S4YoungBasisData.shapeValid &&
  S4Young4Data.shapeValid && S4Young31Data.shapeValid &&
  S4Young22Data.shapeValid && S4Young211Data.shapeValid &&
  S4Young1111Data.shapeValid &&
  S4PulledGroups000_011Data.shapeValid &&
  S4PulledGroups012_023Data.shapeValid &&
  S4PulledGroups024_035Data.shapeValid &&
  S4PulledGroups036_047Data.shapeValid &&
  S4PulledGroups048_059Data.shapeValid &&
  S4PulledGroups060_071Data.shapeValid &&
  S4PulledGroups072_083Data.shapeValid &&
  S4PulledGroups084_095Data.shapeValid &&
  S4PulledGroups096_107Data.shapeValid &&
  S4PulledGroups108_119Data.shapeValid &&
  S4PulledGroups120_131Data.shapeValid &&
  S4PulledGroups132_142Data.shapeValid

theorem shape_valid : shapeValid = true := by
  simp only [shapeValid, S4YoungBasisData.shape_valid,
    S4Young4Data.shape_valid, S4Young31Data.shape_valid,
    S4Young22Data.shape_valid, S4Young211Data.shape_valid,
    S4Young1111Data.shape_valid, S4PulledGroups000_011Data.shape_valid,
    S4PulledGroups012_023Data.shape_valid,
    S4PulledGroups024_035Data.shape_valid,
    S4PulledGroups036_047Data.shape_valid,
    S4PulledGroups048_059Data.shape_valid,
    S4PulledGroups060_071Data.shape_valid,
    S4PulledGroups072_083Data.shape_valid,
    S4PulledGroups084_095Data.shape_valid,
    S4PulledGroups096_107Data.shape_valid,
    S4PulledGroups108_119Data.shape_valid,
    S4PulledGroups120_131Data.shape_valid,
    S4PulledGroups132_142Data.shape_valid, Bool.true_and]

abbrev basisOrderValid : Bool := S4YoungBasisData.basisOrderValid

theorem basis_order_valid : basisOrderValid = true :=
  S4YoungBasisData.basis_order_valid

end Taeyoung.Methods.RootedSOS.S4YoungData
