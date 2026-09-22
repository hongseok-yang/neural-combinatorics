import Taeyoung.Methods.RootedSOS.S4ClassificationGroupChecks
import Taeyoung.Methods.RootedSOS.S4ClassificationLookups000_016Data

namespace Taeyoung.Methods.RootedSOS.S4Classification.LookupChunk000_016

open Taeyoung.Methods.RootedSOS
open Taeyoung.Methods.RootedSOS.S4Classification

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

abbrev start : Nat := 0
abbrev stop : Nat := 17
abbrev cellBase : Nat := 10000000
abbrev groupBase : Nat := 143
abbrev permutationBase : Nat := 6

def encodedRow (index : Fin 17) : Nat :=
  (S4ClassificationLookups000_016Data.data[index.1]?).getD 0 |>.natAbs

def labelUnions : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 53, 54, 56, 57, 58, 60]

def labelUnion (index : Fin 17) : Nat :=
  (labelUnions[0 + index.1]?).getD 0

def lookupCell (index : Fin 17) (left right : Fin 16) : Nat :=
  encodedRow index / cellBase ^ (16 * left.1 + right.1) % cellBase

def witnessGroup (index : Fin 17) (left right : Fin 16) :
    Fin 143 :=
  ⟨lookupCell index left right % groupBase, Nat.mod_lt _ (by decide)⟩

def witnessPermutation (index : Fin 17) (left right : Fin 16) :
    List (Fin 6) :=
  List.ofFn fun coordinate : Fin 6 ↦
    ⟨(lookupCell index left right / groupBase /
      permutationBase ^ coordinate.1) % permutationBase,
      Nat.mod_lt _ (by decide)⟩

def lookupWitnessValid (index : Fin 17)
    (left right : Fin 16) : Bool :=
  let row := witnessGroup index left right
  let permutation := witnessPermutation index left right
  decide permutation.Nodup &&
    decide (relabelCodeByListFin
      (lookupGraph (labelUnion index) left.1 right.1) permutation = standardCode row)

end Taeyoung.Methods.RootedSOS.S4Classification.LookupChunk000_016
