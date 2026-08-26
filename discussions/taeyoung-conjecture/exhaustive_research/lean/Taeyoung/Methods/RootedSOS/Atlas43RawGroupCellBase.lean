import Taeyoung.Methods.RootedSOS.Atlas43CommonGramExact
import Taeyoung.Methods.RootedSOS.Atlas43RawGroupWitnessData
import Taeyoung.Methods.RootedSOS.SparseSymmetric

/-! # Integer-scaled arithmetic for the Atlas 43 raw graph groups

The 81 correction entries outside the common denominator are cleared using
one exact denominator per Gram block.  Kernel computation therefore performs
large integer additions, rather than repeatedly normalizing a dense rational
sum.
-/

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

open Taeyoung.Methods.RootedSOS.Atlas43Data
open Taeyoung.Methods.RootedSOS.Atlas43Gram
open Taeyoung.Methods.RootedSOS.Atlas43PSD
open Taeyoung.Methods.RootedSOS.Atlas43GramWitnessData
open Taeyoung.Methods.RootedSOS.Atlas43RawGroupWitnessData

def claimedExceptionalScaledTotal (row slot : Nat) : Int :=
  (exceptionalScaledGroupTotals[row]?.getD #[])[slot]?.getD 0

def stagedCorrectionDataEntry (order offset i j : Nat) : Array Int :=
  corrections[(offset + upperIndex order (min i j) (max i j))]?.getD #[]

def stagedCorrectionIsCommon (order offset i j : Nat) : Bool :=
  let denominator := (stagedCorrectionDataEntry order offset i j)[4]?.getD 0
  decide (denominator.natAbs ∣ commonCorrectionDenominator)

private def exceptionalEntry₀ (entry : Fin 66) : Array Int :=
  exceptionalScaledEntries₀[entry.1]?.getD #[]

private def exceptionalEntry₁ (entry : Fin 15) : Array Int :=
  exceptionalScaledEntries₁[entry.1]?.getD #[]

private def fin107 (value : Int) : Fin 107 :=
  ⟨value.toNat % 107, Nat.mod_lt _ (by decide)⟩

private def fin48 (value : Int) : Fin 48 :=
  ⟨value.toNat % 48, Nat.mod_lt _ (by decide)⟩

def exceptionalLeft₀ (entry : Fin 66) : Fin 107 :=
  fin107 ((exceptionalEntry₀ entry)[0]?.getD 0)

def exceptionalRight₀ (entry : Fin 66) : Fin 107 :=
  fin107 ((exceptionalEntry₀ entry)[1]?.getD 0)

def exceptionalValue₀ (entry : Fin 66) : Int :=
  (exceptionalEntry₀ entry)[2]?.getD 0

def exceptionalLeft₁ (entry : Fin 15) : Fin 48 :=
  fin48 ((exceptionalEntry₁ entry)[0]?.getD 0)

def exceptionalRight₁ (entry : Fin 15) : Fin 48 :=
  fin48 ((exceptionalEntry₁ entry)[1]?.getD 0)

def exceptionalValue₁ (entry : Fin 15) : Int :=
  (exceptionalEntry₁ entry)[2]?.getD 0

def claimedExceptionalPairWeight₀
    (entry : Fin 66) (slot row : Nat) : Int :=
  ((exceptionalPairWeights₀[entry.1]?.getD #[])[slot]?.getD #[])[row]?.getD 0

def claimedExceptionalPairWeight₁ (entry : Fin 15) (row : Nat) : Int :=
  (exceptionalPairWeights₁[entry.1]?.getD #[])[row]?.getD 0

def claimedRawGroupIndex (a b : Fin 64) : Nat :=
  (rawGroupIndex[a.1]?.getD #[])[b.1]?.getD 33

def claimedRawGroupIndexFin (a b : Fin 64) : Fin 33 :=
  ⟨claimedRawGroupIndex a b % 33, Nat.mod_lt _ (by decide)⟩

def pairWeightBase₀ : Nat := 2 * pairWeightBound₀ + 1
def pairWeightBase₁ : Nat := 2 * pairWeightBound₁ + 1
def pairWeightTermBound₀ : Nat := pairWeightBound₀ / 4096
def pairWeightTermBound₁ : Nat := pairWeightBound₁ / 4096

def stagedExceptionalScaledCorrection₀ (i j : Fin 107) : Int :=
  sparseSymmetricMatrix exceptionalLeft₀ exceptionalRight₀ exceptionalValue₀ i j

def stagedExceptionalScaledCorrection₁ (i j : Fin 48) : Int :=
  sparseSymmetricMatrix exceptionalLeft₁ exceptionalRight₁ exceptionalValue₁ i j

def groupPairWeight₀ (block₀ block₁ : Fin 2)
    (core isolated : Nat) (i j : Fin 107) : Int :=
  ((rawGroupPairs core isolated).map fun pair ↦
    F₀Int (extendedIndex block₀ pair.1) i *
      F₀Int (extendedIndex block₁ pair.2) j).sum

def groupPairWeight₁
    (core isolated : Nat) (i j : Fin 48) : Int :=
  ((rawGroupPairs core isolated).map fun pair ↦
    F₁Int pair.1 i * F₁Int pair.2 j).sum

def actualExceptionalPairWeight₀
    (entry : Fin 66) (slot row : Nat) : Int :=
  let key := rawGroupKey row
  let i := exceptionalLeft₀ entry
  let j := exceptionalRight₀ entry
  let forward := match slot with
    | 0 => groupPairWeight₀ 0 0 key.1 key.2 i j
    | 1 => groupPairWeight₀ 0 1 key.1 key.2 i j
    | 2 => groupPairWeight₀ 1 1 key.1 key.2 i j
    | _ => 0
  let reverse := match slot with
    | 0 => groupPairWeight₀ 0 0 key.1 key.2 j i
    | 1 => groupPairWeight₀ 0 1 key.1 key.2 j i
    | 2 => groupPairWeight₀ 1 1 key.1 key.2 j i
    | _ => 0
  forward + if i = j then 0 else reverse

def actualExceptionalPairWeight₁ (entry : Fin 15) (row : Nat) : Int :=
  let key := rawGroupKey row
  let i := exceptionalLeft₁ entry
  let j := exceptionalRight₁ entry
  groupPairWeight₁ key.1 key.2 i j +
    if i = j then 0 else groupPairWeight₁ key.1 key.2 j i

def exceptionalPairContribution₀
    (entry : Fin 66) (slot : Nat) (a b : Fin 64) : Int :=
  let i := exceptionalLeft₀ entry
  let j := exceptionalRight₀ entry
  let forward := match slot with
    | 0 => F₀Int (extendedIndex 0 a) i * F₀Int (extendedIndex 0 b) j
    | 1 => F₀Int (extendedIndex 0 a) i * F₀Int (extendedIndex 1 b) j
    | 2 => F₀Int (extendedIndex 1 a) i * F₀Int (extendedIndex 1 b) j
    | _ => 0
  let reverse := match slot with
    | 0 => F₀Int (extendedIndex 0 a) j * F₀Int (extendedIndex 0 b) i
    | 1 => F₀Int (extendedIndex 0 a) j * F₀Int (extendedIndex 1 b) i
    | 2 => F₀Int (extendedIndex 1 a) j * F₀Int (extendedIndex 1 b) i
    | _ => 0
  forward + if i = j then 0 else reverse

def exceptionalPairContribution₁ (entry : Fin 15) (a b : Fin 64) : Int :=
  let i := exceptionalLeft₁ entry
  let j := exceptionalRight₁ entry
  F₁Int a i * F₁Int b j +
    if i = j then 0 else F₁Int a j * F₁Int b i

def computedPairWeightEncoding₀ (entry : Fin 66) (slot : Nat) : Int :=
  pairWeightBound₀ * geometricEncoding pairWeightBase₀ 33 +
    ∑ a : Fin 64, ∑ b : Fin 64,
      exceptionalPairContribution₀ entry slot a b *
        (pairWeightBase₀ : Int) ^ claimedRawGroupIndex a b

def computedPairWeightEncoding₁ (entry : Fin 15) : Int :=
  pairWeightBound₁ * geometricEncoding pairWeightBase₁ 33 +
    ∑ a : Fin 64, ∑ b : Fin 64,
      exceptionalPairContribution₁ entry a b *
        (pairWeightBase₁ : Int) ^ claimedRawGroupIndex a b

def exceptionalPairWeight₀EncodingValid
    (entry : Fin 66) (slot : Nat) : Bool :=
  decide (∀ row : Fin 33,
      (claimedExceptionalPairWeight₀ entry slot row).natAbs ≤ pairWeightBound₀) &&
    decide (∀ a b : Fin 64,
      (exceptionalPairContribution₀ entry slot a b).natAbs ≤
        pairWeightTermBound₀) &&
    shiftedEncoding pairWeightBase₀ pairWeightBound₀
        (List.ofFn fun row : Fin 33 ↦
          claimedExceptionalPairWeight₀ entry slot row) ==
      computedPairWeightEncoding₀ entry slot

def exceptionalPairWeight₁EncodingValid (entry : Fin 15) : Bool :=
  decide (∀ row : Fin 33,
      (claimedExceptionalPairWeight₁ entry row).natAbs ≤ pairWeightBound₁) &&
    decide (∀ a b : Fin 64,
      (exceptionalPairContribution₁ entry a b).natAbs ≤
        pairWeightTermBound₁) &&
    shiftedEncoding pairWeightBase₁ pairWeightBound₁
        (List.ofFn fun row : Fin 33 ↦
          claimedExceptionalPairWeight₁ entry row) ==
      computedPairWeightEncoding₁ entry

def computedExceptionalScaledTotal₀ (row slot : Nat) : Int :=
  ∑ entry : Fin 66,
    exceptionalValue₀ entry * claimedExceptionalPairWeight₀ entry slot row

def computedExceptionalScaledTotal₁ (row : Nat) : Int :=
  ∑ entry : Fin 15,
    exceptionalValue₁ entry * claimedExceptionalPairWeight₁ entry row

def stagedCorrectionRational₀Valid (i j : Fin 107) : Bool :=
  Rat.ofInt (stagedExceptionalScaledCorrection₀ i j) /
      Rat.ofInt exceptionalDenominator₀ == C₀ i j - commonC₀ i j

def stagedCorrectionRational₁Valid (i j : Fin 48) : Bool :=
  Rat.ofInt (stagedExceptionalScaledCorrection₁ i j) /
      Rat.ofInt exceptionalDenominator₁ == C₁ i j - commonC₁ i j

def rawGroupScaledCellValid (row slot : Nat) : Bool :=
  let key := rawGroupKey row
  match slot with
  | 0 =>
      claimedExceptionalScaledTotal row 0 ==
          computedExceptionalScaledTotal₀ row 0 &&
        claimedGroupTotal row 0 == commonGroupTotal₀ 0 0 key.1 key.2 +
          Rat.ofInt (claimedExceptionalScaledTotal row 0) /
            Rat.ofInt exceptionalDenominator₀
  | 1 =>
      claimedExceptionalScaledTotal row 1 ==
          computedExceptionalScaledTotal₀ row 1 &&
        claimedGroupTotal row 1 == commonGroupTotal₀ 0 1 key.1 key.2 +
          Rat.ofInt (claimedExceptionalScaledTotal row 1) /
            Rat.ofInt exceptionalDenominator₀
  | 2 =>
      claimedExceptionalScaledTotal row 2 ==
          computedExceptionalScaledTotal₀ row 2 &&
        claimedGroupTotal row 2 == commonGroupTotal₀ 1 1 key.1 key.2 +
          Rat.ofInt (claimedExceptionalScaledTotal row 2) /
            Rat.ofInt exceptionalDenominator₀
  | 3 =>
      claimedExceptionalScaledTotal row 3 ==
          computedExceptionalScaledTotal₁ row &&
        claimedGroupTotal row 3 == commonGroupTotal₁ key.1 key.2 +
          Rat.ofInt (claimedExceptionalScaledTotal row 3) /
            Rat.ofInt exceptionalDenominator₁
  | _ => false

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
