import Taeyoung.Methods.RootedSOS.Atlas43Cores
import Taeyoung.Methods.RootedSOS.Atlas43GramWitnessData
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.Indexes

/-!
# Executable arithmetic for the Atlas 43 coefficient identity

The few exceptional correction denominators are kept separate.  The dense
common-denominator part is checked through `K = F (I + C)` and `G = K Fᵀ`;
the exceptional part is evaluated directly on each of the 33 graph groups.
-/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

open Taeyoung.Methods.RootedSOS.Atlas43Data
open Taeyoung.Methods.RootedSOS.Atlas43Gram
open Taeyoung.Methods.RootedSOS.Atlas43PSD
open Taeyoung.Methods.RootedSOS.Atlas43Flags
open Taeyoung.Methods.RootedSOS.Atlas43FixedDensity
open Taeyoung.Methods.RootedSOS.Atlas43Cores
open Taeyoung.Methods.RootedSOS.Atlas43GramWitnessData

set_option maxRecDepth 100000

/-- Decode a reduced rational pair.  Malformed data maps to zero; the shape
and entrywise checks reject malformed witnesses. -/
def ratPair (entry : Array Int) : ℚ :=
  Rat.ofInt (entry[0]?.getD 0) / Rat.ofInt (entry[1]?.getD 0)

def pairNumerator (entry : Array Int) : Int := entry[0]?.getD 0
def pairDenominator (entry : Array Int) : Int := entry[1]?.getD 0

private def correctionDataEntry (order offset i j : Nat) : Array Int :=
  corrections[(offset + upperIndex order (min i j) (max i j))]?.getD #[]

private def correctionIsCommon (order offset i j : Nat) : Bool :=
  let denominator := (correctionDataEntry order offset i j)[4]?.getD 0
  decide (denominator.natAbs ∣ commonCorrectionDenominator)

private def commonCorrectionScaledNumerator
    (order offset i j : Nat) : Int :=
  let entry := correctionDataEntry order offset i j
  let numerator := entry[3]?.getD 0
  let denominator := entry[4]?.getD 0
  if correctionIsCommon order offset i j then
    numerator * (commonCorrectionDenominator / denominator.natAbs : Nat)
  else 0

def commonC₀ (i j : Fin 107) : ℚ :=
  if correctionIsCommon 107 0 i j then C₀ i j else 0

def commonC₁ (i j : Fin 48) : ℚ :=
  if correctionIsCommon 48 5778 i j then C₁ i j else 0

private def upperIntClaim (data : Array (Array Int)) (a b : Nat) : Int :=
  let lo := min a b
  let hi := max a b
  (data[lo]?.getD #[])[hi - lo]?.getD 0

def claimedCommonC₀Scaled (i j : Fin 107) : Int :=
  upperIntClaim commonCorrection0ScaledUpper i j

def claimedCommonC₁Scaled (i j : Fin 48) : Int :=
  upperIntClaim commonCorrection1ScaledUpper i j

def commonC₀EntryValid (i j : Fin 107) : Bool :=
  claimedCommonC₀Scaled i j == commonCorrectionScaledNumerator 107 0 i j

def commonC₁EntryValid (i j : Fin 48) : Bool :=
  claimedCommonC₁Scaled i j == commonCorrectionScaledNumerator 48 5778 i j

def commonC₀RationalEntryValid (i j : Fin 107) : Bool :=
  commonC₀ i j == Rat.ofInt (claimedCommonC₀Scaled i j) /
    Rat.ofInt commonCorrectionDenominator

def commonC₁RationalEntryValid (i j : Fin 48) : Bool :=
  commonC₁ i j == Rat.ofInt (claimedCommonC₁Scaled i j) /
    Rat.ofInt commonCorrectionDenominator

def claimedIntermediate₀Scaled (a : Fin 128) (j : Fin 107) : Int :=
  (intermediate0Scaled[a.1]?.getD #[])[j.1]?.getD 0

def claimedIntermediate₁Scaled (a : Fin 64) (j : Fin 48) : Int :=
  (intermediate1Scaled[a.1]?.getD #[])[j.1]?.getD 0

def expectedIntermediate₀Scaled (a : Fin 128) (j : Fin 107) : Int :=
  F₀Int a j * commonCorrectionDenominator +
    ∑ i, F₀Int a i * claimedCommonC₀Scaled i j

def expectedIntermediate₁Scaled (a : Fin 64) (j : Fin 48) : Int :=
  F₁Int a j * commonCorrectionDenominator +
    ∑ i, F₁Int a i * claimedCommonC₁Scaled i j

def intermediate₀EntryValid (a : Fin 128) (j : Fin 107) : Bool :=
  claimedIntermediate₀Scaled a j == expectedIntermediate₀Scaled a j

def intermediate₁EntryValid (a : Fin 64) (j : Fin 48) : Bool :=
  claimedIntermediate₁Scaled a j == expectedIntermediate₁Scaled a j

def claimedCommonGram₀Scaled (a b : Fin 128) : Int :=
  upperIntClaim commonGram0ScaledUpper a b

def claimedCommonGram₁Scaled (a b : Fin 64) : Int :=
  upperIntClaim commonGram1ScaledUpper a b

def commonGram₀EntryValid (a b : Fin 128) : Bool :=
  let expected := ∑ j, claimedIntermediate₀Scaled a j * F₀Int b j
  claimedCommonGram₀Scaled a b == expected

def commonGram₁EntryValid (a b : Fin 64) : Bool :=
  let expected := ∑ j, claimedIntermediate₁Scaled a j * F₁Int b j
  claimedCommonGram₁Scaled a b == expected

def intermediateBase₀ : Nat := 2 * intermediate0Bound + 1
def intermediateBase₁ : Nat := 2 * intermediate1Bound + 1
def gramBase₀ : Nat := 2 * gram0Bound + 1
def gramBase₁ : Nat := 2 * gram1Bound + 1

def intEncoding (base : Nat) (values : List Int) : Int :=
  (Nat.ofDigits base (values.map Int.toNat) : Int)

def shiftedEncoding (base bound : Nat) (values : List Int) : Int :=
  intEncoding base (values.map fun value ↦ value + bound)

def geometricEncoding (base count : Nat) : Int :=
  ∑ k ∈ Finset.range count, (base : Int) ^ k

lemma shifted_digit_nonneg {value : Int} {bound : Nat}
    (h : value.natAbs ≤ bound) : 0 ≤ value + bound := by
  have habs : |value| ≤ (bound : Int) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast h
  have hlo : -(bound : Int) ≤ value :=
    le_trans (neg_le_neg habs) (neg_abs_le value)
  omega

lemma shifted_digit_lt {value : Int} {bound : Nat}
    (h : value.natAbs ≤ bound) : (value + bound).toNat < 2 * bound + 1 := by
  have hlo := shifted_digit_nonneg h
  have hhi : value ≤ (bound : Int) := by
    have habs : |value| ≤ (bound : Int) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h
    exact le_trans (le_abs_self value) habs
  rw [Int.toNat_lt hlo]
  omega

/-- Equality of the large-base encodings of two bounded signed vectors forces
entrywise equality.  This is the small trusted decoder behind the row-local
kernel audits below. -/
theorem shiftedEncoding_injective_of_bound
    {n base bound : Nat} (hbound : 0 < bound)
    (hbase : base = 2 * bound + 1)
    (left right : Fin n → Int)
    (hleft : ∀ i, (left i).natAbs ≤ bound)
    (hright : ∀ i, (right i).natAbs ≤ bound)
    (hencoding : shiftedEncoding base bound (List.ofFn left) =
      shiftedEncoding base bound (List.ofFn right)) :
    left = right := by
  have hbase' : 1 < base := by
    rw [hbase]
    omega
  have hnat :
      Nat.ofDigits base ((List.ofFn left).map fun value : Int ↦
        (value + (bound : Int)).toNat) =
        Nat.ofDigits base ((List.ofFn right).map fun value : Int ↦
          (value + (bound : Int)).toNat) := by
    have hcast := hencoding
    simp only [shiftedEncoding, intEncoding, List.map_map] at hcast
    rw [← Nat.coe_ofDigits Int base, ← Nat.coe_ofDigits Int base] at hcast
    exact_mod_cast hcast
  have hlists := Nat.ofDigits_inj_of_len_eq hbase'
    (by simp)
    (by
      intro digit hdigit
      simp only [List.mem_map, List.mem_ofFn] at hdigit
      obtain ⟨value, ⟨i, rfl⟩, rfl⟩ := hdigit
      rw [hbase]
      exact shifted_digit_lt (hleft i))
    (by
      intro digit hdigit
      simp only [List.mem_map, List.mem_ofFn] at hdigit
      obtain ⟨value, ⟨i, rfl⟩, rfl⟩ := hdigit
      rw [hbase]
      exact shifted_digit_lt (hright i))
    hnat
  funext i
  let leftDigits := (List.ofFn left).map fun value : Int ↦
    (value + (bound : Int)).toNat
  let rightDigits := (List.ofFn right).map fun value : Int ↦
    (value + (bound : Int)).toNat
  have hdigit := congrArg (fun values : List Nat ↦ values.getD i.1 0) hlists
  change leftDigits.getD i.1 0 = rightDigits.getD i.1 0 at hdigit
  rw [List.getD_eq_getElem leftDigits 0 (by simp [leftDigits]),
    List.getD_eq_getElem rightDigits 0 (by simp [rightDigits])] at hdigit
  simp only [leftDigits, rightDigits, List.getElem_map, List.getElem_ofFn] at hdigit
  have hleft_nonneg := shifted_digit_nonneg (hleft i)
  have hright_nonneg := shifted_digit_nonneg (hright i)
  have hcast := congrArg (fun value : Nat ↦ (value : Int)) hdigit
  rw [Int.toNat_of_nonneg hleft_nonneg,
    Int.toNat_of_nonneg hright_nonneg] at hcast
  omega

theorem intEncoding_ofFn_eq_sum {n base : Nat} (values : Fin n → Int)
    (hvalues : ∀ i, 0 ≤ values i) :
    intEncoding base (List.ofFn values) =
      ∑ i : Fin n, values i * (base : Int) ^ i.1 := by
  unfold intEncoding
  rw [List.map_ofFn]
  rw [← Nat.coe_ofDigits Int base]
  rw [Nat.ofDigits_eq_sum_mapIdx]
  simp only [List.mapIdx_eq_ofFn, List.length_ofFn, List.get_ofFn,
    List.sum_ofFn, Function.comp_apply]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [Int.toNat_of_nonneg (hvalues _)]
  apply congrArg₂ (· * ·)
  · exact congrArg values (Fin.ext rfl)
  · rfl

theorem shiftedEncoding_ofFn_eq_sum {n base bound : Nat}
    (values : Fin n → Int) (hvalues : ∀ i, (values i).natAbs ≤ bound) :
    shiftedEncoding base bound (List.ofFn values) =
      ∑ i : Fin n, (values i + bound) * (base : Int) ^ i.1 := by
  unfold shiftedEncoding
  rw [List.map_ofFn]
  change intEncoding base (List.ofFn (fun i ↦ values i + bound)) = _
  exact intEncoding_ofFn_eq_sum
    (fun i ↦ values i + bound) (fun i ↦ shifted_digit_nonneg (hvalues i))

/-- Algebraic expansion of one positionally encoded matrix-product row. -/
theorem encoded_matrix_product {m n : Nat} (base bound : Nat)
    (diagonal : Fin n → Int) (left : Fin m → Int)
    (matrix : Fin m → Fin n → Int) :
    (∑ j : Fin n, (diagonal j + (∑ i : Fin m, left i * matrix i j) + bound) *
        (base : Int) ^ j.1) =
      bound * geometricEncoding base n +
        (∑ j : Fin n, diagonal j * (base : Int) ^ j.1) +
          ∑ i : Fin m, left i *
            (∑ j : Fin n, matrix i j * (base : Int) ^ j.1) := by
  rw [geometricEncoding, ← Fin.sum_univ_eq_sum_range]
  simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  ring_nf
  rw [show (∑ x : Fin n, diagonal x * (base : Int) ^ x.1) =
      ∑ x : Fin n, (base : Int) ^ x.1 * diagonal x by
    apply Finset.sum_congr rfl
    intro x _
    ring]
  abel

theorem natAbs_sum_le_card_mul_bound {ι : Type*} [Fintype ι]
    (values : ι → Int) (bound : Nat)
    (hvalues : ∀ i, (values i).natAbs ≤ bound) :
    (∑ i, values i).natAbs ≤ Fintype.card ι * bound := by
  calc
    (∑ i, values i).natAbs ≤ ∑ i, (values i).natAbs := by
      simpa using Int.natAbs_sum_le (Finset.univ : Finset ι) values
    _ ≤ ∑ _i : ι, bound := Finset.sum_le_sum fun i _ ↦ hvalues i
    _ = Fintype.card ι * bound := by simp

theorem matrix_product_entry_bound {m : Nat}
    (denominator leftBound matrixBound : Nat)
    (diagonal : Int) (left : Fin m → Int) (matrix : Fin m → Int)
    (hdiagonal : diagonal.natAbs ≤ leftBound)
    (hleft : ∀ i, (left i).natAbs ≤ leftBound)
    (hmatrix : ∀ i, (matrix i).natAbs ≤ matrixBound) :
    (diagonal * denominator + ∑ i, left i * matrix i).natAbs ≤
      denominator * leftBound + m * leftBound * matrixBound := by
  calc
    (diagonal * denominator + ∑ i, left i * matrix i).natAbs ≤
        (diagonal * denominator).natAbs + (∑ i, left i * matrix i).natAbs :=
      Int.natAbs_add_le _ _
    _ ≤ leftBound * denominator + m * (leftBound * matrixBound) := by
      apply Nat.add_le_add
      · simpa [Int.natAbs_mul, Nat.mul_comm] using
          Nat.mul_le_mul_right denominator hdiagonal
      · simpa using natAbs_sum_le_card_mul_bound
          (fun i ↦ left i * matrix i) (leftBound * matrixBound)
          (fun i ↦ by
            rw [Int.natAbs_mul]
            exact Nat.mul_le_mul (hleft i) (hmatrix i))
    _ = denominator * leftBound + m * leftBound * matrixBound := by ring

def correction₀EncodingValid (i : Fin 107) : Bool :=
  commonCorrection0EncodedRows[i.1]?.getD 0 ==
    ∑ j : Fin 107, claimedCommonC₀Scaled i j * (intermediateBase₀ : Int) ^ j.1

def correction₁EncodingValid (i : Fin 48) : Bool :=
  commonCorrection1EncodedRows[i.1]?.getD 0 ==
    ∑ j : Fin 48, claimedCommonC₁Scaled i j * (intermediateBase₁ : Int) ^ j.1

def intermediate₀EncodingValid (a : Fin 128) : Bool :=
  let claimed := shiftedEncoding intermediateBase₀ intermediate0Bound
    (List.ofFn fun j : Fin 107 ↦ claimedIntermediate₀Scaled a j)
  let expected :=
    intermediate0Bound * geometricEncoding intermediateBase₀ 107 +
      commonCorrectionDenominator *
        (∑ j : Fin 107, F₀Int a j * (intermediateBase₀ : Int) ^ j.1) +
      ∑ i : Fin 107, F₀Int a i *
        (commonCorrection0EncodedRows[i.1]?.getD 0)
  claimed == expected

def intermediate₁EncodingValid (a : Fin 64) : Bool :=
  let claimed := shiftedEncoding intermediateBase₁ intermediate1Bound
    (List.ofFn fun j : Fin 48 ↦ claimedIntermediate₁Scaled a j)
  let expected :=
    intermediate1Bound * geometricEncoding intermediateBase₁ 48 +
      commonCorrectionDenominator *
        (∑ j : Fin 48, F₁Int a j * (intermediateBase₁ : Int) ^ j.1) +
      ∑ i : Fin 48, F₁Int a i *
        (commonCorrection1EncodedRows[i.1]?.getD 0)
  claimed == expected

def factor₀GramColumnEncodingValid (j : Fin 107) : Bool :=
  factor0GramEncodedColumns[j.1]?.getD 0 ==
    ∑ a : Fin 128, F₀Int a j * (gramBase₀ : Int) ^ a.1

def factor₁GramColumnEncodingValid (j : Fin 48) : Bool :=
  factor1GramEncodedColumns[j.1]?.getD 0 ==
    ∑ a : Fin 64, F₁Int a j * (gramBase₁ : Int) ^ a.1

def gram₀EncodingValid (a : Fin 128) : Bool :=
  let claimed := shiftedEncoding gramBase₀ gram0Bound
    (List.ofFn fun b : Fin 128 ↦ claimedCommonGram₀Scaled a b)
  let expected :=
    gram0Bound * geometricEncoding gramBase₀ 128 +
      ∑ j : Fin 107, claimedIntermediate₀Scaled a j *
        (factor0GramEncodedColumns[j.1]?.getD 0)
  claimed == expected

def gram₁EncodingValid (a : Fin 64) : Bool :=
  let claimed := shiftedEncoding gramBase₁ gram1Bound
    (List.ofFn fun b : Fin 64 ↦ claimedCommonGram₁Scaled a b)
  let expected :=
    gram1Bound * geometricEncoding gramBase₁ 64 +
      ∑ j : Fin 48, claimedIntermediate₁Scaled a j *
        (factor1GramEncodedColumns[j.1]?.getD 0)
  claimed == expected

private def absLeNat (value : Int) (bound : Nat) : Bool :=
  value.natAbs ≤ bound

/-- Row-local bounds used by the positional decoder.  Keeping these checks in
the same small modules as the encoded identities prevents kernel evaluation of
the full dense witness from accumulating in one enormous proof term. -/
def block₀BoundsRowValid (row : Fin 128) : Bool :=
  decide (∀ j : Fin 107, (F₀Int row j).natAbs ≤ factor0Bound) &&
  decide (∀ j : Fin 107,
    (claimedIntermediate₀Scaled row j).natAbs ≤ intermediate0Bound) &&
  decide (∀ b : Fin 128,
    (claimedCommonGram₀Scaled row b).natAbs ≤ gram0Bound) &&
  if h : row.1 < 107 then
    decide (∀ j : Fin 107,
      (claimedCommonC₀Scaled ⟨row.1, h⟩ j).natAbs ≤
        commonCorrection0ScaledBound)
  else true

def block₁BoundsRowValid (row : Fin 64) : Bool :=
  decide (∀ j : Fin 48, (F₁Int row j).natAbs ≤ factor1Bound) &&
  decide (∀ j : Fin 48,
    (claimedIntermediate₁Scaled row j).natAbs ≤ intermediate1Bound) &&
  decide (∀ b : Fin 64,
    (claimedCommonGram₁Scaled row b).natAbs ≤ gram1Bound) &&
  if h : row.1 < 48 then
    decide (∀ j : Fin 48,
      (claimedCommonC₁Scaled ⟨row.1, h⟩ j).natAbs ≤
        commonCorrection1ScaledBound)
  else true

/-- The four scalar formulas from which the safe digit bases are obtained. -/
def arithmeticBoundFormulasValid : Bool :=
  intermediate0Bound == commonCorrectionDenominator * factor0Bound +
    107 * factor0Bound * commonCorrection0ScaledBound &&
  intermediate1Bound == commonCorrectionDenominator * factor1Bound +
    48 * factor1Bound * commonCorrection1ScaledBound &&
  gram0Bound == 107 * intermediate0Bound * factor0Bound &&
  gram1Bound == 48 * intermediate1Bound * factor1Bound

def arithmeticBoundsValid : Bool :=
  arithmeticBoundFormulasValid &&
  factors0.all (fun row ↦ row.all fun value ↦ absLeNat value factor0Bound) &&
  factors1.all (fun row ↦ row.all fun value ↦ absLeNat value factor1Bound) &&
  commonCorrection0ScaledUpper.all
    (fun row ↦ row.all fun value ↦ absLeNat value commonCorrection0ScaledBound) &&
  commonCorrection1ScaledUpper.all
    (fun row ↦ row.all fun value ↦ absLeNat value commonCorrection1ScaledBound) &&
  intermediate0Scaled.all
    (fun row ↦ row.all fun value ↦ absLeNat value intermediate0Bound) &&
  intermediate1Scaled.all
    (fun row ↦ row.all fun value ↦ absLeNat value intermediate1Bound) &&
  commonGram0ScaledUpper.all
    (fun row ↦ row.all fun value ↦ absLeNat value gram0Bound) &&
  commonGram1ScaledUpper.all
    (fun row ↦ row.all fun value ↦ absLeNat value gram1Bound)

def commonC₀RowValid (row : Fin 107) : Bool :=
  (List.ofFn fun j : Fin 107 ↦ commonC₀RationalEntryValid row j).all id

def commonC₁RowValid (row : Fin 48) : Bool :=
  (List.ofFn fun j : Fin 48 ↦ commonC₁RationalEntryValid row j).all id

def intermediate₀RowValid (row : Fin 128) : Bool :=
  (List.ofFn fun j : Fin 107 ↦
    intermediate₀EntryValid row j).all id

def intermediate₁RowValid (row : Fin 64) : Bool :=
  (List.ofFn fun j : Fin 48 ↦
    intermediate₁EntryValid row j).all id

def commonGram₀UpperRowValid (row : Fin 128) : Bool :=
  (List.range (128 - row.1)).all fun d ↦
    if h : row.1 + d < 128 then
      commonGram₀EntryValid row ⟨row.1 + d, h⟩
    else false

def commonGram₁UpperRowValid (row : Fin 64) : Bool :=
  (List.range (64 - row.1)).all fun d ↦
    if h : row.1 + d < 64 then
      commonGram₁EntryValid row ⟨row.1 + d, h⟩
    else false

/-- All expensive computations associated with one row of block zero. -/
def block₀WitnessRowValid (row : Fin 128) : Bool :=
  block₀BoundsRowValid row &&
  intermediate₀EncodingValid row && gram₀EncodingValid row &&
  if h : row.1 < 107 then
    commonC₀RowValid ⟨row.1, h⟩ &&
      correction₀EncodingValid ⟨row.1, h⟩ &&
        factor₀GramColumnEncodingValid ⟨row.1, h⟩
  else true

/-- All expensive computations associated with one row of block one. -/
def block₁WitnessRowValid (row : Fin 64) : Bool :=
  block₁BoundsRowValid row &&
  intermediate₁EncodingValid row && gram₁EncodingValid row &&
  if h : row.1 < 48 then
    commonC₁RowValid ⟨row.1, h⟩ &&
      correction₁EncodingValid ⟨row.1, h⟩ &&
        factor₁GramColumnEncodingValid ⟨row.1, h⟩
  else true

def sameRawGroup (core isolated : Nat) (a b : Fin 64) : Bool :=
  coreId a b == core &&
    isolatedEdgeCountFin5 (gluedOrdinaryGraph a b) == isolated

def rawGroupPairs (core isolated : Nat) : List (Fin 64 × Fin 64) :=
  (List.ofFn fun a : Fin 64 ↦
    List.ofFn fun b : Fin 64 ↦ (a, b)).flatten.filter
      fun pair ↦ sameRawGroup core isolated pair.1 pair.2

def extendedIndex (block : Fin 2) (a : Fin 64) : Fin 128 :=
  ⟨block.1 * 64 + a.1, by omega⟩

def commonGroupTotal₀ (block₀ block₁ : Fin 2) (core isolated : Nat) : ℚ :=
  Rat.ofInt (((rawGroupPairs core isolated).map fun pair ↦
    claimedCommonGram₀Scaled (extendedIndex block₀ pair.1)
      (extendedIndex block₁ pair.2)).sum) /
        Rat.ofInt commonCorrectionDenominator

def commonGroupTotal₁ (core isolated : Nat) : ℚ :=
  Rat.ofInt (((rawGroupPairs core isolated).map fun pair ↦
    claimedCommonGram₁Scaled pair.1 pair.2).sum) /
      Rat.ofInt commonCorrectionDenominator

private def exceptionalTerm₀ (block₀ block₁ : Fin 2)
    (core isolated : Nat) (i j : Fin 107) : ℚ :=
  if correctionIsCommon 107 0 i j then 0 else
    C₀ i j * Rat.ofInt
      (((rawGroupPairs core isolated).map fun pair ↦
        F₀Int (extendedIndex block₀ pair.1) i *
          F₀Int (extendedIndex block₁ pair.2) j).sum)

private def exceptionalTerm₁ (core isolated : Nat) (i j : Fin 48) : ℚ :=
  if correctionIsCommon 48 5778 i j then 0 else
    C₁ i j * Rat.ofInt
      (((rawGroupPairs core isolated).map fun pair ↦
        F₁Int pair.1 i * F₁Int pair.2 j).sum)

def exceptionalGroupTotal₀ (block₀ block₁ : Fin 2)
    (core isolated : Nat) : ℚ :=
  ∑ i : Fin 107, ∑ j : Fin 107,
    exceptionalTerm₀ block₀ block₁ core isolated i j

def exceptionalGroupTotal₁ (core isolated : Nat) : ℚ :=
  ∑ i : Fin 48, ∑ j : Fin 48,
    exceptionalTerm₁ core isolated i j

def computedGroupTotal₀ (block₀ block₁ : Fin 2)
    (core isolated : Nat) : ℚ :=
  commonGroupTotal₀ block₀ block₁ core isolated +
    exceptionalGroupTotal₀ block₀ block₁ core isolated

def computedGroupTotal₁ (core isolated : Nat) : ℚ :=
  commonGroupTotal₁ core isolated + exceptionalGroupTotal₁ core isolated

def rawGroupKey (row : Nat) : Nat × Nat :=
  let key := rawGroupKeys[row]?.getD #[]
  (key[0]?.getD 0, key[1]?.getD 0)

def claimedGroupTotal (row slot : Nat) : ℚ :=
  ratPair ((rawGroupTotals[row]?.getD #[])[slot]?.getD #[])

def rawGroupArithmeticValid (row : Nat) : Bool :=
  let key := rawGroupKey row
  claimedGroupTotal row 0 == computedGroupTotal₀ 0 0 key.1 key.2 &&
  claimedGroupTotal row 1 == computedGroupTotal₀ 0 1 key.1 key.2 &&
  claimedGroupTotal row 2 == computedGroupTotal₀ 1 1 key.1 key.2 &&
  claimedGroupTotal row 3 == computedGroupTotal₁ key.1 key.2

def rawGroupKeysValid : Bool :=
  decide rawGroupKeys.toList.Nodup &&
    decide (∀ a b : Fin 64,
      (rawGroupKeys.toList.map Array.toList).contains
        [coreId a b, isolatedEdgeCountFin5 (gluedOrdinaryGraph a b)])

def halfPowerCoefficient (power degree : Nat) : ℚ :=
  if degree ≤ power then
    Rat.ofInt (power.choose degree) / Rat.ofInt (2 ^ power)
  else 0

def shiftedHalfPowerCoefficient (power degree shift : Nat) : ℚ :=
  if shift ≤ degree then halfPowerCoefficient power (degree - shift) else 0

def rawGroupPolynomialCoefficient (row degree : Nat) : ℚ :=
  let isolated := (rawGroupKey row).2
  let c₀ := shiftedHalfPowerCoefficient isolated degree 0
  let c₁ := shiftedHalfPowerCoefficient isolated degree 1
  let c₂ := shiftedHalfPowerCoefficient isolated degree 2
  c₀ * claimedGroupTotal row 0 +
    2 * c₁ * claimedGroupTotal row 1 +
      c₂ * claimedGroupTotal row 2 +
        (c₁ - c₂) * claimedGroupTotal row 3

def certificateCoefficient (core degree : Nat) : ℚ :=
  ((List.range 33).map fun row ↦
    if (rawGroupKey row).1 == core then
      rawGroupPolynomialCoefficient row degree
    else 0).sum

def targetCoefficient (core degree : Nat) : ℚ :=
  let unscaled : ℚ :=
    if core == 43 && degree == 0 then 1
    else if core == 0 then
      match degree with
      | 1 => -1 / 8
      | 2 => -1 / 8
      | 3 => -3 / 8
      | 4 => -3 / 8
      | _ => 0
    else 0
  factorDenominator ^ 2 * unscaled

def allCoefficientEquationsValid : Bool :=
  (List.range 53).all fun core ↦
    (List.range 5).all fun degree ↦
      certificateCoefficient core degree == targetCoefficient core degree

/-- A compact structural check for the derived witness.  Entrywise arithmetic
checks in later modules additionally reject any incorrect value. -/
def witnessShapeCheck : Bool :=
  (List.range commonCorrection0ScaledUpper.size).all (fun i ↦
    (commonCorrection0ScaledUpper[i]?.getD #[]).size == 107 - i) &&
  (List.range commonCorrection1ScaledUpper.size).all (fun i ↦
    (commonCorrection1ScaledUpper[i]?.getD #[]).size == 48 - i) &&
  intermediate0Scaled.all (·.size == 107) &&
  intermediate1Scaled.all (·.size == 48) &&
  (List.range commonGram0ScaledUpper.size).all (fun i ↦
    (commonGram0ScaledUpper[i]?.getD #[]).size == 128 - i) &&
  (List.range commonGram1ScaledUpper.size).all (fun i ↦
    (commonGram1ScaledUpper[i]?.getD #[]).size == 64 - i) &&
  rawGroupKeys.all (·.size == 2) &&
  rawGroupTotals.all fun row ↦ row.size == 4 && row.all (·.size == 2)

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
