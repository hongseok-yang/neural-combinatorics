import Mathlib.Lean.Json
import Mathlib.Tactic.Eval

/-!
# Derived multiplication witness for the Atlas 43 Gram matrices

This file embeds only derived data.  Later modules kernel-check it entrywise
against the factors and corrections in `Atlas43Data` before it is used.
-/

namespace Taeyoung.Methods.RootedSOS.Atlas43GramWitnessData

set_option maxRecDepth 1000000

private def source : String :=
  include_str ".."/".."/".."/".."/"experiments"/
    "house_atlas43_lean_gram.json"

private def decodeFieldFrom {α : Type} [Lean.FromJson α] [Inhabited α]
    (contents key : String) : α :=
  let json := match Lean.Json.parse contents with
  | .ok value => value
  | .error _ => Lean.Json.null
  match (json.getObjVal? key).bind Lean.fromJson? with
  | .ok value => value
  | .error _ => default

def sourceFactorDenominator : Nat :=
  eval% decodeFieldFrom source "source_factor_denominator"

def commonCorrectionDenominator : Nat :=
  eval% decodeFieldFrom source "common_correction_denominator"

def commonCorrection0ScaledUpper : Array (Array Int) :=
  eval% decodeFieldFrom source "C0_common_scaled_upper"

def commonCorrection1ScaledUpper : Array (Array Int) :=
  eval% decodeFieldFrom source "C1_common_scaled_upper"

def intermediate0Scaled : Array (Array Int) :=
  eval% decodeFieldFrom source "K0_scaled"

def intermediate1Scaled : Array (Array Int) :=
  eval% decodeFieldFrom source "K1_scaled"

def commonGram0ScaledUpper : Array (Array Int) :=
  eval% decodeFieldFrom source "G0_scaled_upper"

def commonGram1ScaledUpper : Array (Array Int) :=
  eval% decodeFieldFrom source "G1_scaled_upper"

/-- The 33 `(core, isolated-edge-count)` groups represented in the products. -/
def rawGroupKeys : Array (Array Nat) :=
  eval% decodeFieldFrom source "raw_group_keys"

/-- Rows `[S₀₀, S₀₁, S₁₁, S₁]`, with every entry encoded as a two-integer
rational pair. -/
def rawGroupTotals : Array (Array (Array Int)) :=
  eval% decodeFieldFrom source "raw_group_totals"

def factor0Bound : Nat := eval% decodeFieldFrom source "factor0_bound"
def factor1Bound : Nat := eval% decodeFieldFrom source "factor1_bound"

def commonCorrection0ScaledBound : Nat :=
  eval% decodeFieldFrom source "common_correction0_scaled_bound"
def commonCorrection1ScaledBound : Nat :=
  eval% decodeFieldFrom source "common_correction1_scaled_bound"

def intermediate0Bound : Nat := eval% decodeFieldFrom source "intermediate0_bound"
def intermediate1Bound : Nat := eval% decodeFieldFrom source "intermediate1_bound"
def gram0Bound : Nat := eval% decodeFieldFrom source "gram0_bound"
def gram1Bound : Nat := eval% decodeFieldFrom source "gram1_bound"

def commonCorrection0EncodedRows : Array Int :=
  eval% decodeFieldFrom source "common_correction0_encoded_rows"
def commonCorrection1EncodedRows : Array Int :=
  eval% decodeFieldFrom source "common_correction1_encoded_rows"

def factor0GramEncodedColumns : Array Int :=
  eval% decodeFieldFrom source "factor0_gram_encoded_columns"
def factor1GramEncodedColumns : Array Int :=
  eval% decodeFieldFrom source "factor1_gram_encoded_columns"

theorem header_eq :
    sourceFactorDenominator = 1000000 ∧
      commonCorrectionDenominator = 1000000000000 ∧
      commonCorrection0ScaledUpper.size = 107 ∧
      commonCorrection1ScaledUpper.size = 48 ∧
      intermediate0Scaled.size = 128 ∧ intermediate1Scaled.size = 64 ∧
      commonGram0ScaledUpper.size = 128 ∧
      commonGram1ScaledUpper.size = 64 ∧
      rawGroupKeys.size = 33 ∧ rawGroupTotals.size = 33 ∧
      commonCorrection0EncodedRows.size = 107 ∧
      commonCorrection1EncodedRows.size = 48 ∧
      factor0GramEncodedColumns.size = 107 ∧
      factor1GramEncodedColumns.size = 48 := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43GramWitnessData
