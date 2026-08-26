import Mathlib.Lean.Json
import Mathlib.Tactic.Eval

/-! # Staged exceptional-prefix data for the Atlas 43 raw groups -/

namespace Taeyoung.Methods.RootedSOS.Atlas43RawGroupWitnessData

set_option maxRecDepth 1000000

private def source : String :=
  include_str ".."/".."/".."/".."/"experiments"/
    "house_atlas43_raw_group_witness.json"

private def decodeFieldFrom {α : Type} [Lean.FromJson α] [Inhabited α]
    (contents key : String) : α :=
  let json := match Lean.Json.parse contents with
  | .ok value => value
  | .error _ => Lean.Json.null
  match (json.getObjVal? key).bind Lean.fromJson? with
  | .ok value => value
  | .error _ => default

def rawGroupKeys : Array (Array Nat) :=
  eval% decodeFieldFrom source "raw_group_keys"

def rawGroupIndex : Array (Array Nat) :=
  eval% decodeFieldFrom source "raw_group_index"

def pairWeightBound₀ : Nat :=
  eval% decodeFieldFrom source "pair_weight_bound0"

def pairWeightBound₁ : Nat :=
  eval% decodeFieldFrom source "pair_weight_bound1"

def exceptionalDenominator₀ : Nat :=
  eval% decodeFieldFrom source "exceptional_denominator0"

def exceptionalDenominator₁ : Nat :=
  eval% decodeFieldFrom source "exceptional_denominator1"

/-- Exceptional upper-triangle entries `[i, j, scaledNumerator]`. -/
def exceptionalScaledEntries₀ : Array (Array Int) :=
  eval% decodeFieldFrom source "exceptional_scaled_entries0"

def exceptionalScaledEntries₁ : Array (Array Int) :=
  eval% decodeFieldFrom source "exceptional_scaled_entries1"

def exceptionalPairWeights₀ : Array (Array (Array Int)) :=
  eval% decodeFieldFrom source "exceptional_pair_weights0"

def exceptionalPairWeights₁ : Array (Array Int) :=
  eval% decodeFieldFrom source "exceptional_pair_weights1"

/-- Four integer-scaled exceptional totals for each of the 33 raw groups. -/
def exceptionalScaledGroupTotals : Array (Array Int) :=
  eval% decodeFieldFrom source "exceptional_scaled_group_totals"

end Taeyoung.Methods.RootedSOS.Atlas43RawGroupWitnessData
