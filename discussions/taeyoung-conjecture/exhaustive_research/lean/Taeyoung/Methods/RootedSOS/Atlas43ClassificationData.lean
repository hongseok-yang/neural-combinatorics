import Mathlib.Lean.Json
import Mathlib.Tactic.Eval

/-!
# Finite graph-classification data for the Atlas 43 certificate

This metadata is deliberately separate from the Gram certificate JSON, so
changing or extending isomorphism witnesses does not invalidate the expensive
positive-semidefiniteness checks.
-/

namespace Taeyoung.Methods.RootedSOS.Atlas43ClassificationData

set_option maxRecDepth 100000

private def source : String :=
  include_str ".."/".."/".."/".."/"experiments"/
    "house_atlas43_lean_classification.json"

private def decodeFieldFrom {α : Type} [Lean.FromJson α] [Inhabited α]
    (contents key : String) : α :=
  let json := match Lean.Json.parse contents with
  | .ok value => value
  | .error _ => Lean.Json.null
  match (json.getObjVal? key).bind Lean.fromJson? with
  | .ok value => value
  | .error _ => default

def coreIds : Array (Array Nat) :=
  eval% decodeFieldFrom source "core_ids"

def corePermutations : Array (Array (Array Nat)) :=
  eval% decodeFieldFrom source "core_permutations"

def atlasCodes : Array (Array (Array Bool)) :=
  eval% decodeFieldFrom source "atlas_codes"

def housePermutation : Array Nat :=
  eval% decodeFieldFrom source "house_permutation"

theorem header_eq :
    coreIds.size = 64 ∧ corePermutations.size = 64 ∧
      atlasCodes.size = 53 ∧ housePermutation.size = 5 := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43ClassificationData
