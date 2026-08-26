import Mathlib.Lean.Json
import Mathlib.Tactic.Eval

/-!
# Machine-readable exact data for the Atlas 43 rooted SOS certificate

The certificate is kept in its compact JSON form, which is also consumed by
the independent Python checker.  `include_str` makes its contents part of the
Lean declaration, so changing the JSON invalidates this module.  Every parser
fallback below is deliberately an invalid empty/default value; later
entrywise certificate checks therefore fail if parsing or field lookup fails.

This module only exposes exact integers.  Conversion to rational Gram data and
the coefficient checker live in later modules.
-/

namespace Taeyoung.Methods.RootedSOS.Atlas43Data

set_option maxRecDepth 100000

private def source : String :=
  include_str ".."/".."/".."/".."/"experiments"/"house_atlas43_rational.json"

private def decodeFieldFrom {α : Type} [Lean.FromJson α] [Inhabited α]
    (contents key : String) : α :=
  let json := match Lean.Json.parse contents with
  | .ok value => value
  | .error _ => Lean.Json.null
  match (json.getObjVal? key).bind Lean.fromJson? with
  | .ok value => value
  | .error _ => default

def atlas : Nat := eval% decodeFieldFrom source "atlas"
def factorDenominator : Nat := eval% decodeFieldFrom source "factor_denominator"
def factors0 : Array (Array Int) := eval% decodeFieldFrom source "F0"
def factors1 : Array (Array Int) := eval% decodeFieldFrom source "F1"
def corrections : Array (Array Int) := eval% decodeFieldFrom source "corrections"
def orders : Array Nat := eval% decodeFieldFrom source "orders"
def diagonalDominanceMargins : Array (Array Int) :=
  eval% decodeFieldFrom source "dd_margins"

/-- Structural validation used by external diagnostics.  Mathematical checks
below access every required entry with explicit bounds, so they also fail on a
malformed shape.  We intentionally do not kernel-normalize this whole Boolean
at once: doing so needlessly expands both large factor arrays simultaneously. -/
noncomputable def shapeCheck : Bool :=
  atlas == 43 &&
  factorDenominator == 1000000 &&
  orders == #[107, 48] &&
  factors0.size == 128 && factors0.all (fun row ↦ row.size == 107) &&
  factors1.size == 64 && factors1.all (fun row ↦ row.size == 48) &&
  corrections.all (fun entry ↦
    entry.size == 5 &&
      ((entry[0]?).getD (-1) == 0 || (entry[0]?).getD (-1) == 1)) &&
  diagonalDominanceMargins.size == 2 &&
    diagonalDominanceMargins.all (fun entry ↦ entry.size == 2)

/-- Cheap header check; unlike `shapeCheck`, this does not traverse the factor
matrices. -/
theorem header_eq : atlas = 43 ∧ factorDenominator = 1000000 ∧ orders = #[107, 48] := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43Data
