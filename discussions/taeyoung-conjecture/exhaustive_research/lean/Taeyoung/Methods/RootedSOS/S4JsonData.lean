import Mathlib.Lean.Json
import Mathlib.Tactic.Eval

/-! Small JSON decoder shared by the split S4 certificate-data modules. -/

namespace Taeyoung.Methods.RootedSOS.S4JsonData

def decodeFieldFrom {α : Type} [Lean.FromJson α] [Inhabited α]
    (contents key : String) : α :=
  let json := match Lean.Json.parse contents with
  | .ok value => value
  | .error _ => Lean.Json.null
  match (json.getObjVal? key).bind Lean.fromJson? with
  | .ok value => value
  | .error _ => default

end Taeyoung.Methods.RootedSOS.S4JsonData
