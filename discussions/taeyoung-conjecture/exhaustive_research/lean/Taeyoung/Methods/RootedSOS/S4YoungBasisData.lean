import Taeyoung.Methods.RootedSOS.S4Flags
import Taeyoung.Methods.RootedSOS.S4JsonData

namespace Taeyoung.Methods.RootedSOS.S4YoungBasisData

set_option maxRecDepth 100000

private def source : String :=
  include_str ".."/".."/".."/".."/"experiments"/"s4_lean_common_basis.json"

def basisIndices : Array Nat :=
  eval% S4JsonData.decodeFieldFrom source "basis_indices"

def rawGroupKeys : Array (Array Nat) :=
  eval% S4JsonData.decodeFieldFrom source "raw_group_keys"

def rawGroupKey (row : Fin 143) : Nat × Nat :=
  let entry := rawGroupKeys[row.1]?.getD #[]
  (entry[0]?.getD 209, entry[1]?.getD 4)

def shapeValid : Bool :=
  basisIndices.size == 352 &&
  rawGroupKeys.size == 143 && rawGroupKeys.all (fun row => row.size == 2)

theorem shape_valid : shapeValid = true := by
  decide +kernel

def basisOrderValid : Bool :=
  decide (∀ a : Fin 352, (basisIndices[a.1]?).getD 1024 = S4Flags.basisIndex a)

theorem basis_order_valid : basisOrderValid = true := by
  decide +kernel

end Taeyoung.Methods.RootedSOS.S4YoungBasisData
