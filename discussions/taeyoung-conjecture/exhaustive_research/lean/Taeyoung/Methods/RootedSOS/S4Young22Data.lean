import Taeyoung.Methods.RootedSOS.S4JsonData

namespace Taeyoung.Methods.RootedSOS.S4Young22Data

private def source : String :=
  include_str ".."/".."/".."/".."/"experiments"/"s4_lean_common_young_22.json"

def data : Array (Array Int) := eval% S4JsonData.decodeFieldFrom source "data"

def entry (a : Fin 352) (i : Fin 34) : Int :=
  (data[a.1]?.getD #[])[i.1]?.getD 0

def shapeValid : Bool := data.size == 352 && data.all (fun row => row.size == 34)

theorem shape_valid : shapeValid = true := by decide +kernel

end Taeyoung.Methods.RootedSOS.S4Young22Data
