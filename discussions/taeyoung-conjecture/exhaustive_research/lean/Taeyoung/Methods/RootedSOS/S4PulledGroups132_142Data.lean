import Taeyoung.Methods.RootedSOS.S4JsonData

namespace Taeyoung.Methods.RootedSOS.S4PulledGroups132_142Data

set_option maxRecDepth 100000

private def source : String :=
  include_str ".."/".."/".."/".."/"experiments"/"s4_lean_common_groups_132_142.json"
def data : Array (Array (Array (Array Int))) :=
  eval% S4JsonData.decodeFieldFrom source "pulled_groups"
def groupEntries (row block : Nat) : Array (Array Int) :=
  ((data[row]?.getD #[])[block]?).getD #[]
def shapeValid : Bool := data.size == 11 && data.all (fun group =>
  group.size == 5 && group.all (fun block => block.all (fun entry => entry.size == 3)))
theorem shape_valid : shapeValid = true := by decide +kernel

end Taeyoung.Methods.RootedSOS.S4PulledGroups132_142Data
