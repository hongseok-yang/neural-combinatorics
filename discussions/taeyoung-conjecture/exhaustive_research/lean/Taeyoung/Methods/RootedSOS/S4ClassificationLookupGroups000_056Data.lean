import Taeyoung.Methods.RootedSOS.S4JsonData

namespace Taeyoung.Methods.RootedSOS.S4ClassificationLookupGroups000_056Data

set_option maxRecDepth 1000000

private def source : String :=
  include_str ".."/".."/".."/".."/"experiments"/"s4_lean_classification_manifest_lookup_groups_000_056.json"

def data : Array Int :=
  eval% S4JsonData.decodeFieldFrom source "data"

def shapeValid : Bool := data.size == 57

theorem shape_valid : shapeValid = true := by decide +kernel

end Taeyoung.Methods.RootedSOS.S4ClassificationLookupGroups000_056Data
