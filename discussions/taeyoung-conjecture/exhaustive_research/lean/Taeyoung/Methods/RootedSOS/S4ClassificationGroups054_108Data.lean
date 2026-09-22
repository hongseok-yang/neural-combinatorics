import Taeyoung.Methods.RootedSOS.S4JsonData

namespace Taeyoung.Methods.RootedSOS.S4ClassificationGroups054_108Data

set_option maxRecDepth 1000000

private def source : String :=
  include_str ".."/".."/".."/".."/"experiments"/"s4_lean_classification_manifest_groups_054_108.json"

def keys : Array (Array Nat) :=
  eval% S4JsonData.decodeFieldFrom source "keys"
def core6 : Array (Array (Array Bool)) :=
  eval% S4JsonData.decodeFieldFrom source "core6"
def core4 : Array (Array (Array Bool)) :=
  eval% S4JsonData.decodeFieldFrom source "core4"
def core2 : Array (Array (Array Bool)) :=
  eval% S4JsonData.decodeFieldFrom source "core2"
def standard : Array (Array (Array Bool)) :=
  eval% S4JsonData.decodeFieldFrom source "standard"

private def matrixShape (rows cols : Nat) (matrix : Array (Array Bool)) : Bool :=
  matrix.size == rows && matrix.all (fun row => row.size == cols)

def shapeValid : Bool :=
  keys.size == 55 && keys.all (fun key => key.size == 2) &&
  core6.size == 55 && core6.all (matrixShape 6 6) &&
  core4.size == 55 && core4.all (matrixShape 4 4) &&
  core2.size == 55 && core2.all (matrixShape 2 2) &&
  standard.size == 55 && standard.all (matrixShape 6 6)

theorem shape_valid : shapeValid = true := by decide +kernel

end Taeyoung.Methods.RootedSOS.S4ClassificationGroups054_108Data
