import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.RightData
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block00
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block01
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block02
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block03
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block04
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block05
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block06
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block07
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block08
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block09

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper
def expandedRight (k : Fin 5820) (u : Fin 4) : Int :=
  if k.1 < 1024 then
    let i := (k.1-0)/32
    let j := (k.1-0)%32
    if u.1 = 0 then 24*Block00.H i j
    else if u.1 = 1 then 24*(Block00.H i (32+j)+Block00.H (32+i) j)
    else if u.1 = 2 then 24*Block00.H (32+i) (32+j)
    else 24*Block05.H i j else
  if k.1 < 3728 then
    let i := (k.1-1024)/52
    let j := (k.1-1024)%52
    if u.1 = 0 then 24*Block01.H i j
    else if u.1 = 1 then 24*(Block01.H i (52+j)+Block01.H (52+i) j)
    else if u.1 = 2 then 24*Block01.H (52+i) (52+j)
    else 24*Block06.H i j else
  if k.1 < 4884 then
    let i := (k.1-3728)/34
    let j := (k.1-3728)%34
    if u.1 = 0 then 24*Block02.H i j
    else if u.1 = 1 then 24*(Block02.H i (34+j)+Block02.H (34+i) j)
    else if u.1 = 2 then 24*Block02.H (34+i) (34+j)
    else 24*Block07.H i j else
  if k.1 < 5784 then
    let i := (k.1-4884)/30
    let j := (k.1-4884)%30
    if u.1 = 0 then 24*Block03.H i j
    else if u.1 = 1 then 24*(Block03.H i (30+j)+Block03.H (30+i) j)
    else if u.1 = 2 then 24*Block03.H (30+i) (30+j)
    else 24*Block08.H i j else
  
    let i := (k.1-5784)/6
    let j := (k.1-5784)%6
    if u.1 = 0 then 24*Block04.H i j
    else if u.1 = 1 then 24*(Block04.H i (6+j)+Block04.H (6+i) j)
    else if u.1 = 2 then 24*Block04.H (6+i) (6+j)
    else 24*Block09.H i j

def rightCheck (k : Fin 5820) : Prop :=
  (∀ u : Fin 4, (right k u).natAbs ≤ 886145947167744 ∧ right k u = expandedRight k u) ∧
  rightEncoded k = ∑ u : Fin 4, right k u * (5941289563218743132161 : Int)^u.1
instance (k : Fin 5820) : Decidable (rightCheck k) := by unfold rightCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper
