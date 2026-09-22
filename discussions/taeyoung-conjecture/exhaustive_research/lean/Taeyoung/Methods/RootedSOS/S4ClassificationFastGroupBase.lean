import Taeyoung.Methods.RootedSOS.S4ClassificationLookupBase
import Taeyoung.Methods.RootedSOS.S4ClassificationLookupGroups000_056Data

namespace Taeyoung.Methods.RootedSOS.S4Classification

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

def fastGroupEncodedRow (index : Fin 57) : Nat :=
  if index.1 < 57 then
    ((S4ClassificationLookupGroups000_056Data.data[index.1 - 0]?).getD 0).natAbs
  else 0

def fastWitnessGroup (index : Fin 57) (left right : Fin 16) : Fin 143 :=
  ⟨fastGroupEncodedRow index / 143 ^ (16 * left.1 + right.1) % 143,
    Nat.mod_lt _ (by decide)⟩

def fastGroupValid (index : Fin 57) (left right : Fin 16) : Bool :=
  fastWitnessGroup index left right == witnessGroup index left right

end Taeyoung.Methods.RootedSOS.S4Classification
