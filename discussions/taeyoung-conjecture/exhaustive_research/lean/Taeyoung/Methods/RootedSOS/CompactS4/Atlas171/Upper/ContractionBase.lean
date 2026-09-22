import Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Upper.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Upper.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Upper
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 14321045316352310968320) ∧
  shiftedEncoding 28642090632704621936641 14321045316352310968320 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    336502939977751950547630211548674893426272871474876628534148740125599478406786903099310080 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Upper
