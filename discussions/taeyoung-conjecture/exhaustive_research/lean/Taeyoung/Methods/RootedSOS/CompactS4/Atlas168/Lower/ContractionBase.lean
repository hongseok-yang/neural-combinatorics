import Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 82988890483690470113280) ∧
  shiftedEncoding 165977780967380940226561 82988890483690470113280 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    379463335944277391541132136018003346489049845738558528955874565474742800158335960339626065920 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower
