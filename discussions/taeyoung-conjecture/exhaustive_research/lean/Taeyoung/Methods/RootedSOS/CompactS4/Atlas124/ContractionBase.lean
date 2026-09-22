import Taeyoung.Methods.RootedSOS.CompactS4.Atlas124.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas124.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas124
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 3792007331066039500800) ∧
  shiftedEncoding 7584014662132079001601 3792007331066039500800 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    1654118657008949656694860227666596298322225049651573782839852217402394106019947557683200 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas124
