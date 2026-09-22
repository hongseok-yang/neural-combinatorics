import Taeyoung.Methods.RootedSOS.CompactS4.Atlas122.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas122.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas122
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 1705797525598788648960) ∧
  shiftedEncoding 3411595051197577297921 1705797525598788648960 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    67732936954052604542515309385459902277548158068712715096982315554895287659430454231040 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas122
