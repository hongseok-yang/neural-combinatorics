import Taeyoung.Methods.RootedSOS.CompactS4.Atlas194.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas194.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas194
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 10867973443294395432960) ∧
  shiftedEncoding 21735946886588790865921 10867973443294395432960 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    111605156565856861905689070687167678865402492184522796920638107903081817911942578643927040 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas194
