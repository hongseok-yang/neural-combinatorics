import Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas203
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 5600763352067943628800) ∧
  shiftedEncoding 11201526704135887257601 5600763352067943628800 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    7871887495992419451141392921478894903340020334254247861880266175913476117908764799795200 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas203
