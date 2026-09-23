import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Lower.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Lower.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Lower
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 126073557283543205806080) ∧
  shiftedEncoding 252147114567086411612161 126073557283543205806080 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    2021091683986220294047716486684094582171722095419536747467906236174533645345098191190485893120 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Lower
