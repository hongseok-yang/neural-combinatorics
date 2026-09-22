import Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 21769087313152407306240) ∧
  shiftedEncoding 43538174626304814612481 21769087313152407306240 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    1796597835317101810991944667445438648137175970250810858151362206297840334065658609864540160 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper
