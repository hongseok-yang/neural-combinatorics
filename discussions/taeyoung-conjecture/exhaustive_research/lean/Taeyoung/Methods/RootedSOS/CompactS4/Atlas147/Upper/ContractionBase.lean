import Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Upper.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Upper.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Upper
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 4565668536374289039360) ∧
  shiftedEncoding 9131337072748578078721 4565668536374289039360 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    3476221990327298393341673128867090857705511235870171165156772761443593610235644001648640 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Upper
