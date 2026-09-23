import Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Upper.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Upper.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Upper
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 15202526499664013721600) ∧
  shiftedEncoding 30405052999328027443201 15202526499664013721600 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    427319846212454624615540226264620984936561726731219728849781056967160894448111011669606400 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Upper
