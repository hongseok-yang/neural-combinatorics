import Taeyoung.Methods.RootedSOS.CompactS4.Atlas130.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas130.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas130
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 33223415680390605373440) ∧
  shiftedEncoding 66446831360781210746881 33223415680390605373440 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    9746913388128546955489717869553359453013430851382458249629269561226211324886768100039720960 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas130
