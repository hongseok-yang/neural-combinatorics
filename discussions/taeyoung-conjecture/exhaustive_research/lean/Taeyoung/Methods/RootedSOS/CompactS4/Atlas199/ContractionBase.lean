import Taeyoung.Methods.RootedSOS.CompactS4.Atlas199.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas199.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas199
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 9316486094214469386240) ∧
  shiftedEncoding 18632972188428938772481 9316486094214469386240 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    60269633050188319789586156394943013991963156939803180348860282836770598715256847437660160 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas199
