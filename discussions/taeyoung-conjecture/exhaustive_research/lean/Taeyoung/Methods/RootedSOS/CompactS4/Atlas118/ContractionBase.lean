import Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas118
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 635022438695959265280) ∧
  shiftedEncoding 1270044877391918530561 635022438695959265280 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    1300907066918656587330794077728380750873068646131675453746682922228767288141330513920 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas118
