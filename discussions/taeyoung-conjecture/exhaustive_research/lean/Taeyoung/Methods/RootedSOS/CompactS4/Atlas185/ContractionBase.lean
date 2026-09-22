import Taeyoung.Methods.RootedSOS.CompactS4.Atlas185.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas185.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas185
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 16629509451685507891200) ∧
  shiftedEncoding 33259018903371015782401 16629509451685507891200 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    611797559463638823522765185891178272166355946549460339386953913423749308789560767728844800 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas185
