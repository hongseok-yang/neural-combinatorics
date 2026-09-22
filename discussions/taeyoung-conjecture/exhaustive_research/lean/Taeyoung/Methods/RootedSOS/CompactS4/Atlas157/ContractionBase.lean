import Taeyoung.Methods.RootedSOS.CompactS4.Atlas157.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas157.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas157
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 1763874972814190837760) ∧
  shiftedEncoding 3527749945628381675521 1763874972814190837760 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    77439257403868294785843488018832920372198003533743285875712634382255968089607624458240 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas157
