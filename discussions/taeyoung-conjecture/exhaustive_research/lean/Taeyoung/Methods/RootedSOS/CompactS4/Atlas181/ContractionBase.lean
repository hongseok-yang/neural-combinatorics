import Taeyoung.Methods.RootedSOS.CompactS4.Atlas181.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas181.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas181
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 1871776069873391370240) ∧
  shiftedEncoding 3743552139746782740481 1871776069873391370240 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    98198657295435636594135309757945523052001565080041766147565951682662592897009356636160 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas181
