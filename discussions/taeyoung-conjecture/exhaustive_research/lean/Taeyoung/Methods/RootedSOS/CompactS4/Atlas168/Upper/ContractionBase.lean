import Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Upper.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Upper.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Upper
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 23978025660288054067200) ∧
  shiftedEncoding 47956051320576108134401 23978025660288054067200 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    2644500597577245064883537849952108594912177027607194276217153703791421936026510653574348800 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Upper
