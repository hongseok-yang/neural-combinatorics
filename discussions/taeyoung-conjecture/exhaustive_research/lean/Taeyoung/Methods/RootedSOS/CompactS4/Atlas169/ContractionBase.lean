import Taeyoung.Methods.RootedSOS.CompactS4.Atlas169.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas169.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas169
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 2284514542298854195200) ∧
  shiftedEncoding 4569029084597708390401 2284514542298854195200 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    217904246974042137542715030574266553003966786550544909097587965355656691293899181260800 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas169
