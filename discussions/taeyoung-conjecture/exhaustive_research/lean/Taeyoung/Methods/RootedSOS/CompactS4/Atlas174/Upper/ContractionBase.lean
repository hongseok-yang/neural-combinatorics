import Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 23926132416645719654400) ∧
  shiftedEncoding 47852264833291439308801 23926132416645719654400 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    2621681894677138147653167266193402382387852051788254321031981597644493765398735439894937600 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper
