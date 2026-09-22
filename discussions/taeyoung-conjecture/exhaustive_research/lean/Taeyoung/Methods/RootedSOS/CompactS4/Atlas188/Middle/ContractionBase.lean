import Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Middle.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Middle.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Middle
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 1460765874702205255680000) ∧
  shiftedEncoding 2921531749404410511360001 1460765874702205255680000 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    36426080715779664750482833587875347951194497173260741795943748674265718837838125755787969822720000 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Middle
