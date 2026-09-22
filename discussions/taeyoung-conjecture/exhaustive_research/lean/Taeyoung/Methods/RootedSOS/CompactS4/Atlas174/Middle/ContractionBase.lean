import Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Middle.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Middle.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Middle
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 21257926135943840214480322560) ∧
  shiftedEncoding 42515852271887680428960645121 21257926135943840214480322560 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    1633704712409094015498486863296845240404992190190875732968735801341827040405596219499161395639713074550914615869440 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Middle
