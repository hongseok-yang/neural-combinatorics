import Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Middle.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Middle.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Middle
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 1774277577681172276838400000) ∧
  shiftedEncoding 3548555155362344553676800001 1774277577681172276838400000 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    79282300582340660228383752480588667310917051421938199962188042652140895506674234629398605253585263827353600000 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Middle
