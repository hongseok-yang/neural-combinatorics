import Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Lower.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Lower.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Lower
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 110742952883701921873920) ∧
  shiftedEncoding 221485905767403843747841 110742952883701921873920 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    1203245884588180300545333680950775157210102919442695835137109851242536614233429886443957780480 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Lower
