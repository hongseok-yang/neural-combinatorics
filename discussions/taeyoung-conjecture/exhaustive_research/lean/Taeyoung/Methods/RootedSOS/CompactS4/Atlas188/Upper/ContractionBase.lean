import Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Upper.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Upper.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Upper
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 24519333363647965839360) ∧
  shiftedEncoding 49038666727295931678721 24519333363647965839360 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    2891509478585002639099723227476192610248311344661627164919212783012163659638828126100848640 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Upper
