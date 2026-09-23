import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 2970644781609371566080) ∧
  shiftedEncoding 5941289563218743132161 2970644781609371566080 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    623006935674015781383664435603676638431690637636732777818523021678717808834728160133120 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper
