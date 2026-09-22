import Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 9044007000044818268160) ∧
  shiftedEncoding 18088014000089636536321 9044007000044818268160 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    53522149434966089067264049495143087712263734056223351592843894895491277895120367153315840 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower
