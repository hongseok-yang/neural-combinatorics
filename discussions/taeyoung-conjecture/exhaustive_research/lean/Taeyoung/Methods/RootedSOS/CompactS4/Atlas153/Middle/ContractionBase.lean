import Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Middle.Right
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Middle.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Sparse
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Middle
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ 4010688790510229795635200) ∧
  shiftedEncoding 8021377581020459591270401 4010688790510229795635200 (List.ofFn fun u : Fin 4 => groupTotal g u) =
    2069978543568874836786245862453402446095018506837256884087150470567428631356786229567283729059020800 +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Middle
