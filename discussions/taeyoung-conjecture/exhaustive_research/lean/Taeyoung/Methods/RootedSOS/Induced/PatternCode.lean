import Taeyoung.Methods.RootedSOS.Induced.Relabeling

/-! An explicit code for a relabelled pattern, with no additional enumeration. -/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS.Induced

variable {E : Type*} [Fintype E] [DecidableEq E] {n : Nat}

def patternCode (e : E ≃ Fin n) (p : E → Fin 2) : Fin (2^n) :=
  finFunctionFinEquiv (fun i => p (e.symm i))

theorem bits_patternCode (e : E ≃ Fin n) (p : E → Fin 2) (i : E) :
    finFunctionFinEquiv.symm (patternCode e p) (e i) = p i := by
  simp [patternCode]

theorem patternCode_val (e : E ≃ Fin n) (p : E → Fin 2) :
    (patternCode e p).val = ∑ i, (p i).val * 2^(e i).val := by
  change (∑ i : Fin n, (p (e.symm i)).val * 2^i.val) = _
  rw [← e.sum_comp (fun i => (p (e.symm i)).val * 2^i.val)]
  simp only [Equiv.symm_apply_apply]

end Taeyoung.Methods.RootedSOS.Induced
