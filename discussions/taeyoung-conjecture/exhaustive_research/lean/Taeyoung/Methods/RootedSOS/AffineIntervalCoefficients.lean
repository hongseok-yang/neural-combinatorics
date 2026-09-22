import Taeyoung.Methods.RootedSOS.IntervalCoefficients

/-! Integer polynomial coefficients for an arbitrary rational affine interval. -/

open Finset
open scoped BigOperators
namespace Taeyoung.Methods.RootedSOS

def affineIntervalCoefficient (A B Q n : Nat) (a b c : Int) (j : Fin 6) : Int :=
  ∑ i : Fin 4, if i.1 ≤ n then
    (n.choose i.1 * Q^(5-n) * A^(n-i.1) * B^i.1 : Nat) *
      ((if j.1 = i.1 then a else 0) +
       (if j.1 = i.1+1 then b else 0) +
       (if j.1 = i.1+2 then c else 0)) else 0

theorem affineIntervalCoefficient_eval (A B Q n : Nat) (hQ : 0 < Q) (hn : n ≤ 3)
    (a b c : Int) (s : Real) :
    (∑ j : Fin 6, (affineIntervalCoefficient A B Q n a b c j : Real)*s^j.1) =
      (Q : Real)^5*(((A : Real)+(B : Real)*s)/Q)^n *
        ((a : Real)+(b : Real)*s+(c : Real)*s^2) := by
  have hq : (Q : Real) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hQ)
  interval_cases n <;>
    simp [affineIntervalCoefficient, Fin.sum_univ_succ] <;>
    push_cast <;> field_simp [hq] <;> ring

#print axioms affineIntervalCoefficient_eval
end Taeyoung.Methods.RootedSOS
