import Taeyoung.Methods.RootedSOS.IntervalCoefficients

/-! Integer coefficient evaluation on p = (3+s)/4. -/

open Finset
open scoped BigOperators
namespace Taeyoung.Methods.RootedSOS

def quarterIntervalCoefficient (n : Nat) (a b c : Int) (j : Fin 6) : Int :=
  ∑ i : Fin 4, if i.1 ≤ n then
    (n.choose i.1 * (256 / 4^n) * 3^(n-i.1) : Nat) *
      ((if j.1 = i.1 then a else 0) +
       (if j.1 = i.1+1 then b else 0) +
       (if j.1 = i.1+2 then c else 0)) else 0

theorem quarterIntervalCoefficient_eval (n : Nat) (hn : n ≤ 3)
    (a b c : Int) (s : Real) :
    (∑ j : Fin 6, (quarterIntervalCoefficient n a b c j : Real)*s^j.1) =
      256*((3+s)/4)^n*((a : Real)+(b : Real)*s+(c : Real)*s^2) := by
  interval_cases n <;>
    simp [quarterIntervalCoefficient, Fin.sum_univ_succ] <;> push_cast <;> ring

#print axioms quarterIntervalCoefficient_eval
end Taeyoung.Methods.RootedSOS
