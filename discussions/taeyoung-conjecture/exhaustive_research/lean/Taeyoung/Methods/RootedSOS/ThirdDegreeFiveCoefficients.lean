import Taeyoung.Methods.RootedSOS.IntervalCoefficients

/-! The factor 243 also clears degree-five targets on p = (2+s)/3. -/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

def thirdDegreeFiveCoefficient (n : Nat) (a b c : Int) (j : Fin 6) : Int :=
  ∑ i : Fin 4, if i.1 ≤ n then
    (n.choose i.1 * (243 / 3^n) * 2^(n-i.1) : Nat) *
      ((if j.1 = i.1 then a else 0) +
       (if j.1 = i.1+1 then b else 0) +
       (if j.1 = i.1+2 then c else 0)) else 0

theorem thirdDegreeFiveCoefficient_eval (n : Nat) (hn : n ≤ 3)
    (a b c : Int) (s : Real) :
    (∑ j : Fin 6, (thirdDegreeFiveCoefficient n a b c j : Real) * s^j.1) =
      243 * ((2+s)/3)^n * ((a : Real)+(b : Real)*s+(c : Real)*s^2) := by
  interval_cases n <;>
    simp [thirdDegreeFiveCoefficient, Fin.sum_univ_succ] <;> push_cast <;> ring

#print axioms thirdDegreeFiveCoefficient_eval
end Taeyoung.Methods.RootedSOS
