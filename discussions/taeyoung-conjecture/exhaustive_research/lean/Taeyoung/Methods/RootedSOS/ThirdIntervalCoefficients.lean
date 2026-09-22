import Taeyoung.Methods.RootedSOS.IntervalCoefficients

/-! Integer coefficients for p = (2+s)/3. The factor 81 clears the
denominators of all isolated-edge factors and the four-chromatic targets. -/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

def thirdIntervalCoefficient (n : Nat) (a b c : Int) (j : Fin 6) : Int :=
  ∑ i : Fin 4, if i.1 ≤ n then
    (n.choose i.1 * (81 / 3^n) * 2^(n-i.1) : Nat) *
      ((if j.1 = i.1 then a else 0) +
       (if j.1 = i.1+1 then b else 0) +
       (if j.1 = i.1+2 then c else 0)) else 0

theorem thirdIntervalCoefficient_eval (n : Nat) (hn : n ≤ 3)
    (a b c : Int) (s : Real) :
    (∑ j : Fin 6, (thirdIntervalCoefficient n a b c j : Real) * s^j.1) =
      81 * ((2+s)/3)^n * ((a : Real)+(b : Real)*s+(c : Real)*s^2) := by
  interval_cases n <;>
    simp [thirdIntervalCoefficient, Fin.sum_univ_succ] <;> push_cast <;> ring

#print axioms thirdIntervalCoefficient_eval
end Taeyoung.Methods.RootedSOS
