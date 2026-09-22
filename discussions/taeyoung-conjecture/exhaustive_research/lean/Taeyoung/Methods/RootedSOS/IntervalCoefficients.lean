import Taeyoung.Methods.RootedSOS.PackedCoefficients
import Mathlib.Data.Nat.Choose.Basic

/-! Small integer coefficients for substituting p = (1+s)/2. The factor 16
clears every power-of-two denominator appearing in the S4 classification. -/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

def intervalCoefficient (n : Nat) (a b c : Int) (j : Fin 6) : Int :=
  ∑ i : Fin 4, if i.1 ≤ n then
    (n.choose i.1 * (16 / 2^n) : Nat) *
      ((if j.1 = i.1 then a else 0) +
       (if j.1 = i.1+1 then b else 0) +
       (if j.1 = i.1+2 then c else 0)) else 0

theorem intervalCoefficient_eval (n : Nat) (hn : n ≤ 3)
    (a b c : Int) (s : Real) :
    (∑ j : Fin 6, (intervalCoefficient n a b c j : Real) * s^j.1) =
      16 * ((1+s)/2)^n * ((a : Real)+(b : Real)*s+(c : Real)*s^2) := by
  interval_cases n <;>
    simp [intervalCoefficient, Fin.sum_univ_succ] <;> push_cast <;> ring

theorem group_sum_eval {G R : Type*} [Fintype G] [Fintype R] [DecidableEq R]
    (group : G → R) (a : G → Real) (f : R → Real) :
    (∑ g, a g * f (group g)) =
      ∑ r, (∑ g, if group g = r then a g else 0) * f r := by
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp

theorem group_coefficients_eval {G R J : Type*}
    [Fintype G] [Fintype R] [Fintype J] [DecidableEq R]
    (group : G → R) (a : G → J → Int) (b : R → J → Int)
    (hb : ∀ r j, (∑ g, if group g = r then a g j else 0) = b r j)
    (s : J → Real) (f : R → Real) :
    (∑ g, (∑ j, (a g j : Real)*s j) * f (group g)) =
      ∑ r, (∑ j, (b r j : Real)*s j) * f r := by
  rw [group_sum_eval group]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  simp_rw [← hb]
  push_cast
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  by_cases h : group g = r <;> simp [h]

end Taeyoung.Methods.RootedSOS
