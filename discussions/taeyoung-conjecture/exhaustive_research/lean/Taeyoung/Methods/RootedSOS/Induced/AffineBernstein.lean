import Taeyoung.Methods.RootedSOS.Induced.Bernstein

/-! Fixed-density multipliers on an arbitrary affine interval. -/

open Finset
open scoped BigOperators
namespace Taeyoung.Methods.RootedSOS.Induced

theorem penaltyCoefficient_eval_affine (plain edge : Int) (u ua ub : Fin 5 → Int)
    (a b : Real) (ha : ∀ k, (ua k : Real) = a*(u k : Real))
    (hb : ∀ k, (ub k : Real) = b*(u k : Real)) (s : Real) :
    (∑ k : Fin 6, (penaltyCoefficient plain edge u ua ub k : Real)*basis 5 s k.1) =
      bernstein4 u s*((edge : Real)-((1-s)*a+s*b)*(plain : Real)) := by
  simp only [penaltyCoefficient, Int.cast_add, add_mul, Finset.sum_add_distrib]
  rw [liftLeft_eval, liftRight_eval]
  simp only [bernstein4, basis, Fin.sum_univ_succ]
  push_cast
  simp only [ha, hb]
  ring

theorem penaltyCoefficient_eval_twoThirdsThreeQuarters (plain edge : Int)
    (u ua ub : Fin 5 → Int) (ha : ∀ k, 3*ua k = 2*u k)
    (hb : ∀ k, 4*ub k = 3*u k) (s : Real) :
    (∑ k : Fin 6, (penaltyCoefficient plain edge u ua ub k : Real)*basis 5 s k.1) =
      bernstein4 u s*((edge : Real)-(8+s)/12*(plain : Real)) := by
  have hA (k : Fin 5) : (ua k : Real) = ((2 : Real)/3)*(u k : Real) := by
    have h : (3 : Real)*(ua k : Real) = 2*(u k : Real) := by exact_mod_cast ha k
    linarith
  have hB (k : Fin 5) : (ub k : Real) = ((3 : Real)/4)*(u k : Real) := by
    have h : (4 : Real)*(ub k : Real) = 3*(u k : Real) := by exact_mod_cast hb k
    linarith
  have he := penaltyCoefficient_eval_affine plain edge u ua ub (2/3) (3/4) hA hB s
  rw [show (1-s)*((2 : Real)/3)+s*((3 : Real)/4) = (8+s)/12 by ring] at he
  exact he

#print axioms penaltyCoefficient_eval_twoThirdsThreeQuarters
end Taeyoung.Methods.RootedSOS.Induced
