import Taeyoung.Methods.RootedSOS.IntervalCoefficients

/-! Small Bernstein identities for the induced degree-five interval certificate. -/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS.Induced

def basis (n : Nat) (s : Real) (k : Nat) : Real := s^k*(1-s)^(n-k)

theorem basis_nonneg (n k : Nat) {s : Real} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ basis n s k := mul_nonneg (pow_nonneg hs0 _) (pow_nonneg (sub_nonneg.mpr hs1) _)

def quadraticCoefficient (a b c : Int) (k : Fin 6) : Int :=
  (Nat.choose 3 k.1 : Int)*a +
    (if 1 ≤ k.1 then (Nat.choose 3 (k.1-1) : Int)*b else 0) +
    (if 2 ≤ k.1 then (Nat.choose 3 (k.1-2) : Int)*c else 0)

theorem quadraticCoefficient_eval (a b c : Int) (s : Real) :
    (∑ k : Fin 6, (quadraticCoefficient a b c k : Real)*basis 5 s k.1) =
      (a : Real)*(1-s)^2+(b : Real)*s*(1-s)+(c : Real)*s^2 := by
  simp [quadraticCoefficient, basis, Fin.sum_univ_succ]
  push_cast
  ring

theorem constantCoefficient_eval (a : Int) (s : Real) :
    (∑ k : Fin 6, ((Nat.choose 5 k.1 : Int)*a : Real)*basis 5 s k.1) = a := by
  simp [basis, Fin.sum_univ_succ]
  push_cast
  norm_num [Nat.choose]
  ring

def bernstein4 (u : Fin 5 → Int) (s : Real) : Real :=
  ∑ k : Fin 5, (Nat.choose 4 k.1 : Real)*(u k : Real)*basis 4 s k.1

def liftLeft (u : Fin 5 → Int) (k : Fin 6) : Int :=
  if h : k.1 < 5 then (Nat.choose 4 k.1 : Int)*u ⟨k.1,h⟩ else 0

def liftRight (u : Fin 5 → Int) (k : Fin 6) : Int :=
  if h : 0 < k.1 then (Nat.choose 4 (k.1-1) : Int)*u ⟨k.1-1,by omega⟩ else 0

theorem liftLeft_eval (u : Fin 5 → Int) (s : Real) :
    (∑ k : Fin 6, (liftLeft u k : Real)*basis 5 s k.1) = (1-s)*bernstein4 u s := by
  simp [liftLeft, bernstein4, basis, Fin.sum_univ_succ]
  push_cast
  ring

theorem liftRight_eval (u : Fin 5 → Int) (s : Real) :
    (∑ k : Fin 6, (liftRight u k : Real)*basis 5 s k.1) = s*bernstein4 u s := by
  simp [liftRight, bernstein4, basis, Fin.sum_univ_succ]
  push_cast
  ring

def penaltyCoefficient (plain edge : Int) (u ua ub : Fin 5 → Int) (k : Fin 6) : Int :=
  liftLeft (fun j => edge*u j-plain*ua j) k + liftRight (fun j => edge*u j-plain*ub j) k

theorem penaltyCoefficient_eval (plain edge : Int) (u ua ub : Fin 5 → Int)
    (ha : ∀ k, 2*ua k = u k) (hb : ∀ k, 3*ub k = 2*u k) (s : Real) :
    (∑ k : Fin 6, (penaltyCoefficient plain edge u ua ub k : Real)*basis 5 s k.1) =
      bernstein4 u s*((edge : Real)-(3+s)/6*(plain : Real)) := by
  have hA (k : Fin 5) : (ua k : Real) = (u k : Real)/2 := by
    have h : (2 : Real)*(ua k : Real) = (u k : Real) := by exact_mod_cast ha k
    linarith
  have hB (k : Fin 5) : (ub k : Real) = 2*(u k : Real)/3 := by
    have h : (3 : Real)*(ub k : Real) = 2*(u k : Real) := by exact_mod_cast hb k
    linarith
  simp only [penaltyCoefficient, Int.cast_add, add_mul, Finset.sum_add_distrib]
  rw [liftLeft_eval, liftRight_eval]
  simp only [bernstein4, basis, Fin.sum_univ_succ]
  push_cast
  simp only [hA, hB]
  ring

end Taeyoung.Methods.RootedSOS.Induced
