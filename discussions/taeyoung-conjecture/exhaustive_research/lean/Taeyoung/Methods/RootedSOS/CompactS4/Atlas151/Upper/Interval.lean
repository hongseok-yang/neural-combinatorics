import Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper.IntervalChecks0000
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper.IntervalChecks0026
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper.IntervalChecks0052
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper.IntervalChecks0078
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper.IntervalChecks0104
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper.IntervalChecks0130
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper
open Finset
theorem polynomialCheck_all (k : Fin 143) : polynomialCheck k := by
  by_cases h : k.1 < 26
  · let j : Fin 26 := ⟨k.1-0, by omega⟩
    have he : (⟨0+j.1, by omega⟩ : Fin 143) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using IntervalChecks_0000 j
  by_cases h : k.1 < 52
  · let j : Fin 26 := ⟨k.1-26, by omega⟩
    have he : (⟨26+j.1, by omega⟩ : Fin 143) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using IntervalChecks_0026 j
  by_cases h : k.1 < 78
  · let j : Fin 26 := ⟨k.1-52, by omega⟩
    have he : (⟨52+j.1, by omega⟩ : Fin 143) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using IntervalChecks_0052 j
  by_cases h : k.1 < 104
  · let j : Fin 26 := ⟨k.1-78, by omega⟩
    have he : (⟨78+j.1, by omega⟩ : Fin 143) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using IntervalChecks_0078 j
  by_cases h : k.1 < 130
  · let j : Fin 26 := ⟨k.1-104, by omega⟩
    have he : (⟨104+j.1, by omega⟩ : Fin 143) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using IntervalChecks_0104 j
  by_cases h : k.1 < 143
  · let j : Fin 13 := ⟨k.1-130, by omega⟩
    have he : (⟨130+j.1, by omega⟩ : Fin 143) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using IntervalChecks_0130 j
  omega

theorem group_polynomial_eval (g : Fin 143) (s : Real) :
    (∑ j : Fin 6, (polynomialCoefficient g j : Real)*s^j.1) =
      243*((2+1*s)/3)^(S4Classification.groupKey g).2 *
        ((groupTotal g 0 : Real)+(groupTotal g 1 : Real)*s+
          (groupTotal g 2 : Real)*s^2+(groupTotal g 3 : Real)*s*(1-s)) := by
  rw [show polynomialCoefficient g = affineIntervalCoefficient 2 1 3 (S4Classification.groupKey g).2
      (groupTotal g 0) (groupTotal g 1 + groupTotal g 3)
      (groupTotal g 2 - groupTotal g 3) from rfl]
  rw [affineIntervalCoefficient_eval 2 1 3 _ (by decide) (isolated_bound g)]
  norm_num only [Nat.cast_ofNat]
  push_cast
  ring

theorem target_coefficient_eval (r : Fin 143) (s : Real) :
    (∑ j : Fin 6, (targetCoefficient r j : Real)*s^j.1) =
      (if r = 99 then 243*23328000000000000 else 0) -
      (if r = 0 then 23328000000000000*((8)*s^0 + (38)*s^1 + (65)*s^2 + (64)*s^3 + (52)*s^4 + (16)*s^5) else 0) := by
  by_cases h : r = 99 <;> by_cases h0 : r = 0 <;>
    simp [targetCoefficient,Fin.sum_univ_succ,h,h0] <;> ring

theorem group_identity (s : Real) (f : Fin 143 → Real) :
    243*(∑ g : Fin 143,
      ((groupTotal g 0 : Real)+(groupTotal g 1 : Real)*s+
        (groupTotal g 2 : Real)*s^2+(groupTotal g 3 : Real)*s*(1-s)) *
        (((2+1*s)/3)^(S4Classification.groupKey g).2 * f (representative g))) =
      23328000000000000*(243*f 99-((8)*s^0 + (38)*s^1 + (65)*s^2 + (64)*s^3 + (52)*s^4 + (16)*s^5)*f 0) := by
  calc
    _ = ∑ g : Fin 143,
        (∑ j : Fin 6, (polynomialCoefficient g j : Real)*s^j.1)*f (representative g) := by
      simp only [Finset.mul_sum, group_polynomial_eval]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = ∑ r : Fin 143,
        (∑ j : Fin 6, (targetCoefficient r j : Real)*s^j.1)*f r :=
      group_coefficients_eval representative polynomialCoefficient targetCoefficient
        (fun r j => polynomialCheck_all r j) (fun j => s^j.1) f
    _ = _ := by
      simp only [target_coefficient_eval, sub_mul, ite_mul, zero_mul,
        Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring

#print axioms group_identity
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper
