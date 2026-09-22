import Taeyoung.Methods.RootedSOS.Induced.Bernstein

/-! Evaluate pointwise coefficient identities at arbitrary induced densities. -/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS.Induced

theorem evaluated_coefficient_identity {G J : Type*} [Fintype G] [Fintype J]
    (target empty gram residual density : G → Real) (multiplier : J → Real)
    (plain edge : J → G → Real) (D T p : Real)
    (h : ∀ g, D*target g-T*empty g = gram g+residual g+
      ∑ j, multiplier j*(edge j g-p*plain j g)) :
    D*(∑ g, target g*density g)-T*(∑ g, empty g*density g) =
      (∑ g, gram g*density g)+(∑ g, residual g*density g)+
        ∑ j, multiplier j*((∑ g, edge j g*density g)-p*(∑ g, plain j g*density g)) := by
  have hcross :
      (∑ g, (∑ j, multiplier j*(edge j g-p*plain j g))*density g) =
        ∑ j, multiplier j*((∑ g, edge j g*density g)-p*(∑ g, plain j g*density g)) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro g _
    ring
  calc
    _ = ∑ g, (D*target g-T*empty g)*density g := by
      simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
    _ = ∑ g, (gram g+residual g+∑ j, multiplier j*(edge j g-p*plain j g))*density g := by
      simp_rw [h]
    _ = _ := by
      simp only [add_mul, Finset.sum_add_distrib]
      rw [hcross]

end Taeyoung.Methods.RootedSOS.Induced
