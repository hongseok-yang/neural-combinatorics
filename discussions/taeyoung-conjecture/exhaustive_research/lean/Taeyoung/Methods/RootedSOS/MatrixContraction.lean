import Taeyoung.Methods.RootedSOS.PackedCoefficients

/-! Evaluate an exact integer matrix product against arbitrary real weights. -/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

theorem integer_contraction_eval {G K U : Type*} [Fintype G] [Fintype K] [Fintype U]
    (left : G → K → Int) (right : K → U → Int) (result : G → U → Int)
    (hresult : ∀ g u, result g u = ∑ k, left g k * right k u)
    (w : U → Real) (f : G → Real) :
    (∑ k, (∑ u, (right k u : Real)*w u) * (∑ g, (left g k : Real)*f g)) =
      ∑ g, (∑ u, (result g u : Real)*w u)*f g := by
  simp_rw [hresult]
  push_cast
  simp only [Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ k, ∑ g, ∑ u, (right k u : Real)*w u*((left g k : Real)*f g) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = ∑ g, ∑ k, ∑ u, (right k u : Real)*w u*((left g k : Real)*f g) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro k _
      ring

end Taeyoung.Methods.RootedSOS
