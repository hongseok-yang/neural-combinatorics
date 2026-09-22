import Taeyoung.Methods.RootedSOS.Induced.BranchGram

/-! Finite sums of labelled flags may be used as the coordinates of a Gram block. -/

open Finset MeasureTheory
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS.Induced

variable {A B X Y : Type*} [Fintype A] [Fintype B]
  [MeasurableSpace X] [MeasurableSpace Y]
variable {ν : Measure X} {η : Measure Y} [IsProbabilityMeasure ν] [IsProbabilityMeasure η]

theorem pairKernel_sum (root : X → Real) (f : A → X × Y → Real)
    (g : B → X × Y → Real) (q : X × (Y × Y)) :
    pairKernel root (fun z => ∑ a, f a z) (fun z => ∑ b, g b z) q =
      ∑ a, ∑ b, pairKernel root (f a) (g b) q := by
  simp only [pairKernel, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem integrable_pairKernel_sum (root : X → Real) (f : A → X × Y → Real)
    (g : B → X × Y → Real)
    (hint : ∀ a b, Integrable (pairKernel root (f a) (g b)) (ν.prod (η.prod η))) :
    Integrable (pairKernel root (fun z => ∑ a, f a z) (fun z => ∑ b, g b z))
      (ν.prod (η.prod η)) := by
  simp_rw [show pairKernel root (fun z => ∑ a, f a z) (fun z => ∑ b, g b z) =
      (fun q => ∑ a, ∑ b, pairKernel root (f a) (g b) q) from funext (pairKernel_sum root f g)]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b

theorem integral_pairKernel_sum (root : X → Real) (f : A → X × Y → Real)
    (g : B → X × Y → Real)
    (hint : ∀ a b, Integrable (pairKernel root (f a) (g b)) (ν.prod (η.prod η))) :
    (∫ q, pairKernel root (fun z => ∑ a, f a z) (fun z => ∑ b, g b z) q ∂ν.prod (η.prod η)) =
      ∑ a, ∑ b, ∫ q, pairKernel root (f a) (g b) q ∂ν.prod (η.prod η) := by
  simp_rw [pairKernel_sum]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => hint a b)]
  apply Finset.sum_congr rfl
  intro a _
  exact integral_finsetSum _ (fun b _ => hint a b)

end Taeyoung.Methods.RootedSOS.Induced
