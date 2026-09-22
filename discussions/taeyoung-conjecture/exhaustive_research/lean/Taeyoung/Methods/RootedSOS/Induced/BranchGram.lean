import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance
import Taeyoung.Foundation.DisjointUnion

/-!
Positivity for flags with any number of branch vertices. The two branch samples
are independent conditional on their roots. A nonnegative root-pattern weight
is included once, including when it specifies absent root edges.
-/

open Finset MeasureTheory
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS.Induced

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {ν : Measure X} {η : Measure Y} [IsProbabilityMeasure ν] [IsProbabilityMeasure η]

def pairKernel (root : X → Real) (f g : X × Y → Real) (q : X × (Y × Y)) : Real :=
  root q.1 * f (q.1, q.2.1) * g (q.1, q.2.2)

theorem integral_pairKernel (root : X → Real) (f g : X × Y → Real)
    (hint : Integrable (pairKernel root f g) (ν.prod (η.prod η))) :
    (∫ q, pairKernel root f g q ∂ν.prod (η.prod η)) =
      ∫ x, root x * (∫ y, f (x,y) ∂η) * (∫ y, g (x,y) ∂η) ∂ν := by
  rw [integral_prod _ hint]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [pairKernel, mul_assoc]
  rw [integral_const_mul, integral_prod_mul (fun y => f (x,y)) (fun y => g (x,y))]

theorem integrable_conditionalPair (root : X → Real) (f g : X × Y → Real)
    (hint : Integrable (pairKernel root f g) (ν.prod (η.prod η))) :
    Integrable (fun x => root x * (∫ y, f (x,y) ∂η) * (∫ y, g (x,y) ∂η)) ν := by
  have h := hint.integral_prod_left
  have he (x : X) : (∫ q, pairKernel root f g (x,q) ∂η.prod η) =
      root x * (∫ y, f (x,y) ∂η) * (∫ y, g (x,y) ∂η) := by
    simp only [pairKernel, mul_assoc]
    rw [integral_const_mul, integral_prod_mul (fun y => f (x,y)) (fun y => g (x,y))]
  simp_rw [he] at h
  exact h

/-- A PSD matrix gives a nonnegative combination of two-branch integrals. -/
theorem branchGram_nonneg {n : Nat} (root : X → Real) (f : Fin n → X × Y → Real)
    (G : Fin n → Fin n → Real)
    (hroot : ∀ x, 0 ≤ root x)
    (hG : ∀ v, 0 ≤ matrixQuadratic G v)
    (hint : ∀ i j, Integrable (pairKernel root (f i) (f j)) (ν.prod (η.prod η))) :
    0 ≤ ∑ i, ∑ j, G i j * (∫ q, pairKernel root (f i) (f j) q ∂ν.prod (η.prod η)) := by
  simp_rw [integral_pairKernel root _ _ (hint _ _)]
  have hnonneg : 0 ≤ ∫ x, root x * matrixQuadratic G (fun i => ∫ y, f i (x,y) ∂η) ∂ν :=
    integral_nonneg fun x => mul_nonneg (hroot x) (hG _)
  have hpoint (x : X) : root x * matrixQuadratic G (fun i => ∫ y, f i (x,y) ∂η) =
      ∑ i, ∑ j, G i j * (root x * (∫ y, f i (x,y) ∂η) * (∫ y, f j (x,y) ∂η)) := by
    simp only [matrixQuadratic, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hpoint] at hnonneg
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finset_sum _ (fun j _ =>
      (integrable_conditionalPair root (f i) (f j) (hint i j)).const_mul (G i j)))] at hnonneg
  simp_rw [integral_finsetSum _ (fun j _ =>
    (integrable_conditionalPair root (f _) (f j) (hint _ j)).const_mul (G _ j)),
    integral_const_mul] at hnonneg
  exact hnonneg

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The root block and two branch blocks use their ordinary product measures. -/
def tripleSplit (m r : Nat) : (Fin (m + (r + r)) → Ω) ≃ᵐ
    ((Fin m → Ω) × ((Fin r → Ω) × (Fin r → Ω))) :=
  (Taeyoung.assignmentSplit Ω m (r+r)).trans
    (MeasurableEquiv.refl _ |>.prodCongr (Taeyoung.assignmentSplit Ω r r))

theorem measurePreserving_tripleSplit (m r : Nat) :
    MeasurePreserving (tripleSplit (Ω := Ω) m r)
      (Taeyoung.assignmentMeasure (Fin (m+(r+r))) μ)
      ((Taeyoung.assignmentMeasure (Fin m) μ).prod
        ((Taeyoung.assignmentMeasure (Fin r) μ).prod (Taeyoung.assignmentMeasure (Fin r) μ))) := by
  exact ((MeasurePreserving.id _).prod (Taeyoung.measurePreserving_assignmentSplit r r)).comp
    (Taeyoung.measurePreserving_assignmentSplit m (r+r))

theorem integral_tripleSplit (m r : Nat)
    (f : ((Fin m → Ω) × ((Fin r → Ω) × (Fin r → Ω))) → Real) :
    (∫ z, f (tripleSplit (Ω := Ω) m r z) ∂Taeyoung.assignmentMeasure (Fin (m+(r+r))) μ) =
      ∫ q, f q ∂((Taeyoung.assignmentMeasure (Fin m) μ).prod
        ((Taeyoung.assignmentMeasure (Fin r) μ).prod (Taeyoung.assignmentMeasure (Fin r) μ))) :=
  (measurePreserving_tripleSplit m r).integral_comp' f

end Taeyoung.Methods.RootedSOS.Induced
