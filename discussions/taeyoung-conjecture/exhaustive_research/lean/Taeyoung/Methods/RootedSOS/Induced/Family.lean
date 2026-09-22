import Taeyoung.Methods.RootedSOS.Induced.Gluing
import Taeyoung.Methods.RootedSOS.Induced.BranchSums

/-! A flag coordinate is an explicit finite sum of labelled branch patterns. -/

open Finset MeasureTheory
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS.Induced

variable {I J R B C : Type*}
  [Fintype I] [Fintype J] [Fintype R] [Fintype B] [Fintype C]
  [DecidableEq I] [DecidableEq J] [DecidableEq R] [DecidableEq B] [DecidableEq C]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {n : Nat}

def familyWeight (pairs : B → (I ⊕ J) × (I ⊕ J)) (size : Fin n → Nat)
    (member : (i : Fin n) → Fin (size i) → B → Fin 2) (W : Taeyoung.Graphon Ω μ)
    (i : Fin n) (q : (I → Ω) × (J → Ω)) : Real :=
  ∑ a, branchWeight pairs (member i a) W q

noncomputable def familyPair (rootPairs : R → I × I) (root : R → Fin 2)
    (pairs : B → (I ⊕ J) × (I ⊕ J)) (size : Fin n → Nat)
    (member : (i : Fin n) → Fin (size i) → B → Fin 2) (W : Taeyoung.Graphon Ω μ)
    (i j : Fin n) : Real :=
  ∫ q, pairKernel (inducedWeight rootPairs root W)
    (familyWeight pairs size member W i) (familyWeight pairs size member W j) q ∂
    ((Taeyoung.assignmentMeasure I μ).prod
      ((Taeyoung.assignmentMeasure J μ).prod (Taeyoung.assignmentMeasure J μ)))

theorem family_gram_nonneg (rootPairs : R → I × I) (root : R → Fin 2)
    (pairs : B → (I ⊕ J) × (I ⊕ J)) (size : Fin n → Nat)
    (member : (i : Fin n) → Fin (size i) → B → Fin 2) (W : Taeyoung.Graphon Ω μ)
    (G : Fin n → Fin n → Real) (hG : ∀ x, 0 ≤ matrixQuadratic G x) :
    0 ≤ ∑ i, ∑ j, G i j * familyPair rootPairs root pairs size member W i j := by
  apply branchGram_nonneg (inducedWeight rootPairs root W) (familyWeight pairs size member W) G
    (fun q => inducedWeight_nonneg rootPairs root W q) hG
  intro i j
  exact integrable_pairKernel_sum _ _ _
    (fun a b => integrable_rawPair rootPairs pairs root (member i a) (member j b) W)

theorem familyPair_expansion (rootPairs : R → I × I) (root : R → Fin 2)
    (pairs : B → (I ⊕ J) × (I ⊕ J)) (crossPairs : C → J × J) (size : Fin n → Nat)
    (member : (i : Fin n) → Fin (size i) → B → Fin 2) (W : Taeyoung.Graphon Ω μ)
    (i j : Fin n) :
    familyPair rootPairs root pairs size member W i j =
      ∑ a : Fin (size i), ∑ b : Fin (size j), ∑ c : C → Fin 2,
        inducedDensity (gluedPairs rootPairs pairs crossPairs)
          (gluedPattern root (member i a) (member j b) c) W := by
  unfold familyPair familyWeight
  rw [integral_pairKernel_sum _ _ _
    (fun a b => integrable_rawPair rootPairs pairs root (member i a) (member j b) W)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact (sum_completedDensity rootPairs pairs crossPairs root (member i a) (member j b) W).symm

end Taeyoung.Methods.RootedSOS.Induced
