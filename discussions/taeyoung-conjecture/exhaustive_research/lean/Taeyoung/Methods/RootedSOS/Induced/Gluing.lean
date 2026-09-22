import Taeyoung.Methods.RootedSOS.Induced.Relabeling
import Taeyoung.Methods.RootedSOS.Induced.BranchGram

/-!
Two induced flags are glued at their roots. Only the edges between their branch
sets remain unspecified. Summing their completions recovers a conditional
product, which is the positive Gram expression proved in `BranchGram`.
-/

open Finset MeasureTheory
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS.Induced

variable {I J R B C : Type*}
  [Fintype I] [Fintype J] [Fintype R] [Fintype B] [Fintype C]
  [DecidableEq I] [DecidableEq J] [DecidableEq R] [DecidableEq B] [DecidableEq C]

def leftVertex : I ⊕ J → I ⊕ (J ⊕ J) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
def rightVertex : I ⊕ J → I ⊕ (J ⊕ J) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)

def gluedPairs (root : R → I × I) (branch : B → (I ⊕ J) × (I ⊕ J))
    (cross : C → J × J) : (R ⊕ (B ⊕ B)) ⊕ C → (I ⊕ (J ⊕ J)) × (I ⊕ (J ⊕ J)) :=
  Sum.elim (Sum.elim
    (fun e => (Sum.inl (root e).1, Sum.inl (root e).2))
    (Sum.elim (fun e => (leftVertex (branch e).1, leftVertex (branch e).2))
      (fun e => (rightVertex (branch e).1, rightVertex (branch e).2))))
    (fun e => (Sum.inr (Sum.inl (cross e).1), Sum.inr (Sum.inr (cross e).2)))

def gluedPattern (root : R → Fin 2) (a b : B → Fin 2) (c : C → Fin 2) :
    (R ⊕ (B ⊕ B)) ⊕ C → Fin 2 := Sum.elim (Sum.elim root (Sum.elim a b)) c

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def joinAssignment (q : (I → Ω) × ((J → Ω) × (J → Ω))) : I ⊕ (J ⊕ J) → Ω :=
  Sum.elim q.1 (Sum.elim q.2.1 q.2.2)

def sumTripleSplit : ((I ⊕ (J ⊕ J)) → Ω) ≃ᵐ
    ((I → Ω) × ((J → Ω) × (J → Ω))) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ (J ⊕ J) => Ω)).trans
    ((MeasurableEquiv.refl _).prodCongr
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ J => Ω)))

theorem measurePreserving_sumTripleSplit :
    MeasurePreserving (sumTripleSplit (I := I) (J := J) (Ω := Ω))
      (Taeyoung.assignmentMeasure (I ⊕ (J ⊕ J)) μ)
      ((Taeyoung.assignmentMeasure I μ).prod
        ((Taeyoung.assignmentMeasure J μ).prod (Taeyoung.assignmentMeasure J μ))) := by
  exact
    ((MeasurePreserving.id (Taeyoung.assignmentMeasure I μ)).prod
      (measurePreserving_sumPiEquivProdPi (fun _ : J ⊕ J => μ))).comp
      (measurePreserving_sumPiEquivProdPi (fun _ : I ⊕ (J ⊕ J) => μ))

@[simp] theorem join_sumTripleSplit (z : I ⊕ (J ⊕ J) → Ω) :
    joinAssignment (sumTripleSplit z) = z := by
  funext i
  rcases i with i | (i | i) <;> rfl

def branchWeight (pairs : B → (I ⊕ J) × (I ⊕ J)) (p : B → Fin 2)
    (W : Taeyoung.Graphon Ω μ) (q : (I → Ω) × (J → Ω)) : Real :=
  inducedWeight pairs p W (Sum.elim q.1 q.2)

/-- The omitted cross-edge probabilities sum to one. -/
theorem sum_completedWeight (rootPairs : R → I × I)
    (branchPairs : B → (I ⊕ J) × (I ⊕ J)) (crossPairs : C → J × J)
    (p : R → Fin 2) (a b : B → Fin 2) (W : Taeyoung.Graphon Ω μ)
    (q : (I → Ω) × ((J → Ω) × (J → Ω))) :
    (∑ c : C → Fin 2, inducedWeight (gluedPairs rootPairs branchPairs crossPairs)
      (gluedPattern p a b c) W (joinAssignment q)) =
      pairKernel (inducedWeight rootPairs p W) (branchWeight branchPairs a W)
        (branchWeight branchPairs b W) q := by
  simp only [inducedWeight, gluedPattern]
  rw [show (∑ c : C → Fin 2,
      patternWeight (fun e => W (joinAssignment q (gluedPairs rootPairs branchPairs crossPairs e).1)
        (joinAssignment q (gluedPairs rootPairs branchPairs crossPairs e).2))
        (Sum.elim (Sum.elim p (Sum.elim a b)) c)) =
      patternWeight (fun e => W (joinAssignment q (gluedPairs rootPairs branchPairs crossPairs (.inl e)).1)
        (joinAssignment q (gluedPairs rootPairs branchPairs crossPairs (.inl e)).2))
        (Sum.elim p (Sum.elim a b)) from
    patternWeight_completions (Equiv.refl _) _ _]
  rw [patternWeight_sum, patternWeight_sum]
  simp only [pairKernel, branchWeight, inducedWeight, patternWeight, gluedPairs,
    joinAssignment, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
  have hleft (v : I ⊕ J) : Sum.elim q.1 (Sum.elim q.2.1 q.2.2) (leftVertex v) =
      Sum.elim q.1 q.2.1 v := by cases v <;> rfl
  have hright (v : I ⊕ J) : Sum.elim q.1 (Sum.elim q.2.1 q.2.2) (rightVertex v) =
      Sum.elim q.1 q.2.2 v := by cases v <;> rfl
  simp only [hleft, hright, mul_assoc]

theorem sum_completedDensity (rootPairs : R → I × I)
    (branchPairs : B → (I ⊕ J) × (I ⊕ J)) (crossPairs : C → J × J)
    (p : R → Fin 2) (a b : B → Fin 2) (W : Taeyoung.Graphon Ω μ) :
    (∑ c : C → Fin 2, inducedDensity (gluedPairs rootPairs branchPairs crossPairs)
      (gluedPattern p a b c) W) =
      ∫ q, pairKernel (inducedWeight rootPairs p W) (branchWeight branchPairs a W)
        (branchWeight branchPairs b W) q ∂
        ((Taeyoung.assignmentMeasure I μ).prod
          ((Taeyoung.assignmentMeasure J μ).prod (Taeyoung.assignmentMeasure J μ))) := by
  simp only [inducedDensity]
  rw [← integral_finsetSum _ (fun c _ => integrable_inducedWeight _ _ W)]
  have he (z : I ⊕ (J ⊕ J) → Ω) :=
    sum_completedWeight rootPairs branchPairs crossPairs p a b W (sumTripleSplit z)
  simp only [join_sumTripleSplit] at he
  simp_rw [he]
  exact measurePreserving_sumTripleSplit.integral_comp' _

theorem measurable_branchWeight (pairs : B → (I ⊕ J) × (I ⊕ J)) (p : B → Fin 2)
    (W : Taeyoung.Graphon Ω μ) : Measurable (branchWeight pairs p W) := by
  apply (measurable_inducedWeight pairs p W).comp
  apply measurable_pi_lambda
  intro i
  rcases i with i | i
  · exact (measurable_pi_apply i).comp measurable_fst
  · exact (measurable_pi_apply i).comp measurable_snd

theorem integrable_rawPair (rootPairs : R → I × I)
    (branchPairs : B → (I ⊕ J) × (I ⊕ J))
    (p : R → Fin 2) (a b : B → Fin 2) (W : Taeyoung.Graphon Ω μ) :
    Integrable (pairKernel (inducedWeight rootPairs p W) (branchWeight branchPairs a W)
      (branchWeight branchPairs b W))
      ((Taeyoung.assignmentMeasure I μ).prod
        ((Taeyoung.assignmentMeasure J μ).prod (Taeyoung.assignmentMeasure J μ))) := by
  have hm : Measurable (pairKernel (inducedWeight rootPairs p W) (branchWeight branchPairs a W)
      (branchWeight branchPairs b W)) :=
    (((measurable_inducedWeight rootPairs p W).comp measurable_fst).mul
      ((measurable_branchWeight branchPairs a W).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))).mul
      ((measurable_branchWeight branchPairs b W).comp
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  apply (integrable_const (1 : Real)).mono' hm.aestronglyMeasurable
  filter_upwards [] with q
  have hr0 := inducedWeight_nonneg rootPairs p W q.1
  have hr1 := inducedWeight_le_one rootPairs p W q.1
  have ha0 := inducedWeight_nonneg branchPairs a W (Sum.elim q.1 q.2.1)
  have ha1 := inducedWeight_le_one branchPairs a W (Sum.elim q.1 q.2.1)
  have hb0 := inducedWeight_nonneg branchPairs b W (Sum.elim q.1 q.2.2)
  have hb1 := inducedWeight_le_one branchPairs b W (Sum.elim q.1 q.2.2)
  dsimp only [pairKernel, branchWeight]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hr0 ha0) hb0)]
  exact (mul_le_mul (mul_le_mul hr1 ha1 ha0 (by positivity)) hb1 hb0
    (by positivity)).trans_eq (by norm_num)

end Taeyoung.Methods.RootedSOS.Induced
