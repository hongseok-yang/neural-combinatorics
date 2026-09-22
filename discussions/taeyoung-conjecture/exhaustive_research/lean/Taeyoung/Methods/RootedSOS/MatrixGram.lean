import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance
import Taeyoung.Methods.RootedSOS.FlagGram

/-! Interpret a directly specified positive Gram matrix in the existing
shared-Bernoulli flag framework. All denominators are factored out once. -/

open Finset MeasureTheory
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

variable {n : Nat}

def matrixCorrection (denominator : Nat) (G : Fin n → Fin n → Int)
    (i j : Fin n) : Rat :=
  (G i j : Rat) / denominator - if i = j then 1 else 0

theorem matrixCorrection_cast (denominator : Nat) (G : Fin n → Fin n → Int)
    (i j : Fin n) :
    (matrixCorrection denominator G i j : Real) =
      (G i j : Real) / denominator - if i = j then 1 else 0 := by
  by_cases h : i = j <;> simp [matrixCorrection, h]

private theorem correction_cancels_diagonal
    (R : Fin n → Fin n → Real) (x : Fin n → Real) :
    (∑ i, x i ^ 2) +
        ∑ i, ∑ j, x i * (R i j - if i = j then 1 else 0) * x j =
      matrixQuadratic R x := by
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  have hdiag : (∑ i, ∑ j, x i * (if i = j then (1 : Real) else 0) * x j) =
      ∑ i, x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    simp [mul_ite, ite_mul, sq]
  rw [hdiag]
  dsimp [matrixQuadratic]
  ring

theorem factoredRatGramForm_matrixCorrection
    {I : Type*} [Fintype I]
    (denominator : Nat) (G : Fin n → Fin n → Int)
    (F : I → Fin n → Real) (v : I → Real) :
    factoredRatGramForm F (matrixCorrection denominator G) v =
      matrixQuadratic (fun i j => (G i j : Real)) (fun i => ∑ a, F a i * v a) /
        denominator := by
  unfold factoredRatGramForm
  simp_rw [matrixCorrection_cast]
  rw [correction_cancels_diagonal]
  simp only [matrixQuadratic, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem factoredRatGramForm_matrixCorrection_nonneg
    {I : Type*} [Fintype I]
    (denominator : Nat) (G : Fin n → Fin n → Int)
    (hG : ∀ x, 0 ≤ matrixQuadratic (fun i j => (G i j : Real)) x)
    (F : I → Fin n → Real) (v : I → Real) :
    0 ≤ factoredRatGramForm F (matrixCorrection denominator G) v := by
  rw [factoredRatGramForm_matrixCorrection]
  exact div_nonneg (hG _) (Nat.cast_nonneg _)

theorem expandedGramEntry_matrixCorrection
    {I : Type*} (denominator : Nat) (G : Fin n → Fin n → Int)
    (N : I → Fin n → Int) (H : I → I → Int)
    (hH : ∀ a b, H a b = ∑ j, (∑ i, N a i * G i j) * N b j)
    (a b : I) :
    expandedGramEntry (fun a i => (N a i : Real))
      (fun i j => (matrixCorrection denominator G i j : Real)) a b =
        (H a b : Real) / denominator := by
  unfold expandedGramEntry
  simp_rw [matrixCorrection_cast, mul_sub, Finset.sum_sub_distrib]
  have hd (j : Fin n) :
      (∑ i, (N a i : Real) * (if i = j then 1 else 0)) = N a j := by
    simp [mul_ite]
  have hc (u v : Real) : u + (v - u) = v := by ring
  simp_rw [hd, hc]
  rw [hH]
  push_cast
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (∑ i, (N a i : Real) * ((G i j : Real) / denominator)) =
      (∑ i, (N a i : Real) * (G i j : Real)) / denominator by
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  ring

theorem averagedFlagGramBlock_matrixCorrection_nonneg
    {k order : Nat} {A I : Type*} [Fintype A] [Fintype I]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (labelGraph : A → SimpleGraph (Fin k)) [∀ a, DecidableRel (labelGraph a).Adj]
    (neighbors : A → Finset (Fin k))
    (T : A → I → Real) (F : (Fin order × I) → Fin n → Real)
    (denominator : Nat) (G : Fin n → Fin n → Int)
    (hG : ∀ x, 0 ≤ matrixQuadratic (fun i j => (G i j : Real)) x)
    (W : Taeyoung.Graphon Ω μ) (s : Real) (x : Fin k → Ω) :
    0 ≤ averagedFlagGramBlock labelGraph neighbors T F
      (matrixCorrection denominator G) W s x := by
  unfold averagedFlagGramBlock
  apply bernoulli_average_nonneg (fun e => Taeyoung.edgeValue_nonneg W x e)
    (fun e => Taeyoung.edgeValue_le_one W x e)
  intro bits
  exact factoredRatGramForm_matrixCorrection_nonneg denominator G hG F _

end Taeyoung.Methods.RootedSOS
