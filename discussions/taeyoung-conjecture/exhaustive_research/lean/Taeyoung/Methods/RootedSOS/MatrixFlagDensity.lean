import Taeyoung.Methods.RootedSOS.MatrixGram

/-! An integer positive Gram matrix gives a nonnegative combination of glued
flag densities. Its scalar denominator is unnecessary for this implication. -/

open Finset MeasureTheory
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

variable {k order n : Nat} {A I : Type*} [Fintype A] [Fintype I]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integer_flag_density_nonneg
    (labelGraph : A → SimpleGraph (Fin k)) [∀ a, DecidableRel (labelGraph a).Adj]
    (neighbors : A → Finset (Fin k)) (T : A → I → Real)
    (N : (Fin order × I) → Fin n → Int) (G : Fin n → Fin n → Int)
    (H : (Fin order × I) → (Fin order × I) → Int)
    (hG : ∀ x, 0 ≤ matrixQuadratic (fun i j => (G i j : Real)) x)
    (hH : ∀ a b, H a b = ∑ j, (∑ i, N a i * G i j) * N b j)
    (W : Taeyoung.Graphon Ω μ) (s : Real) :
    0 ≤ ∑ ui, ∑ vj, (H ui vj : Real) * s ^ (ui.1.1 + vj.1.1) *
      (∑ a, ∑ b, T a ui.2 * T b vj.2 *
        Taeyoung.homDensity (gluedRootedFlagGraph (labelGraph a) (labelGraph b)
          (neighbors a) (neighbors b)) W) := by
  let F := fun a i => (N a i : Real)
  let C := matrixCorrection 1 G
  have hnonneg : 0 ≤ ∫ x, averagedFlagGramBlock labelGraph neighbors T F C W s x
      ∂Taeyoung.assignmentMeasure (Fin k) μ :=
    integral_nonneg (fun x =>
      averagedFlagGramBlock_matrixCorrection_nonneg labelGraph neighbors T F 1 G hG W s x)
  rw [integral_averagedFlagGramBlock_eq_density_sum] at hnonneg
  have hexp (a b : Fin order × I) :
      expandedGramEntry F (fun i j => (C i j : Real)) a b = (H a b : Real) := by
    simpa only [Nat.cast_one, div_one] using
      expandedGramEntry_matrixCorrection 1 G N H hH a b
  have he : (∑ a, ∑ b, flagGramPairCoefficient T F C s a b *
      Taeyoung.homDensity (gluedRootedFlagGraph (labelGraph a) (labelGraph b)
        (neighbors a) (neighbors b)) W) =
      ∑ ui, ∑ vj, (H ui vj : Real) * s ^ (ui.1.1 + vj.1.1) *
        (∑ a, ∑ b, T a ui.2 * T b vj.2 *
          Taeyoung.homDensity (gluedRootedFlagGraph (labelGraph a) (labelGraph b)
            (neighbors a) (neighbors b)) W) := by
    simp only [flagGramPairCoefficient, hexp, Finset.sum_mul, Finset.mul_sum]
    rw [sum_comm_four]
    apply Finset.sum_congr rfl
    intro ui _
    apply Finset.sum_congr rfl
    intro vj _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rwa [he] at hnonneg

theorem two_layer_sum {d : Nat} (H : Nat → Nat → Int)
    (phi : Fin d → Fin d → Real) (s : Real) :
    (∑ ui : Fin 2 × Fin d, ∑ vj : Fin 2 × Fin d,
      (H (finProdFinEquiv ui) (finProdFinEquiv vj) : Real) *
        s^(ui.1.1+vj.1.1) * phi ui.2 vj.2) =
      ∑ i : Fin d, ∑ j : Fin d,
        ((H i j : Real) + ((H i (d+j) : Real)+(H (d+i) j : Real))*s +
          (H (d+i) (d+j) : Real)*s^2) * phi i j := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [finProdFinEquiv, Fin.val_zero, Fin.val_one,
    Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add, Nat.add_comm,
    pow_zero, pow_one, mul_one]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  norm_num
  ring

theorem one_layer_sum {d : Nat} (H : Nat → Nat → Int)
    (phi : Fin d → Fin d → Real) (s : Real) :
    (∑ ui : Fin 1 × Fin d, ∑ vj : Fin 1 × Fin d,
      (H (finProdFinEquiv ui) (finProdFinEquiv vj) : Real) *
        s^(ui.1.1+vj.1.1) * phi ui.2 vj.2) =
      ∑ i : Fin d, ∑ j : Fin d, (H i j : Real) * phi i j := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_one, finProdFinEquiv]

end Taeyoung.Methods.RootedSOS
