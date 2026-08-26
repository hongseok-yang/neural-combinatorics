import Taeyoung.Methods.RootedSOS.FlagLinearCombination

/-!
# Analytic expansion of a rooted-flag Gram block

This module is the reusable bridge from a factored rational Gram block to a
finite linear combination of ordinary glued-graph densities.  Certificate
instances therefore reduce to exact finite coefficient arithmetic.
-/

open Finset MeasureTheory
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

open Taeyoung

variable {k order : ℕ}
variable {A I J : Type*} [Fintype A] [Fintype I] [Fintype J]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- A single polynomially extended, symmetry-sliced, factored Gram block,
averaged over the shared labelled-edge Bernoulli variables. -/
noncomputable def averagedFlagGramBlock
    (labelGraph : A → SimpleGraph (Fin k))
    [∀ a, DecidableRel (labelGraph a).Adj]
    (neighbors : A → Finset (Fin k))
    (T : A → I → ℝ) (F : (Fin order × I) → J → ℝ)
    (C : J → J → Rat) (W : Graphon Ω μ) (s : ℝ) (x : Fin k → Ω) : ℝ :=
  ∑ bits ∈ (univ : Finset (Sym2 (Fin k))).powerset,
    bernoulliWeight (fun e => edgeValue W x e) bits *
      factoredRatGramForm F C
        (monomialFlagExtension s
          (flagLinearCombination T
            (rawFlagVector labelGraph neighbors W x bits)))

/-- Coefficient of one ordered pair of raw flags after expanding a Gram
block. -/
noncomputable def flagGramPairCoefficient
    (T : A → I → ℝ) (F : (Fin order × I) → J → ℝ)
    (C : J → J → Rat) (s : ℝ) (a b : A) : ℝ :=
  ∑ ui, ∑ vj,
    expandedGramEntry F (fun i j => (C i j : ℝ)) ui vj *
      s ^ (ui.1.1 + vj.1.1) * T a ui.2 * T b vj.2

theorem averagedFlagGramBlock_eq_kernel_sum
    (labelGraph : A → SimpleGraph (Fin k))
    [∀ a, DecidableRel (labelGraph a).Adj]
    (neighbors : A → Finset (Fin k))
    (T : A → I → ℝ) (F : (Fin order × I) → J → ℝ)
    (C : J → J → Rat) (W : Graphon Ω μ) (s : ℝ) (x : Fin k → Ω) :
    averagedFlagGramBlock labelGraph neighbors T F C W s x =
      ∑ a, ∑ b, flagGramPairCoefficient T F C s a b *
        gluedRootedFlagKernel W x (labelGraph a) (labelGraph b)
          (neighbors a) (neighbors b) := by
  unfold averagedFlagGramBlock
  simp_rw [factoredRatGramForm_eq_expanded_entries]
  rw [weighted_average_quadratic]
  simp_rw [bernoulli_monomialFlagExtension_product
    labelGraph neighbors T W x s]
  unfold flagGramPairCoefficient
  calc
    (∑ ui, ∑ vj,
      expandedGramEntry F (fun i j => (C i j : ℝ)) ui vj *
        (s ^ (ui.1.1 + vj.1.1) *
          ∑ a, ∑ b, T a ui.2 * T b vj.2 *
            gluedRootedFlagKernel W x (labelGraph a) (labelGraph b)
              (neighbors a) (neighbors b))) =
        ∑ ui, ∑ vj, ∑ a, ∑ b,
          expandedGramEntry F (fun i j => (C i j : ℝ)) ui vj *
            s ^ (ui.1.1 + vj.1.1) * T a ui.2 * T b vj.2 *
              gluedRootedFlagKernel W x (labelGraph a) (labelGraph b)
                (neighbors a) (neighbors b) := by
      apply Finset.sum_congr rfl
      intro ui _
      apply Finset.sum_congr rfl
      intro vj _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ a, ∑ b, ∑ ui, ∑ vj,
          expandedGramEntry F (fun i j => (C i j : ℝ)) ui vj *
            s ^ (ui.1.1 + vj.1.1) * T a ui.2 * T b vj.2 *
              gluedRootedFlagKernel W x (labelGraph a) (labelGraph b)
                (neighbors a) (neighbors b) :=
      sum_comm_four (fun ui vj a b =>
        expandedGramEntry F (fun i j => (C i j : ℝ)) ui vj *
          s ^ (ui.1.1 + vj.1.1) * T a ui.2 * T b vj.2 *
            gluedRootedFlagKernel W x (labelGraph a) (labelGraph b)
              (neighbors a) (neighbors b))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [Finset.sum_mul]

/-- Integrating a Gram block replaces every glued kernel by the corresponding
ordinary homomorphism density. -/
theorem integral_averagedFlagGramBlock_eq_density_sum
    (labelGraph : A → SimpleGraph (Fin k))
    [∀ a, DecidableRel (labelGraph a).Adj]
    (neighbors : A → Finset (Fin k))
    (T : A → I → ℝ) (F : (Fin order × I) → J → ℝ)
    (C : J → J → Rat) (W : Graphon Ω μ) (s : ℝ) :
    (∫ x, averagedFlagGramBlock labelGraph neighbors T F C W s x
      ∂assignmentMeasure (Fin k) μ) =
      ∑ a, ∑ b, flagGramPairCoefficient T F C s a b *
        homDensity (gluedRootedFlagGraph (labelGraph a) (labelGraph b)
          (neighbors a) (neighbors b)) W := by
  rw [MeasureTheory.integral_congr_ae
    (MeasureTheory.ae_of_all _ fun x =>
      averagedFlagGramBlock_eq_kernel_sum
        labelGraph neighbors T F C W s x)]
  rw [integral_fintype_sum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [integral_fintype_sum]
    · apply Finset.sum_congr rfl
      intro b _
      rw [MeasureTheory.integral_const_mul,
        integral_gluedRootedFlagKernel_eq_homDensity]
    · intro b
      exact (integrable_gluedRootedFlagKernel W
        (labelGraph a) (labelGraph b) (neighbors a) (neighbors b)).const_mul _
  · intro a
    exact integrable_fintype_sum _ fun b =>
      (integrable_gluedRootedFlagKernel W
        (labelGraph a) (labelGraph b) (neighbors a) (neighbors b)).const_mul _

end Taeyoung.Methods.RootedSOS
