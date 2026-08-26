import Taeyoung.Methods.RootedSOS.Gram
import Taeyoung.Foundation.ProductIntegral

/-!
# Finite quadratic-form expansion lemmas

These algebraic identities turn a factored rational Gram form into its full
matrix of coefficients and commute finite Bernoulli averages with that
expansion.  They are independent of the number of roots and of any Atlas row.
-/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

lemma sum_comm_three {R A B C : Type*} [AddCommMonoid R]
    [Fintype A] [Fintype B] [Fintype C] (f : A → B → C → R) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ b, ∑ a, f a b c := by
  calc
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ a, ∑ c, f a b c := by
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ a, f a b c := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ b, ∑ a, f a b c := by
      rw [Finset.sum_comm]

lemma sum_comm_four {R A B C D : Type*} [AddCommMonoid R]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → B → C → D → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
        ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := by rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]

lemma identity_quadratic_expand {R I J : Type*} [CommRing R]
    [Fintype I] [Fintype J] (F : I → J → R) (v : I → R) :
    (∑ j, (∑ a, F a j * v a) ^ 2) =
      ∑ a, ∑ b, (∑ j, F a j * F b j) * v a * v b := by
  calc
    (∑ j, (∑ a, F a j * v a) ^ 2) =
        ∑ j, ∑ b, ∑ a, (F a j * v a) * (F b j * v b) := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    _ = ∑ a, ∑ b, ∑ j, (F a j * v a) * (F b j * v b) :=
      sum_comm_three (fun j b a => (F a j * v a) * (F b j * v b))
    _ = ∑ a, ∑ b, (∑ j, F a j * F b j) * v a * v b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

lemma correction_quadratic_expand {R I J : Type*} [CommRing R]
    [Fintype I] [Fintype J] (F : I → J → R)
    (C : J → J → R) (v : I → R) :
    (∑ i, ∑ j, (∑ a, F a i * v a) * C i j *
      ∑ b, F b j * v b) =
      ∑ a, ∑ b, (∑ j, (∑ i, F a i * C i j) * F b j) * v a * v b := by
  calc
    (∑ i, ∑ j, (∑ a, F a i * v a) * C i j *
      ∑ b, F b j * v b) =
        ∑ i, ∑ j, ∑ b, ∑ a,
          (F a i * v a) * C i j * (F b j * v b) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ b, ∑ a, ∑ i, ∑ j,
        (F a i * v a) * C i j * (F b j * v b) :=
      sum_comm_four
        (fun i j b a => (F a i * v a) * C i j * (F b j * v b))
    _ = ∑ a, ∑ b, ∑ i, ∑ j,
        (F a i * v a) * C i j * (F b j * v b) := by
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, (∑ j, (∑ i, F a i * C i j) * F b j) * v a * v b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Entry of the full Gram matrix represented by `F (I + C) Fᵀ`. -/
def expandedGramEntry {R I J : Type*} [CommRing R] [Fintype J]
    (F : I → J → R) (C : J → J → R) (a b : I) : R :=
  ∑ j, (F a j + ∑ i, F a i * C i j) * F b j

lemma quadratic_eq_expanded_entries {R I J : Type*} [CommRing R]
    [Fintype I] [Fintype J] (F : I → J → R)
    (C : J → J → R) (v : I → R) :
    (∑ i, (∑ a, F a i * v a) ^ 2) +
      ∑ i, ∑ j, (∑ a, F a i * v a) * C i j *
        ∑ a, F a j * v a =
      ∑ a, ∑ b, expandedGramEntry F C a b * v a * v b := by
  unfold expandedGramEntry
  simp_rw [add_mul, Finset.sum_add_distrib]
  simp only [add_mul, Finset.sum_add_distrib]
  exact congrArg₂ (fun x y => x + y)
    (identity_quadratic_expand F v) (correction_quadratic_expand F C v)

/-- A factored rational Gram form expanded into its full real coefficient
matrix. -/
lemma factoredRatGramForm_eq_expanded_entries
    {I J : Type*} [Fintype I] [Fintype J]
    (F : I → J → ℝ) (C : J → J → Rat) (v : I → ℝ) :
    factoredRatGramForm F C v =
      ∑ a, ∑ b,
        expandedGramEntry F (fun i j => (C i j : ℝ)) a b * v a * v b := by
  change
    (∑ i, (∑ a, F a i * v a) ^ 2) +
      ∑ i, ∑ j, (∑ a, F a i * v a) * (C i j : ℝ) *
        ∑ a, F a j * v a = _
  exact quadratic_eq_expanded_entries F (fun i j => (C i j : ℝ)) v

lemma weighted_average_quadratic {R S I : Type*} [CommRing R] [Fintype I]
    (samples : Finset S) (weight : S → R) (matrix : I → I → R)
    (vector : S → I → R) :
    (∑ s ∈ samples, weight s *
      ∑ a, ∑ b, matrix a b * vector s a * vector s b) =
      ∑ a, ∑ b, matrix a b *
        ∑ s ∈ samples, weight s * vector s a * vector s b := by
  calc
    (∑ s ∈ samples, weight s *
      ∑ a, ∑ b, matrix a b * vector s a * vector s b) =
        ∑ s ∈ samples, ∑ a, ∑ b,
          weight s * matrix a b * vector s a * vector s b := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ a, ∑ s ∈ samples, ∑ b,
        weight s * matrix a b * vector s a * vector s b := by
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, ∑ s ∈ samples,
        weight s * matrix a b * vector s a * vector s b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, matrix a b *
        ∑ s ∈ samples, weight s * vector s a * vector s b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring

lemma integrable_fintype_sum
    {Ω R I : Type*} [MeasurableSpace Ω] [NormedAddCommGroup R]
    [Fintype I] {μ : MeasureTheory.Measure Ω} (f : I → Ω → R)
    (hf : ∀ i, MeasureTheory.Integrable (f i) μ) :
    MeasureTheory.Integrable (fun x => ∑ i, f i x) μ :=
  MeasureTheory.integrable_finsetSum Finset.univ (fun i _ => hf i)

lemma integral_fintype_sum
    {Ω R I : Type*} [MeasurableSpace Ω] [NormedAddCommGroup R]
    [NormedSpace ℝ R] [Fintype I] {μ : MeasureTheory.Measure Ω}
    (f : I → Ω → R) (hf : ∀ i, MeasureTheory.Integrable (f i) μ) :
    (∫ x, ∑ i, f i x ∂μ) = ∑ i, ∫ x, f i x ∂μ := by
  exact MeasureTheory.integral_finset_sum Finset.univ (fun i _ => hf i)

lemma integral_const_mul_fintype_sum
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {μ : MeasureTheory.Measure Ω} (c : I → ℝ) (f : I → Ω → ℝ)
    (hf : ∀ i, MeasureTheory.Integrable (f i) μ) :
    (∫ x, ∑ i, c i * f i x ∂μ) = ∑ i, c i * ∫ x, f i x ∂μ := by
  rw [integral_fintype_sum (fun i x => c i * f i x)
    (fun i => (hf i).const_mul (c i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [MeasureTheory.integral_const_mul]

end Taeyoung.Methods.RootedSOS
