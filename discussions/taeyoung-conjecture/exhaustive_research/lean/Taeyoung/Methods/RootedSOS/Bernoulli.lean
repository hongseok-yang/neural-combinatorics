import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic

/-!
# Finite Bernoulli averaging for rooted SOS certificates

Rooted quantum-graph products identify equally labelled edges.  Evaluating
the corresponding monomials directly at a fractional graphon value would
instead square an edge that occurs in both factors.  The sound interpretation
is to sample one shared Bernoulli bit for every labelled edge, evaluate all
rooted flags at those bits, and then average.  Boolean monomials are
idempotent, while their averages recover the graphon edge values.

This file gives that finite calculation without constructing a conditional
probability kernel.  It is valid for every finite family of edge
probabilities and is the semantic bridge needed by the Atlas 43 and S4 exact
rooted-SOS certificates.
-/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The mass of a set `A` under independent Bernoulli variables with success
probabilities `w`. -/
noncomputable def bernoulliWeight (w : ι → ℝ) (A : Finset ι) : ℝ :=
  (∏ i ∈ A, w i) * ∏ i ∈ (univ \ A), (1 - w i)

theorem bernoulliWeight_nonneg {w : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) (A : Finset ι) :
    0 ≤ bernoulliWeight w A := by
  apply mul_nonneg <;> apply Finset.prod_nonneg
  · exact fun i _ ↦ hw0 i
  · exact fun i _ ↦ sub_nonneg.mpr (hw1 i)

/-- Bernoulli masses form a finite partition of unity. -/
theorem sum_bernoulliWeight (w : ι → ℝ) :
    ∑ A ∈ (univ : Finset ι).powerset, bernoulliWeight w A = 1 := by
  calc
    (∑ A ∈ (univ : Finset ι).powerset, bernoulliWeight w A) =
        ∏ i ∈ (univ : Finset ι), (w i + (1 - w i)) := by
      simpa only [bernoulliWeight] using
        (Finset.prod_add w (fun i ↦ 1 - w i) (univ : Finset ι)).symm
    _ = 1 := by simp

/-- Averaging a nonnegative expression over the shared Bernoulli edge bits
preserves nonnegativity. -/
theorem bernoulli_average_nonneg {w : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (q : Finset ι → ℝ) (hq : ∀ A, 0 ≤ q A) :
    0 ≤ ∑ A ∈ (univ : Finset ι).powerset, bernoulliWeight w A * q A := by
  exact Finset.sum_nonneg fun A _ ↦
    mul_nonneg (bernoulliWeight_nonneg hw0 hw1 A) (hq A)

/-- The average of a Boolean monomial is the product of its success
probabilities.  This is precisely the idempotent rule used when two rooted
flags share the same labelled edge. -/
theorem bernoulli_monomial (w : ι → ℝ) (T : Finset ι) :
    (∑ A ∈ (univ : Finset ι).powerset,
      bernoulliWeight w A * if T ⊆ A then 1 else 0) =
      ∏ i ∈ T, w i := by
  classical
  let v : ι → ℝ := fun i ↦ if i ∈ T then 0 else 1 - w i
  calc
    (∑ A ∈ (univ : Finset ι).powerset,
        bernoulliWeight w A * if T ⊆ A then 1 else 0) =
        ∑ A ∈ (univ : Finset ι).powerset,
          (∏ i ∈ A, w i) * ∏ i ∈ (univ \ A), v i := by
      refine Finset.sum_congr rfl fun A hA ↦ ?_
      by_cases hTA : T ⊆ A
      · simp only [hTA, if_true, mul_one, bernoulliWeight]
        congr 1
        refine Finset.prod_congr rfl fun i hi ↦ ?_
        have hiA : i ∉ A := (Finset.mem_sdiff.mp hi).2
        have hiT : i ∉ T := fun hit ↦ hiA (hTA hit)
        simp [v, hiT]
      · simp only [hTA, if_false, mul_zero]
        obtain ⟨i, hiT, hiA⟩ := Finset.not_subset.mp hTA
        have hiDiff : i ∈ (univ \ A : Finset ι) :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiA⟩
        have hz : ∏ j ∈ (univ \ A), v j = 0 := by
          apply Finset.prod_eq_zero hiDiff
          simp [v, hiT]
        rw [hz, mul_zero]
    _ = ∏ i ∈ (univ : Finset ι), (w i + v i) := by
      rw [Finset.prod_add]
    _ = ∏ i ∈ T, (w i + v i) := by
      symm
      apply Finset.prod_subset (Finset.subset_univ T)
      intro i _ hiT
      simp [v, hiT]
    _ = ∏ i ∈ T, w i := by
      apply Finset.prod_congr rfl
      intro i hiT
      simp [v, hiT]

/-- Two rooted flags multiply by taking the union of their labelled-edge
sets.  This is the exact rule that would be unsound if the labelled edges were
evaluated directly at fractional values and consequently squared. -/
theorem bernoulli_indicator_product
    (w : ι → ℝ) (S T : Finset ι) (a b : ℝ) :
    (∑ A ∈ (univ : Finset ι).powerset, bernoulliWeight w A *
      (if S ⊆ A then a else 0) * (if T ⊆ A then b else 0)) =
      (∏ i ∈ S ∪ T, w i) * a * b := by
  calc
    (∑ A ∈ (univ : Finset ι).powerset, bernoulliWeight w A *
        (if S ⊆ A then a else 0) * (if T ⊆ A then b else 0)) =
        (∑ A ∈ (univ : Finset ι).powerset,
          bernoulliWeight w A * if S ∪ T ⊆ A then 1 else 0) * a * b := by
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A _
      by_cases hS : S ⊆ A <;> by_cases hT : T ⊆ A <;>
        simp_all [Finset.union_subset_iff]
    _ = (∏ i ∈ S ∪ T, w i) * a * b := by
      rw [bernoulli_monomial]

end Taeyoung.Methods.RootedSOS
