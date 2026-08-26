import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Gram-matrix positivity for exact rooted SOS certificates

The Atlas 43 and four-root certificates store each reduced Gram matrix as
`I + C`, where `C` is symmetric and every absolute row sum is at most one.
This file proves the finite-dimensional inequality consumed by those
certificates directly, without eigenvalues or floating-point arithmetic.
-/

open Finset

namespace Taeyoung.Methods.RootedSOS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The elementary estimate used for every off-diagonal Gram entry. -/
private theorem correction_term_lower_bound (c x y : ℝ) :
    -(abs c * (x ^ 2 + y ^ 2) / 2) ≤ x * c * y := by
  have hxy : 2 * (abs x * abs y) ≤ x ^ 2 + y ^ 2 := by
    nlinarith [sq_nonneg (abs x - abs y), sq_abs x, sq_abs y]
  have hcxy : abs c * (abs x * abs y) ≤ abs c * ((x ^ 2 + y ^ 2) / 2) := by
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
  have habs : -(abs (x * c * y)) ≤ x * c * y := neg_abs_le _
  rw [abs_mul, abs_mul] at habs
  nlinarith [hcxy]

/-- Swapping the two finite summation axes does not change the absolute
correction contribution when the correction is symmetric. -/
private theorem swapped_abs_sum
    (C : ι → ι → ℝ) (hC : ∀ i j, C i j = C j i) (x : ι → ℝ) :
    (∑ i, ∑ j, abs (C i j) * x j ^ 2) =
      ∑ i, x i ^ 2 * ∑ j, abs (C i j) := by
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  rw [hC j i]
  ring

/-- A symmetric correction whose absolute row sums are at most one can be
added to the identity without destroying nonnegativity.

This is the exact diagonal-dominance criterion used by the rational Gram
matrices in the rooted SOS certificates. -/
theorem identity_add_correction_quadratic_nonneg
    (C : ι → ι → ℝ)
    (hC : ∀ i j, C i j = C j i)
    (hrow : ∀ i, ∑ j, abs (C i j) ≤ 1)
    (x : ι → ℝ) :
    0 ≤ (∑ i, x i ^ 2) + ∑ i, ∑ j, x i * C i j * x j := by
  let S : ℝ := ∑ i, x i ^ 2
  let A : ℝ := ∑ i, x i ^ 2 * ∑ j, abs (C i j)
  let L : ℝ := ∑ i, ∑ j, -(abs (C i j) * (x i ^ 2 + x j ^ 2) / 2)
  have hA : A ≤ S := by
    dsimp [A, S]
    apply sum_le_sum
    intro i _
    simpa using mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg (x i))
  have hL : L = -A := by
    dsimp [L, A]
    rw [show (∑ i, ∑ j, -(abs (C i j) * (x i ^ 2 + x j ^ 2) / 2)) =
        -(1 / 2 : ℝ) *
          ((∑ i, ∑ j, abs (C i j) * x i ^ 2) +
            ∑ i, ∑ j, abs (C i j) * x j ^ 2) by
      calc
        _ = ∑ i, ∑ j,
            (-(1 / 2 : ℝ) * (abs (C i j) * x i ^ 2) +
              -(1 / 2 : ℝ) * (abs (C i j) * x j ^ 2)) := by
              apply sum_congr rfl
              intro i _
              apply sum_congr rfl
              intro j _
              ring
        _ = _ := by
          simp_rw [sum_add_distrib, ← mul_sum]
          ring]
    rw [swapped_abs_sum C hC x]
    have hfirst : (∑ i, ∑ j, abs (C i j) * x i ^ 2) =
        ∑ i, x i ^ 2 * ∑ j, abs (C i j) := by
      apply sum_congr rfl
      intro i _
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    rw [hfirst]
    ring
  have hsum : L ≤ ∑ i, ∑ j, x i * C i j * x j := by
    dsimp [L]
    apply sum_le_sum
    intro i _
    apply sum_le_sum
    intro j _
    exact correction_term_lower_bound (C i j) (x i) (x j)
  rw [hL] at hsum
  dsimp [S] at hA ⊢
  linarith

/-- Rational certificate data can be checked in `ℚ` and cast to the real
quadratic form without introducing a numerical approximation. -/
theorem identity_add_rat_correction_quadratic_nonneg
    (C : ι → ι → ℚ)
    (hC : ∀ i j, C i j = C j i)
    (hrow : ∀ i, ∑ j, abs (C i j) ≤ 1)
    (x : ι → ℝ) :
    0 ≤ (∑ i, x i ^ 2) +
      ∑ i, ∑ j, x i * (C i j : ℝ) * x j := by
  apply identity_add_correction_quadratic_nonneg
  · intro i j
    exact_mod_cast hC i j
  · intro i
    have hi : ((∑ j, abs (C i j) : ℚ) : ℝ) ≤ 1 := by
      exact_mod_cast hrow i
    simpa using hi

/-- The factored form used by the certificates.  The rows of `F` first turn
the rooted-density vector into reduced coordinates; positivity then depends
only on the much smaller rational correction matrix `C`. -/
theorem factored_rat_gram_quadratic_nonneg
    {κ : Type*} [Fintype κ]
    (F : κ → ι → ℝ)
    (C : ι → ι → ℚ)
    (hC : ∀ i j, C i j = C j i)
    (hrow : ∀ i, ∑ j, abs (C i j) ≤ 1)
    (v : κ → ℝ) :
    0 ≤
      (∑ i, (∑ a, F a i * v a) ^ 2) +
        ∑ i, ∑ j,
          (∑ a, F a i * v a) * (C i j : ℝ) *
            ∑ a, F a j * v a := by
  exact identity_add_rat_correction_quadratic_nonneg C hC hrow
    (fun i ↦ ∑ a, F a i * v a)

/-- The quadratic form represented by an exact rational correction `I + C`
after applying the (usually integer-scaled) factor `F`. -/
noncomputable def factoredRatGramForm
    {κ : Type*} [Fintype κ]
    (F : κ → ι → ℝ) (C : ι → ι → ℚ) (v : κ → ℝ) : ℝ :=
  (∑ i, (∑ a, F a i * v a) ^ 2) +
    ∑ i, ∑ j,
      (∑ a, F a i * v a) * (C i j : ℝ) *
        ∑ a, F a j * v a

theorem factoredRatGramForm_nonneg
    {κ : Type*} [Fintype κ]
    (F : κ → ι → ℝ)
    (C : ι → ι → ℚ)
    (hC : ∀ i j, C i j = C j i)
    (hrow : ∀ i, ∑ j, abs (C i j) ≤ 1)
    (v : κ → ℝ) :
    0 ≤ factoredRatGramForm F C v :=
  factored_rat_gram_quadratic_nonneg F C hC hrow v

end Taeyoung.Methods.RootedSOS
