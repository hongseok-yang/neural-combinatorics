import Taeyoung.Methods.RootedSOS.Gram

/-!
# General diagonal-dominance positivity

The S4 certificates use the Gershgorin condition
`1 + C i i ≥ ∑ j ≠ i, |C i j|`.  Unlike the simpler absolute-row-sum
criterion, this also permits positive diagonal corrections.
-/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def offDiagonal (C : ι → ι → ℝ) (i j : ι) : ℝ :=
  if i = j then 0 else C i j

private theorem offDiagonal_symm (C : ι → ι → ℝ)
    (hC : ∀ i j, C i j = C j i) :
    ∀ i j, offDiagonal C i j = offDiagonal C j i := by
  intro i j
  by_cases h : i = j
  · subst j
    simp [offDiagonal]
  · rw [offDiagonal, offDiagonal, if_neg h, if_neg (Ne.symm h), hC]

private theorem dd_correction_term_lower_bound (c x y : ℝ) :
    -(abs c * (x ^ 2 + y ^ 2) / 2) ≤ x * c * y := by
  have hxy : 2 * (abs x * abs y) ≤ x ^ 2 + y ^ 2 := by
    nlinarith [sq_nonneg (abs x - abs y), sq_abs x, sq_abs y]
  have hcxy : abs c * (abs x * abs y) ≤
      abs c * ((x ^ 2 + y ^ 2) / 2) := by
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
  have habs : -(abs (x * c * y)) ≤ x * c * y := neg_abs_le _
  rw [abs_mul, abs_mul] at habs
  nlinarith [hcxy]

private theorem dd_swapped_abs_sum
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

/-- A symmetric correction may be added to the identity whenever every
corrected diagonal dominates its off-diagonal absolute row sum. -/
theorem identity_add_correction_diagonallyDominant_nonneg
    (C : ι → ι → ℝ)
    (hC : ∀ i j, C i j = C j i)
    (hrow : ∀ i,
      (∑ j, abs (offDiagonal C i j)) ≤ 1 + C i i)
    (x : ι → ℝ) :
    0 ≤ (∑ i, x i ^ 2) + ∑ i, ∑ j, x i * C i j * x j := by
  let O : ι → ι → ℝ := offDiagonal C
  let S : ℝ := ∑ i, (1 + C i i) * x i ^ 2
  let A : ℝ := ∑ i, x i ^ 2 * ∑ j, abs (O i j)
  let L : ℝ :=
    ∑ i, ∑ j, -(abs (O i j) * (x i ^ 2 + x j ^ 2) / 2)
  have hO : ∀ i j, O i j = O j i := offDiagonal_symm C hC
  have hA : A ≤ S := by
    dsimp [A, S]
    apply sum_le_sum
    intro i _
    simpa [O, mul_comm] using
      mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg (x i))
  have hL : L = -A := by
    dsimp [L, A]
    rw [show (∑ i, ∑ j,
        -(abs (O i j) * (x i ^ 2 + x j ^ 2) / 2)) =
        -(1 / 2 : ℝ) *
          ((∑ i, ∑ j, abs (O i j) * x i ^ 2) +
            ∑ i, ∑ j, abs (O i j) * x j ^ 2) by
      calc
        _ = ∑ i, ∑ j,
            (-(1 / 2 : ℝ) * (abs (O i j) * x i ^ 2) +
              -(1 / 2 : ℝ) * (abs (O i j) * x j ^ 2)) := by
              apply sum_congr rfl
              intro i _
              apply sum_congr rfl
              intro j _
              ring
        _ = _ := by
          simp_rw [sum_add_distrib, ← mul_sum]
          ring]
    rw [dd_swapped_abs_sum O hO x]
    have hfirst : (∑ i, ∑ j, abs (O i j) * x i ^ 2) =
        ∑ i, x i ^ 2 * ∑ j, abs (O i j) := by
      apply sum_congr rfl
      intro i _
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    rw [hfirst]
    ring
  have hsum : L ≤ ∑ i, ∑ j, x i * O i j * x j := by
    dsimp [L]
    apply sum_le_sum
    intro i _
    apply sum_le_sum
    intro j _
    exact dd_correction_term_lower_bound (O i j) (x i) (x j)
  rw [hL] at hsum
  have hnonneg : 0 ≤ S + ∑ i, ∑ j, x i * O i j * x j := by
    linarith
  have hsplit (i : ι) :
      (∑ j, x i * C i j * x j) =
        x i * C i i * x i + ∑ j, x i * O i j * x j := by
    have hCsum : (∑ j, x i * C i j * x j) =
        (∑ j ∈ (Finset.univ : Finset ι).erase i, x i * C i j * x j) +
          x i * C i i * x i :=
      (Finset.sum_erase_add (Finset.univ : Finset ι)
        (fun j => x i * C i j * x j) (Finset.mem_univ i)).symm
    have hOsum : (∑ j, x i * O i j * x j) =
        ∑ j ∈ (Finset.univ : Finset ι).erase i, x i * O i j * x j := by
      rw [← Finset.sum_erase_add (Finset.univ : Finset ι)
        (fun j => x i * O i j * x j) (Finset.mem_univ i)]
      simp [O, offDiagonal]
    rw [hCsum, hOsum, add_comm]
    apply congrArg (fun value => x i * C i i * x i + value)
    apply Finset.sum_congr rfl
    intro j hj
    have hji : i ≠ j :=
      Ne.symm (Finset.mem_erase.mp hj).1
    simp only [O, offDiagonal, if_neg hji]
  calc
    (∑ i, x i ^ 2) + ∑ i, ∑ j, x i * C i j * x j =
        S + ∑ i, ∑ j, x i * O i j * x j := by
      dsimp [S]
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib, ← add_assoc]
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≥ 0 := hnonneg

/-- Rational diagonal-dominance data casts directly to the real quadratic
form used by factored Gram certificates. -/
theorem identity_add_rat_correction_diagonallyDominant_nonneg
    (C : ι → ι → ℚ)
    (hC : ∀ i j, C i j = C j i)
    (hrow : ∀ i,
      (∑ j, abs (if i = j then (0 : ℚ) else C i j)) ≤ 1 + C i i)
    (x : ι → ℝ) :
    0 ≤ (∑ i, x i ^ 2) +
      ∑ i, ∑ j, x i * (C i j : ℝ) * x j := by
  apply identity_add_correction_diagonallyDominant_nonneg
  · intro i j
    exact_mod_cast hC i j
  · intro i
    have hi :
        (((∑ j, abs (if i = j then (0 : ℚ) else C i j)) : ℚ) : ℝ) ≤
          ((1 + C i i : ℚ) : ℝ) := by
      exact_mod_cast hrow i
    calc
      (∑ j, abs (offDiagonal (fun a b => (C a b : ℝ)) i j)) =
          (((∑ j, abs (if i = j then (0 : ℚ) else C i j)) : ℚ) : ℝ) := by
        push_cast
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i = j <;> simp [offDiagonal, hij]
      _ ≤ ((1 + C i i : ℚ) : ℝ) := hi
      _ = 1 + (C i i : ℝ) := by
        push_cast
        rfl

/-- Factoring a diagonally-dominant rational Gram matrix preserves the same
positivity certificate used by `factoredRatGramForm`. -/
theorem factoredRatGramForm_nonneg_diagonallyDominant
    {A : Type*} [Fintype A]
    (F : A → ι → ℝ) (C : ι → ι → ℚ)
    (hC : ∀ i j, C i j = C j i)
    (hrow : ∀ i,
      (∑ j, abs (if i = j then (0 : ℚ) else C i j)) ≤ 1 + C i i)
    (v : A → ℝ) :
    0 ≤ factoredRatGramForm F C v := by
  exact identity_add_rat_correction_diagonallyDominant_nonneg C hC hrow
    (fun i => ∑ a, F a i * v a)

end Taeyoung.Methods.RootedSOS
