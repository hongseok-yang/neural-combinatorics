import Taeyoung.Methods.RootedSOS.Bernoulli
import Taeyoung.Methods.RootedSOS.DiagonalDominance

/-!
# Certificate-independent interval-SOS positivity

The four-root certificates use a unit interval parameter `s` and the standard
Markov--Lukács shape

`Gram₀(v₀) + s(1-s) Gram₁(v₁)`.

This file isolates its exact positivity argument from every particular Atlas
row.  Certificate instances only have to supply symmetry and rational
diagonal-dominance checks for their correction matrices.
-/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

variable {E I₀ I₁ J₀ J₁ : Type*}
variable [Fintype E] [DecidableEq E]
variable [Fintype I₀] [Fintype I₁]
variable [Fintype J₀] [DecidableEq J₀]
variable [Fintype J₁] [DecidableEq J₁]

/-- Pointwise nonnegativity of the two-block unit-interval SOS. -/
theorem unitIntervalRatSOS_nonneg
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (F₀ : I₀ → J₀ → ℝ) (C₀ : J₀ → J₀ → ℚ)
    (hC₀ : ∀ i j, C₀ i j = C₀ j i)
    (hrow₀ : ∀ i, ∑ j, |C₀ i j| ≤ 1)
    (F₁ : I₁ → J₁ → ℝ) (C₁ : J₁ → J₁ → ℚ)
    (hC₁ : ∀ i j, C₁ i j = C₁ j i)
    (hrow₁ : ∀ i, ∑ j, |C₁ i j| ≤ 1)
    (v₀ : I₀ → ℝ) (v₁ : I₁ → ℝ) :
    0 ≤ factoredRatGramForm F₀ C₀ v₀ +
      s * (1 - s) * factoredRatGramForm F₁ C₁ v₁ := by
  exact add_nonneg
    (factoredRatGramForm_nonneg F₀ C₀ hC₀ hrow₀ v₀)
    (mul_nonneg (mul_nonneg hs0 (sub_nonneg.mpr hs1))
      (factoredRatGramForm_nonneg F₁ C₁ hC₁ hrow₁ v₁))

/-- Pointwise positivity under the full Gershgorin condition used by the S4
certificates.  Positive diagonal corrections are allowed. -/
theorem unitIntervalRatSOS_nonneg_diagonallyDominant
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (F₀ : I₀ → J₀ → ℝ) (C₀ : J₀ → J₀ → ℚ)
    (hC₀ : ∀ i j, C₀ i j = C₀ j i)
    (hrow₀ : ∀ i,
      (∑ j, abs (if i = j then (0 : ℚ) else C₀ i j)) ≤ 1 + C₀ i i)
    (F₁ : I₁ → J₁ → ℝ) (C₁ : J₁ → J₁ → ℚ)
    (hC₁ : ∀ i j, C₁ i j = C₁ j i)
    (hrow₁ : ∀ i,
      (∑ j, abs (if i = j then (0 : ℚ) else C₁ i j)) ≤ 1 + C₁ i i)
    (v₀ : I₀ → ℝ) (v₁ : I₁ → ℝ) :
    0 ≤ factoredRatGramForm F₀ C₀ v₀ +
      s * (1 - s) * factoredRatGramForm F₁ C₁ v₁ := by
  exact add_nonneg
    (factoredRatGramForm_nonneg_diagonallyDominant F₀ C₀ hC₀ hrow₀ v₀)
    (mul_nonneg (mul_nonneg hs0 (sub_nonneg.mpr hs1))
      (factoredRatGramForm_nonneg_diagonallyDominant F₁ C₁ hC₁ hrow₁ v₁))

/-- Averaging a unit-interval SOS over shared Bernoulli labelled-edge bits
preserves its nonnegativity. -/
theorem bernoulli_unitIntervalRatSOS_nonneg
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (w : E → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (F₀ : I₀ → J₀ → ℝ) (C₀ : J₀ → J₀ → ℚ)
    (hC₀ : ∀ i j, C₀ i j = C₀ j i)
    (hrow₀ : ∀ i, ∑ j, |C₀ i j| ≤ 1)
    (F₁ : I₁ → J₁ → ℝ) (C₁ : J₁ → J₁ → ℚ)
    (hC₁ : ∀ i j, C₁ i j = C₁ j i)
    (hrow₁ : ∀ i, ∑ j, |C₁ i j| ≤ 1)
    (v₀ : Finset E → I₀ → ℝ) (v₁ : Finset E → I₁ → ℝ) :
    0 ≤ ∑ A ∈ (univ : Finset E).powerset, bernoulliWeight w A *
      (factoredRatGramForm F₀ C₀ (v₀ A) +
        s * (1 - s) * factoredRatGramForm F₁ C₁ (v₁ A)) := by
  apply bernoulli_average_nonneg hw0 hw1
  intro A
  exact unitIntervalRatSOS_nonneg s hs0 hs1 F₀ C₀ hC₀ hrow₀
    F₁ C₁ hC₁ hrow₁ (v₀ A) (v₁ A)

/-- Bernoulli averaging preserves the general S4 diagonal-dominance
certificate. -/
theorem bernoulli_unitIntervalRatSOS_nonneg_diagonallyDominant
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (w : E → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (F₀ : I₀ → J₀ → ℝ) (C₀ : J₀ → J₀ → ℚ)
    (hC₀ : ∀ i j, C₀ i j = C₀ j i)
    (hrow₀ : ∀ i,
      (∑ j, abs (if i = j then (0 : ℚ) else C₀ i j)) ≤ 1 + C₀ i i)
    (F₁ : I₁ → J₁ → ℝ) (C₁ : J₁ → J₁ → ℚ)
    (hC₁ : ∀ i j, C₁ i j = C₁ j i)
    (hrow₁ : ∀ i,
      (∑ j, abs (if i = j then (0 : ℚ) else C₁ i j)) ≤ 1 + C₁ i i)
    (v₀ : Finset E → I₀ → ℝ) (v₁ : Finset E → I₁ → ℝ) :
    0 ≤ ∑ A ∈ (univ : Finset E).powerset, bernoulliWeight w A *
      (factoredRatGramForm F₀ C₀ (v₀ A) +
        s * (1 - s) * factoredRatGramForm F₁ C₁ (v₁ A)) := by
  apply bernoulli_average_nonneg hw0 hw1
  intro A
  exact unitIntervalRatSOS_nonneg_diagonallyDominant s hs0 hs1
    F₀ C₀ hC₀ hrow₀ F₁ C₁ hC₁ hrow₁ (v₀ A) (v₁ A)

end Taeyoung.Methods.RootedSOS
