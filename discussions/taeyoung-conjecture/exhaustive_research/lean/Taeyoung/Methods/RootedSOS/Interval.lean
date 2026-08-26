import Taeyoung.Methods.RootedSOS.Bernoulli
import Taeyoung.Methods.RootedSOS.Gram
import Mathlib.Tactic.Linarith

/-!
# Sound interval-SOS wrapper

This combines the two reusable pieces of an exact rooted interval
certificate:

* rational diagonal-dominant Gram matrices give nonnegative quadratic forms;
* shared labelled edges are evaluated at Bernoulli bits and averaged, so
  simple-edge gluing is sound for fractional graphons.

Only the certificate-specific coefficient identity remains after applying
`bernoulli_interval_sos_nonneg`.
-/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

variable {ε κ₀ κ₁ ρ₀ ρ₁ : Type*}
variable [Fintype ε] [DecidableEq ε]
variable [Fintype κ₀] [Fintype κ₁]
variable [Fintype ρ₀] [DecidableEq ρ₀]
variable [Fintype ρ₁] [DecidableEq ρ₁]

/-- The exact nonnegativity conclusion for the two-block interval format

`Gram₀(v₀) + u(1-u) Gram₁(v₁)`, where `u = 2p-1`.

The vectors may depend arbitrarily on the shared Bernoulli edge set.  In the
Atlas 43 certificate `κ₀` indexes `(f, u f)` and `κ₁` indexes `f` itself. -/
theorem bernoulli_interval_sos_nonneg
    (p : ℝ) (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (w : ε → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (F₀ : κ₀ → ρ₀ → ℝ) (C₀ : ρ₀ → ρ₀ → ℚ)
    (hC₀ : ∀ i j, C₀ i j = C₀ j i)
    (hrow₀ : ∀ i, ∑ j, abs (C₀ i j) ≤ 1)
    (F₁ : κ₁ → ρ₁ → ℝ) (C₁ : ρ₁ → ρ₁ → ℚ)
    (hC₁ : ∀ i j, C₁ i j = C₁ j i)
    (hrow₁ : ∀ i, ∑ j, abs (C₁ i j) ≤ 1)
    (v₀ : Finset ε → κ₀ → ℝ) (v₁ : Finset ε → κ₁ → ℝ) :
    0 ≤ ∑ A ∈ (univ : Finset ε).powerset, bernoulliWeight w A *
      (factoredRatGramForm F₀ C₀ (v₀ A) +
        (2 * p - 1) * (1 - (2 * p - 1)) *
          factoredRatGramForm F₁ C₁ (v₁ A)) := by
  have hu : 0 ≤ (2 * p - 1) * (1 - (2 * p - 1)) := by
    apply mul_nonneg <;> linarith
  apply bernoulli_average_nonneg hw0 hw1
  intro A
  exact add_nonneg
    (factoredRatGramForm_nonneg F₀ C₀ hC₀ hrow₀ (v₀ A))
    (mul_nonneg hu (factoredRatGramForm_nonneg F₁ C₁ hC₁ hrow₁ (v₁ A)))

end Taeyoung.Methods.RootedSOS
