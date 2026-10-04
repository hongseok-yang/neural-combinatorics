import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field

/-!
# Finite relative entropy

Plan T-D4 and §2.3.  On a weighted host the paper's Shannon entropies become relative entropies
against reference weights:

```
  relEnt ρ p = ∑ₐ p(a) log (ρ(a) / p(a))          (= −KL(p ‖ ρ); the paper's H(p) is ρ ≡ 1).
```

Lean's conventions `Real.log 0 = 0` and `x / 0 = 0` make `relEnt` total; every statement carries the
support hypothesis `p a ≠ 0 → ρ a ≠ 0` where it matters.

* `relEnt_le_log_sum` (**Gibbs**, the weighted `eq:support`): `relEnt ρ p ≤ log ∑ ρ` for a law `p`
  supported where `ρ > 0`.  Proved from `log u ≤ u − 1`; no Jensen inequality is needed.
* `relEnt_nonpos_of_law` (**`KL ≥ 0`**).
* `relEnt_prod` (**chain rule**, product form, the weighted `eq:chain`).
* `relEnt_congr` (evaluate the logarithm on the support), `relEnt_equiv` (reindexing),
  `relEnt_one` (the case `ρ ≡ 1` is the Shannon entropy).
-/

open Finset

namespace ApicesCommonness

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Relative entropy** `∑ₐ p(a) log (ρ(a) / p(a))` of `p` against the reference `ρ`. -/
noncomputable def relEnt (ρ p : α → ℝ) : ℝ := ∑ a, p a * Real.log (ρ a / p a)

/-- Only the support of `p` matters: replace the logarithm there by any `f`. -/
lemma relEnt_congr {ρ p : α → ℝ} (f : α → ℝ) (h : ∀ a, p a ≠ 0 → Real.log (ρ a / p a) = f a) :
    relEnt ρ p = ∑ a, p a * f a := by
  refine sum_congr rfl fun a _ => ?_
  by_cases ha : p a = 0
  · rw [ha, zero_mul, zero_mul]
  · rw [h a ha]

/-- With the reference `ρ ≡ 1`, `relEnt` is the Shannon entropy `−∑ p log p`. -/
lemma relEnt_one (p : α → ℝ) : relEnt (fun _ => 1) p = -∑ a, p a * Real.log (p a) := by
  rw [relEnt_congr (fun a => -Real.log (p a)) fun a _ => by rw [one_div, Real.log_inv]]
  simp only [mul_neg, sum_neg_distrib]

/-- Reindexing along an equivalence. -/
lemma relEnt_equiv (e : α ≃ β) (ρ p : β → ℝ) : relEnt (ρ ∘ e) (p ∘ e) = relEnt ρ p :=
  e.sum_comp fun b => p b * Real.log (ρ b / p b)

/-- If `p` is a law supported where `ρ > 0`, then `∑ ρ > 0`. -/
lemma sum_pos_of_support {ρ p : α → ℝ} (hp1 : ∑ a, p a = 1) (hρ0 : ∀ a, 0 ≤ ρ a)
    (hsupp : ∀ a, p a ≠ 0 → ρ a ≠ 0) : 0 < ∑ a, ρ a := by
  obtain ⟨a, -, ha⟩ : ∃ a ∈ (univ : Finset α), p a ≠ 0 := by
    by_contra h
    simp only [mem_univ, true_and, not_exists, not_not] at h
    rw [sum_eq_zero fun a _ => h a] at hp1
    exact zero_ne_one hp1
  exact lt_of_lt_of_le ((hρ0 a).lt_of_ne (hsupp a ha).symm)
    (single_le_sum (fun b _ => hρ0 b) (mem_univ a))

/-- **Gibbs' inequality** (the weighted support bound `eq:support`): for a law `p` supported where
`ρ > 0`, `relEnt ρ p ≤ log ∑ ρ`. -/
theorem relEnt_le_log_sum {ρ p : α → ℝ} (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (hρ0 : ∀ a, 0 ≤ ρ a) (hsupp : ∀ a, p a ≠ 0 → ρ a ≠ 0) :
    relEnt ρ p ≤ Real.log (∑ a, ρ a) := by
  set Z := ∑ a, ρ a with hZ
  have hZpos : 0 < Z := sum_pos_of_support hp1 hρ0 hsupp
  -- termwise: `p log (ρ/p) − p log Z ≤ ρ/Z − p`
  have hterm : ∀ a, p a * Real.log (ρ a / p a) - p a * Real.log Z ≤ ρ a / Z - p a := by
    intro a
    rcases (hp0 a).lt_or_eq with hpa | hpa
    · have hρa : 0 < ρ a := (hρ0 a).lt_of_ne (hsupp a hpa.ne').symm
      have hx : 0 < ρ a / (p a * Z) := div_pos hρa (mul_pos hpa hZpos)
      have hlog : Real.log (ρ a / p a) - Real.log Z = Real.log (ρ a / (p a * Z)) := by
        rw [← Real.log_div (div_pos hρa hpa).ne' hZpos.ne', div_div]
      have h1 := Real.log_le_sub_one_of_pos hx
      calc p a * Real.log (ρ a / p a) - p a * Real.log Z
          = p a * Real.log (ρ a / (p a * Z)) := by rw [← mul_sub, hlog]
        _ ≤ p a * (ρ a / (p a * Z) - 1) := mul_le_mul_of_nonneg_left h1 hpa.le
        _ = ρ a / Z - p a := by field_simp
    · rw [← hpa]
      simp only [zero_mul, sub_zero]
      exact div_nonneg (hρ0 a) hZpos.le
  have hsum := sum_le_sum fun a (_ : a ∈ (univ : Finset α)) => hterm a
  rw [sum_sub_distrib, sum_sub_distrib, ← sum_mul, hp1, one_mul, ← sum_div, ← hZ,
    div_self hZpos.ne', sub_self] at hsum
  unfold relEnt
  linarith

/-- **`KL ≥ 0`**: against a reference law, the relative entropy of a law is nonpositive. -/
theorem relEnt_nonpos_of_law {ρ p : α → ℝ} (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (hρ0 : ∀ a, 0 ≤ ρ a) (hρ1 : ∑ a, ρ a = 1) (hsupp : ∀ a, p a ≠ 0 → ρ a ≠ 0) :
    relEnt ρ p ≤ 0 := by
  have h := relEnt_le_log_sum hp0 hp1 hρ0 hsupp
  rwa [hρ1, Real.log_one] at h

/-- **Chain rule, product form** (the weighted `eq:chain`).  For `p(a, b) = p₁(a) κ(a, b)` and
`ρ(a, b) = ρ₁(a) ρ₂(a, b)`, where each row `κ a` with `p₁ a ≠ 0` sums to one:
`relEnt ρ p = relEnt ρ₁ p₁ + ∑ₐ p₁(a) relEnt (ρ₂ a) (κ a)`. -/
theorem relEnt_prod (ρ₁ p₁ : α → ℝ) (ρ₂ κ : α → β → ℝ) (hκ : ∀ a, p₁ a ≠ 0 → ∑ b, κ a b = 1)
    (hs₁ : ∀ a, p₁ a ≠ 0 → ρ₁ a ≠ 0) (hs₂ : ∀ a b, p₁ a ≠ 0 → κ a b ≠ 0 → ρ₂ a b ≠ 0) :
    relEnt (fun x : α × β => ρ₁ x.1 * ρ₂ x.1 x.2) (fun x => p₁ x.1 * κ x.1 x.2)
      = relEnt ρ₁ p₁ + ∑ a, p₁ a * relEnt (ρ₂ a) (κ a) := by
  unfold relEnt
  rw [Fintype.sum_prod_type, ← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  by_cases ha : p₁ a = 0
  · simp [ha]
  have hrow : ∀ b, p₁ a * κ a b * Real.log (ρ₁ a * ρ₂ a b / (p₁ a * κ a b))
      = p₁ a * Real.log (ρ₁ a / p₁ a) * κ a b + p₁ a * (κ a b * Real.log (ρ₂ a b / κ a b)) := by
    intro b
    by_cases hb : κ a b = 0
    · simp [hb]
    have h₁ : ρ₁ a / p₁ a ≠ 0 := div_ne_zero (hs₁ a ha) ha
    have h₂ : ρ₂ a b / κ a b ≠ 0 := div_ne_zero (hs₂ a b ha hb) hb
    rw [show ρ₁ a * ρ₂ a b / (p₁ a * κ a b) = ρ₁ a / p₁ a * (ρ₂ a b / κ a b) by
      rw [mul_div_mul_comm], Real.log_mul h₁ h₂]
    ring
  simp only [hrow, sum_add_distrib, ← mul_sum, hκ a ha, mul_one]

end ApicesCommonness
