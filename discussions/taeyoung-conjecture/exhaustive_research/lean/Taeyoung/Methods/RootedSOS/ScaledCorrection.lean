import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Taeyoung.Methods.RootedSOS.DiagonalDominance

/-!
# Integer-scaled rational corrections

Exceptional S4 corrections are checked after putting every entry over one
positive block denominator.  This module turns the resulting integer
diagonal-dominance inequality into the rational hypothesis used by the SOS
positivity theorem.
-/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def scaledRatCorrection (denominator : Nat) (scaled : ι → ι → Int)
    (i j : ι) : Rat :=
  (scaled i j : Rat) / (denominator : Rat)

theorem scaledRatCorrection_symm (denominator : Nat)
    (scaled : ι → ι → Int) (hscaled : ∀ i j, scaled i j = scaled j i) :
    ∀ i j, scaledRatCorrection denominator scaled i j =
      scaledRatCorrection denominator scaled j i := by
  intro i j
  simp only [scaledRatCorrection, hscaled]

private theorem abs_scaledRatCorrection
    (denominator : Nat) (scaled : Int) (hdenominator : 0 < denominator) :
    abs ((scaled : Rat) / (denominator : Rat)) =
      (scaled.natAbs : Rat) / (denominator : Rat) := by
  have hD : (0 : Rat) < (denominator : Rat) := by
    exact_mod_cast hdenominator
  rw [abs_div, abs_of_pos hD]
  congr 1
  simp

/-- A scaled integer row inequality implies rational Gershgorin diagonal
dominance after division by the common positive denominator. -/
theorem scaledRatCorrection_diagonallyDominant
    (denominator : Nat) (scaled : ι → ι → Int)
    (hdenominator : 0 < denominator)
    (hrow : ∀ i,
      ((∑ j, if i = j then 0 else (scaled i j).natAbs : Nat) : Int) ≤
        (denominator : Int) + scaled i i) :
    ∀ i,
      (∑ j, abs (if i = j then (0 : Rat)
        else scaledRatCorrection denominator scaled i j)) ≤
          1 + scaledRatCorrection denominator scaled i i := by
  intro i
  let radius : Nat := ∑ j, if i = j then 0 else (scaled i j).natAbs
  have hD : (0 : Rat) < (denominator : Rat) := by
    exact_mod_cast hdenominator
  have hiInt : (radius : Int) ≤ (denominator : Int) + scaled i i := by
    exact hrow i
  have hi : (radius : Rat) ≤
      (denominator : Rat) + (scaled i i : Rat) := by
    exact_mod_cast hiInt
  calc
    (∑ j, abs (if i = j then (0 : Rat)
        else scaledRatCorrection denominator scaled i j)) =
        (radius : Rat) / (denominator : Rat) := by
      dsimp [radius]
      calc
        (∑ j, abs (if i = j then (0 : Rat)
            else scaledRatCorrection denominator scaled i j)) =
            ∑ j, ((if i = j then 0 else (scaled i j).natAbs : Nat) : Rat) /
              (denominator : Rat) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hij : i = j
          · subst j
            simp
          · simp only [if_neg hij, scaledRatCorrection]
            exact abs_scaledRatCorrection denominator (scaled i j) hdenominator
        _ = ((∑ j, if i = j then 0 else (scaled i j).natAbs : Nat) : Rat) /
              (denominator : Rat) := by
          rw [← Finset.sum_div]
          norm_cast
    _ ≤ 1 + (scaled i i : Rat) / (denominator : Rat) := by
      rw [div_le_iff₀ hD]
      simpa only [add_mul, one_mul, div_mul_cancel₀ _ hD.ne'] using hi
    _ = 1 + scaledRatCorrection denominator scaled i i := by
      rfl

theorem scaledRatGram_nonneg
    {A : Type*} [Fintype A]
    (denominator : Nat) (scaled : ι → ι → Int)
    (hdenominator : 0 < denominator)
    (hscaled : ∀ i j, scaled i j = scaled j i)
    (hrow : ∀ i,
      ((∑ j, if i = j then 0 else (scaled i j).natAbs : Nat) : Int) ≤
        (denominator : Int) + scaled i i)
    (F : A → ι → Real) (v : A → Real) :
    0 ≤ factoredRatGramForm F
      (scaledRatCorrection denominator scaled) v := by
  exact factoredRatGramForm_nonneg_diagonallyDominant F
    (scaledRatCorrection denominator scaled)
    (scaledRatCorrection_symm denominator scaled hscaled)
    (scaledRatCorrection_diagonallyDominant denominator scaled hdenominator hrow) v

end Taeyoung.Methods.RootedSOS
