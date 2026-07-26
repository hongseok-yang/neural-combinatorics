import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# The clique polynomial used in the pure-chordal bound

For an edge density `p`, the quantity

`cliquePoly s p = ∏ a ∈ Finset.range s, (1 - a * (1 - p))`

is the polynomial denoted `A_s(p)` in the pure-chordal blueprint.
-/

namespace PureChordal

open scoped BigOperators

/-- The explicit clique polynomial `A_s(p)`. -/
def cliquePoly (s : ℕ) (p : ℝ) : ℝ :=
  ∏ a ∈ Finset.range s, (1 - (a : ℝ) * (1 - p))

@[simp] lemma cliquePoly_zero (p : ℝ) : cliquePoly 0 p = 1 := by
  simp [cliquePoly]

@[simp] lemma cliquePoly_one (p : ℝ) : cliquePoly 1 p = 1 := by
  simp [cliquePoly]

lemma cliquePoly_succ (s : ℕ) (p : ℝ) :
    cliquePoly (s + 1) p = cliquePoly s p * (1 - (s : ℝ) * (1 - p)) := by
  simp [cliquePoly, Finset.prod_range_succ]

lemma cliquePoly_nonneg
    {s : ℕ} {p : ℝ}
    (hfactor : ∀ a < s, 0 ≤ 1 - (a : ℝ) * (1 - p)) :
    0 ≤ cliquePoly s p := by
  rw [cliquePoly]
  exact Finset.prod_nonneg fun a ha ↦ hfactor a (Finset.mem_range.mp ha)

lemma cliquePoly_pos
    {s : ℕ} {p : ℝ}
    (hfactor : ∀ a < s, 0 < 1 - (a : ℝ) * (1 - p)) :
    0 < cliquePoly s p := by
  rw [cliquePoly]
  exact Finset.prod_pos fun a ha ↦ hfactor a (Finset.mem_range.mp ha)

lemma cliquePoly_mul_tail (s r : ℕ) (hsr : s ≤ r) (p : ℝ) :
    cliquePoly r p =
      cliquePoly s p *
        ∏ j ∈ Finset.Ico s r, (1 - (j : ℝ) * (1 - p)) := by
  rw [cliquePoly, cliquePoly, ← Finset.prod_sdiff (Finset.range_mono hsr)]
  have hset : Finset.range r \ Finset.range s = Finset.Ico s r := by
    ext j
    simp [and_comm]
  rw [hset, mul_comm]

lemma cliquePoly_le_one
    {s : ℕ} {p : ℝ}
    (hfactor : ∀ a < s, 0 ≤ 1 - (a : ℝ) * (1 - p))
    (hfactor_one : ∀ a < s, 1 - (a : ℝ) * (1 - p) ≤ 1) :
    cliquePoly s p ≤ 1 := by
  rw [cliquePoly]
  exact Finset.prod_le_one (fun a ha ↦ hfactor a (Finset.mem_range.mp ha))
    (fun a ha ↦ hfactor_one a (Finset.mem_range.mp ha))

end PureChordal
