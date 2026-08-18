import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Real.Basic

/-!
# Chromatic-polynomial specifications

Mathlib does not currently expose a general chromatic-polynomial object for
`SimpleGraph`.  We therefore characterize the polynomial by its values on all
natural numbers.  Uniqueness is proved here, so method directories may supply
whichever factored polynomial is most convenient without changing the target.
-/

namespace Taeyoung

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

/-- A map into `Fin k` that separates the endpoints of every edge. -/
def IsProperAssignment {k : ℕ} (x : V → Fin k) : Prop :=
  ∀ ⦃u v⦄, H.Adj u v → x u ≠ x v

noncomputable local instance instDecidableIsProperAssignment
    {k : ℕ} (x : V → Fin k) :
    Decidable (IsProperAssignment H x) :=
  Classical.propDecidable _

/-- The exact number of proper maps from `H` to the `k` labelled colours. -/
noncomputable def properAssignmentCount (k : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (V → Fin k)).filter
    (IsProperAssignment H)).card

/-- The universal natural-colouring characterization of a chromatic polynomial. -/
def IsChromaticPolynomial (P : Polynomial ℝ) : Prop :=
  ∀ k : ℕ, Polynomial.eval (k : ℝ) P = (properAssignmentCount H k : ℕ)

theorem IsChromaticPolynomial.unique
    {P Q : Polynomial ℝ}
    (hP : IsChromaticPolynomial H P)
    (hQ : IsChromaticPolynomial H Q) :
    P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq P Q
  have hinfinite : Set.Infinite (Set.range fun k : ℕ => (k : ℝ)) :=
    Set.infinite_range_of_injective Nat.cast_injective
  apply hinfinite.mono
  rintro x ⟨k, rfl⟩
  change Polynomial.eval (k : ℝ) P = Polynomial.eval (k : ℝ) Q
  rw [hP k, hQ k]

/-- A natural number is the chromatic number when it admits a colouring and
every strictly smaller number of colours admits none. -/
structure IsChromaticNumber (r : ℕ) : Prop where
  positive : 0 < properAssignmentCount H r
  zero_below : ∀ k : ℕ, k < r → properAssignmentCount H k = 0

theorem IsChromaticNumber.unique
    {r s : ℕ}
    (hr : IsChromaticNumber H r)
    (hs : IsChromaticNumber H s) :
    r = s := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hrs | hsr
  · have hz := hs.zero_below r hrs
    exact (Nat.ne_of_gt hr.positive) hz
  · have hz := hr.zero_below s hsr
    exact (Nat.ne_of_gt hs.positive) hz

end Taeyoung
