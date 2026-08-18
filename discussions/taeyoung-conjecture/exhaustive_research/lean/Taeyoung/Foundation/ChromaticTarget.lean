import Taeyoung.Foundation.ChromaticPolynomial

/-!
# The chromatic lower-bound target

Away from edge density one this is the literal expression in the conjecture.
At density one it is defined to be its polynomial-continuation value `1`.
-/

namespace Taeyoung

variable {V : Type*} [Fintype V]

/-- Endpoint-safe form of `(1-p)^v P(1/(1-p))`. -/
noncomputable def chromaticTarget
    (P : Polynomial ℝ) (p : ℝ) : ℝ :=
  if p = 1 then 1
  else (1 - p) ^ Fintype.card V * Polynomial.eval (1 / (1 - p)) P

@[simp] theorem chromaticTarget_at_one (P : Polynomial ℝ) :
    chromaticTarget (V := V) P 1 = 1 := by
  simp [chromaticTarget]

theorem chromaticTarget_of_ne_one
    (P : Polynomial ℝ) {p : ℝ} (hp : p ≠ 1) :
    chromaticTarget (V := V) P p =
      (1 - p) ^ Fintype.card V * Polynomial.eval (1 / (1 - p)) P := by
  simp [chromaticTarget, hp]

end Taeyoung
