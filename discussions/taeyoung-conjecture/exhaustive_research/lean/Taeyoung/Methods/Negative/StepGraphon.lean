import Taeyoung.Foundation
import Taeyoung.Methods.Negative.Tensor

/-!
# Rational step graphons on a uniform finite space

`Methods/Negative/Tensor.lean` handles the 19 tensor–Turán rows, whose witness
takes only the values `0` and `1`.  The Turán-local rows of
`notes/turan_local_and_high_density_negative_tests.tex` need genuinely
*fractional* cell values — a perturbation of a Turán graphon by `ε` on some
cells — so this file supplies the general construction.

A witness here is a symmetric matrix `N : Fin k → Fin k → ℕ` together with a
scale `s`, giving the graphon with cell values `N i j / s` on `Fin k` with the
uniform measure.  The point of carrying the numerator as a natural number is
that the homomorphism density then has a **natural-number** numerator,

```
t(H, W) = (∑_z ∏_{e ∈ E(H)} N(z u, z v)) / (k^{v(H)} · s^{e(H)}),
```

so the whole density is one `decide +kernel` evaluation of a sum over
`V → Fin k` — no real arithmetic inside the kernel, and no `Finset.filter` over
a function space.  For a six-vertex row with `k = 4` that is `4⁶ = 4096`
assignments, far cheaper than the colouring counts the tensor rows need.

The three rows this closes — Atlas 166, 172 and 206 — all use the *uniform*
measure, with four or three equal parts.  Atlas 152 does not: its five parts
have unequal masses, so it needs a weighted measure and is not covered here.
-/

open Finset MeasureTheory

namespace Taeyoung.Methods.Negative

open Taeyoung Taeyoung.Methods.PureChordal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The construction -/

/-- The step graphon with cell values `N i j / s` on `Fin k`, uniform measure. -/
noncomputable def stepGraphon (k s : ℕ) [NeZero k] (N : Fin k → Fin k → ℕ)
    (hsymm : ∀ i j, N i j = N j i) (hle : ∀ i j, N i j ≤ s) :
    Graphon (Fin k) (finiteUniformMeasure (Fin k)) where
  toFun i j := (N i j : ℝ) / (s : ℝ)
  measurable := measurable_of_finite _
  nonneg i j := by positivity
  le_one i j := by
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      simp [Nat.le_zero.mp (hle i j)]
    · rw [div_le_one (by exact_mod_cast hs)]
      exact_mod_cast hle i j
  symm i j := by rw [hsymm i j]

@[simp] lemma stepGraphon_apply (k s : ℕ) [NeZero k] (N : Fin k → Fin k → ℕ)
    (hsymm : ∀ i j, N i j = N j i) (hle : ∀ i j, N i j ≤ s) (i j : Fin k) :
    stepGraphon k s N hsymm hle i j = (N i j : ℝ) / (s : ℝ) := rfl

/-! ### Densities from a natural-number weight

`H.edgeFinset` does **not** reduce in the kernel — it goes through a `Fintype`
instance on a subtype — so the weight must be supplied as an explicit
computable function of the assignment.  Each row does that from its own
`edgeFinset` lemma, exactly as the positive method modules do, and what is left
is one `decide +kernel` on a sum of naturals over `V → Fin k`. -/

/-- If the graph weight has a natural-number numerator over a fixed
denominator, the density is a single kernel computation. -/
theorem homDensity_of_natWeight
    (H : SimpleGraph V) [DecidableRel H.Adj] {k : ℕ} [NeZero k]
    (W : Graphon (Fin k) (finiteUniformMeasure (Fin k)))
    (F : (V → Fin k) → ℕ) (D : ℝ)
    (hw : ∀ z, graphWeight H W z = (F z : ℝ) / D) :
    homDensity H W
      = ((∑ z : V → Fin k, F z : ℕ) : ℝ) / ((k : ℝ) ^ Fintype.card V * D) := by
  classical
  rw [homDensity, assignmentMeasure_finiteUniform, finiteUniform_integral]
  simp_rw [hw]
  rw [← Finset.sum_div, div_div, Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [mul_comm]

/-- The edge density of a finite-uniform graphon, in the same form. -/
theorem cliqueDensity_two_of_natWeight {k : ℕ} [NeZero k]
    (W : Graphon (Fin k) (finiteUniformMeasure (Fin k)))
    (F : (Fin 2 → Fin k) → ℕ) (D : ℝ)
    (hw : ∀ z : Fin 2 → Fin k, W (z 0) (z 1) = (F z : ℝ) / D) :
    cliqueDensity 2 W
      = ((∑ z : Fin 2 → Fin k, F z : ℕ) : ℝ) / ((k : ℝ) ^ 2 * D) := by
  have h := homDensity_of_natWeight (⊤ : SimpleGraph (Fin 2)) W F D fun z ↦ by
    rw [graphWeight_top_fin_two]; exact hw z
  rw [cliqueDensity, h, Fintype.card_fin]

/-! ### Packaging -/

/-- **A finite-uniform witness refutes the catalogue proposition.**  Stated for
an arbitrary graphon on `Fin k` with the uniform measure, so that a row may name
its witness once and reuse that name throughout. -/
theorem violatesLowerBound_of_finiteUniform
    {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {P : Polynomial ℝ} {r : ℕ}
    (hP : IsChromaticPolynomial H P) (hr : IsChromaticNumber H r)
    {k : ℕ} [NeZero k] (W : Graphon (Fin k) (finiteUniformMeasure (Fin k)))
    (hadm : admissibleDensity r (cliqueDensity 2 W))
    (hlt : homDensity H W < chromaticTarget (V := V) P (cliqueDensity 2 W)) :
    ViolatesLowerBound H := by
  intro hsat
  exact absurd (hsat P r hP hr (Ω := Fin k) W hadm) (not_le.mpr hlt)

end Taeyoung.Methods.Negative
