import Taeyoung.Methods.PureChordal.BalancedMultipartite

/-!
# The Turán tensor graphon

The analytic half of the 19 negative rows.  Each witness in
`notes/even_girth_false.tex` is a two-factor tensor construction, and the two
factors are balanced complete multipartite graphons.  Their categorical (tensor)
product is again a finite graphon: on `Fin a × Fin b` with the uniform measure,
two points are adjacent exactly when they differ in **both** coordinates,

```
W((x₁,x₂),(y₁,y₂)) = [x₁ ≠ y₁]·[x₂ ≠ y₂].
```

**No measure-theoretic product is needed.**  The naive route — build
`Graphon (Ω₁ × Ω₂) (μ₁.prod μ₂)` and push `homDensity` through the measurable
equivalence `(V → Ω₁ × Ω₂) ≃ᵐ (V → Ω₁) × (V → Ω₂)` — is avoided entirely,
because on a *finite uniform* space `homDensity` is already a finite sum
(`assignmentMeasure_finiteUniform`, `finiteUniform_integral`), and an assignment
`V → Fin a × Fin b` is proper for this graphon exactly when both of its
coordinate projections are proper.  So the factorisation is
`Equiv.arrowProdEquivProdArrow` plus `Finset.sum_mul_sum`, and

```
t(H, T_a ⊗ T_b) = χ_H(a)·χ_H(b) / (ab)^{v(H)},
p               = (1 - 1/a)(1 - 1/b).
```

Both `χ_H(a)` and `χ_H(b)` are `properAssignmentCount`, so
`Methods/Negative/ProperCount.lean` evaluates them by `decide +kernel`, and
`Methods/Negative/Chromatic.lean` supplies the chromatic polynomial the
`ViolatesLowerBound` statement has to exhibit.  What remains per row is exact
rational arithmetic comparing the display above with `Φ_H(p)`.
-/

open Finset MeasureTheory

namespace Taeyoung.Methods.Negative

open Taeyoung Taeyoung.Methods.PureChordal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The categorical product of two balanced complete multipartite graphons:
adjacent iff the coordinates differ in both factors. -/
def tensorTuran (a b : ℕ) [NeZero a] [NeZero b] :
    Graphon (Fin a × Fin b) (finiteUniformMeasure (Fin a × Fin b)) where
  toFun x y := (if x.1 = y.1 then 0 else 1) * (if x.2 = y.2 then 0 else 1)
  measurable := measurable_of_finite _
  nonneg := by intro x y; split <;> split <;> norm_num
  le_one := by intro x y; split <;> split <;> norm_num
  symm := by
    intro x y
    congr 1
    · rcases eq_or_ne x.1 y.1 with h | h
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg h.symm]
    · rcases eq_or_ne x.2 y.2 with h | h
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg h.symm]

section Density

variable (H : SimpleGraph V) [DecidableRel H.Adj]

noncomputable local instance instDecidableIsProper' {k : ℕ} (x : V → Fin k) :
    Decidable (IsProperAssignment H x) := Classical.propDecidable _

variable (a b : ℕ) [NeZero a] [NeZero b]

/-- An assignment is proper for the tensor exactly when both projections are. -/
lemma graphWeight_tensorTuran (z : V → Fin a × Fin b) :
    graphWeight H (tensorTuran a b) z =
      (if IsProperAssignment H (fun v ↦ (z v).1) then (1 : ℝ) else 0) *
        (if IsProperAssignment H (fun v ↦ (z v).2) then (1 : ℝ) else 0) := by
  classical
  by_cases h1 : IsProperAssignment H (fun v ↦ (z v).1) <;>
    by_cases h2 : IsProperAssignment H (fun v ↦ (z v).2)
  · rw [if_pos h1, if_pos h2, mul_one]
    refine Finset.prod_eq_one fun e he ↦ ?_
    induction e using Sym2.inductionOn with
    | _ u v =>
        have huv : H.Adj u v := by simpa [SimpleGraph.mem_edgeFinset] using he
        simp [edgeValue, Sym2.lift_mk, tensorTuran, h1 huv, h2 huv]
  · rw [if_neg h2, mul_zero]
    simp only [IsProperAssignment, not_forall] at h2
    rcases h2 with ⟨u, v, huv, hsame⟩
    refine Finset.prod_eq_zero (i := s(u, v)) ?_ ?_
    · simpa [SimpleGraph.mem_edgeFinset] using huv
    · simp [edgeValue, Sym2.lift_mk, tensorTuran, not_ne_iff.mp hsame]
  · rw [if_neg h1, zero_mul]
    simp only [IsProperAssignment, not_forall] at h1
    rcases h1 with ⟨u, v, huv, hsame⟩
    refine Finset.prod_eq_zero (i := s(u, v)) ?_ ?_
    · simpa [SimpleGraph.mem_edgeFinset] using huv
    · simp [edgeValue, Sym2.lift_mk, tensorTuran, not_ne_iff.mp hsame]
  · rw [if_neg h1, zero_mul]
    simp only [IsProperAssignment, not_forall] at h1
    rcases h1 with ⟨u, v, huv, hsame⟩
    refine Finset.prod_eq_zero (i := s(u, v)) ?_ ?_
    · simpa [SimpleGraph.mem_edgeFinset] using huv
    · simp [edgeValue, Sym2.lift_mk, tensorTuran, not_ne_iff.mp hsame]

/-- **The density multiplies.** -/
theorem homDensity_tensorTuran :
    homDensity H (tensorTuran a b) =
      (properAssignmentCount H a : ℝ) * (properAssignmentCount H b : ℝ) /
        ((a : ℝ) * (b : ℝ)) ^ Fintype.card V := by
  classical
  rw [homDensity, assignmentMeasure_finiteUniform, finiteUniform_integral]
  simp_rw [graphWeight_tensorTuran H a b]
  have hsum : (∑ z : V → Fin a × Fin b,
      (if IsProperAssignment H (fun v ↦ (z v).1) then (1 : ℝ) else 0) *
        (if IsProperAssignment H (fun v ↦ (z v).2) then (1 : ℝ) else 0)) =
      (∑ x : V → Fin a, if IsProperAssignment H x then (1 : ℝ) else 0) *
        (∑ y : V → Fin b, if IsProperAssignment H y then (1 : ℝ) else 0) := by
    let E : (V → Fin a × Fin b) ≃ (V → Fin a) × (V → Fin b) :=
      { toFun := fun z ↦ (fun v ↦ (z v).1, fun v ↦ (z v).2)
        invFun := fun q v ↦ (q.1 v, q.2 v)
        left_inv := fun z ↦ by funext v; simp
        right_inv := fun q ↦ by simp }
    rw [← Equiv.sum_comp E.symm, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
    rfl
  rw [hsum,
    show (∑ x : V → Fin a, if IsProperAssignment H x then (1 : ℝ) else 0) =
      properAssignmentCount H a by simp [properAssignmentCount],
    show (∑ y : V → Fin b, if IsProperAssignment H y then (1 : ℝ) else 0) =
      properAssignmentCount H b by simp [properAssignmentCount]]
  congr 1
  simp [Fintype.card_prod, mul_pow]

/-- **The edge density multiplies too.** -/
theorem edgeDensity_tensorTuran :
    cliqueDensity 2 (tensorTuran a b) = (1 - 1 / (a : ℝ)) * (1 - 1 / (b : ℝ)) := by
  have ha : (a : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne a)
  have hb : (b : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne b)
  have hdesc : ∀ n : ℕ, n ≠ 0 → ((n.descFactorial 2 : ℕ) : ℝ) = ((n : ℝ) - 1) * n := by
    intro n hn
    have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    simp only [Nat.descFactorial, Nat.cast_mul, Nat.cast_sub h1, Nat.cast_one]
    simp
  rw [cliqueDensity, homDensity_tensorTuran, properAssignmentCount_top,
    properAssignmentCount_top]
  simp only [Fintype.card_fin]
  rw [hdesc a (NeZero.ne a), hdesc b (NeZero.ne b)]
  field_simp

end Density

/-! ### Packaging a negative row

`ViolatesLowerBound H` is `¬ SatisfiesLowerBound H`, and the latter is a
universally quantified statement, so refuting it is exactly a matter of
specialising it at one witness.  Everything below is bookkeeping; the content is
the two density formulas above. -/

/-- **A tensor-Turán witness refutes the catalogue proposition.** -/
theorem violatesLowerBound_of_tensor
    {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {P : Polynomial ℝ} {r : ℕ}
    (hP : IsChromaticPolynomial H P) (hr : IsChromaticNumber H r)
    (a b : ℕ) [NeZero a] [NeZero b]
    (hadm : admissibleDensity r ((1 - 1 / (a : ℝ)) * (1 - 1 / (b : ℝ))))
    (hlt : homDensity H (tensorTuran a b) <
      chromaticTarget (V := V) P ((1 - 1 / (a : ℝ)) * (1 - 1 / (b : ℝ)))) :
    ViolatesLowerBound H := by
  intro hsat
  have hp : edgeDensity (tensorTuran a b) =
      (1 - 1 / (a : ℝ)) * (1 - 1 / (b : ℝ)) := edgeDensity_tensorTuran a b
  have hkey := hsat P r hP hr (Ω := Fin a × Fin b) (tensorTuran a b)
    (by rw [hp]; exact hadm)
  rw [hp] at hkey
  exact absurd hkey (not_le.mpr hlt)

end Taeyoung.Methods.Negative
