import ApicesCommonness.Common.Graph.HomDensity
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The two-coordinate marginal of a product measure

For distinct `i j : Fin v`, the map `x ↦ (x i, x j)` pushes `μ^{⊗v}` forward to `μ ⊗ μ`
(`pairMarginal_measurePreserving`).  This is the one piece of product-measure plumbing behind the
`L¹` bound on homomorphism densities (plan §2.1): the integral of a function of a single edge's two
endpoints is a double integral over `Ω × Ω` (`integral_pair`).

The proof compares the two measures on rectangles (`Measure.prod_eq`): the preimage of `s ×ˢ t` is
the box with sides `s` at `i`, `t` at `j` and `Ω` elsewhere, whose mass is `μ s · μ t` by
`Measure.pi_pi`.
-/

open MeasureTheory Finset

namespace ApicesCommonness

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Pair marginal.**  For `i ≠ j`, `x ↦ (x i, x j)` is measure preserving from `μ^{⊗v}` to
`μ ⊗ μ`. -/
theorem pairMarginal_measurePreserving {v : ℕ} {i j : Fin v} (hij : i ≠ j) :
    MeasurePreserving (fun x : Fin v → Ω => (x i, x j)) (Measure.pi fun _ => μ) (μ.prod μ) := by
  classical
  have hmeas : Measurable fun x : Fin v → Ω => (x i, x j) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  refine ⟨hmeas, (Measure.prod_eq fun s t hs ht => ?_).symm⟩
  rw [Measure.map_apply hmeas (hs.prod ht)]
  set box : Fin v → Set Ω := fun l => if l = i then s else if l = j then t else Set.univ with hbox
  have hpre : (fun x : Fin v → Ω => (x i, x j)) ⁻¹' (s ×ˢ t) = Set.univ.pi box := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, hbox]
    constructor
    · rintro ⟨hs', ht'⟩ l
      by_cases hli : l = i
      · subst hli; simpa using hs'
      · by_cases hlj : l = j
        · subst hlj; simpa [hli] using ht'
        · simp [hli, hlj]
    · intro h
      refine ⟨by simpa using h i, ?_⟩
      have := h j
      simpa [hij.symm] using this
  have hfac : ∀ l, μ (box l) = (if l = i then μ s else 1) * (if l = j then μ t else 1) := by
    intro l
    by_cases hli : l = i
    · subst hli; simp [hbox, hij]
    · by_cases hlj : l = j
      · subst hlj; simp [hbox, hli]
      · simp [hbox, hli, hlj]
  rw [hpre, Measure.pi_pi]
  simp only [hfac, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]

/-- The integral of a function of one edge's endpoints is the double integral over `Ω × Ω`. -/
theorem integral_pair {v : ℕ} {i j : Fin v} (hij : i ≠ j) {f : Ω × Ω → ℝ}
    (hf : AEStronglyMeasurable f (μ.prod μ)) :
    ∫ x, f (x i, x j) ∂(Measure.pi fun _ => μ) = ∫ p, f p ∂(μ.prod μ) := by
  have hmp := pairMarginal_measurePreserving (μ := μ) hij
  rw [← hmp.map_eq] at hf ⊢
  exact (integral_map hmp.measurable.aemeasurable hf).symm

end ApicesCommonness
