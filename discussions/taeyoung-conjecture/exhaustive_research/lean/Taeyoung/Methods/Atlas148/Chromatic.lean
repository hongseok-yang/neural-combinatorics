import Taeyoung.Methods.Atlas148.Low
import Taeyoung.Methods.Negative.Chromatic

/-!
# Atlas 148: the chromatic data, and the catalogue proposition

The chromatic polynomial is

```
χ_{F₁₄₈}(r) = r(r-1)(r-2)²(r²-3r+3),
```

whose last factor is irreducible over the rationals.  The catalogue's usual
route for a positive row — an attachment tower over a clique, read off by
`affineProd` — therefore does not apply: those towers only ever produce
products of affine factors.  What does apply is the surjective-count route the
negative rows use, `isChromaticPolynomial_of_surjCount`, with the six counts
checked by `decide +kernel`.  The five-colour count is the expensive one; the
top count is supplied by `surjCount_card` instead of being enumerated.

The target is then obtained the way `Methods/OddCycleC5/Chromatic.lean` does
it, by `chromaticTarget_of_ne_one` and one `field_simp; ring`, rather than by
`chromaticTarget_affineProd`:

```
Φ_{F₁₄₈}(p) = (1-p)⁶·χ(1/(1-p)) = p(2p-1)²(3p²-3p+1).
```
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.Atlas148

open Taeyoung Taeyoung.Methods.Negative

/-! ### The six surjective counts -/

theorem s148_0 : surjCount graph148 0 = 0 := by decide +kernel
theorem s148_1 : surjCount graph148 1 = 0 := by decide +kernel
theorem s148_2 : surjCount graph148 2 = 0 := by decide +kernel
theorem s148_3 : surjCount graph148 3 = 18 := by decide +kernel
theorem s148_4 : surjCount graph148 4 = 264 := by decide +kernel
theorem s148_5 : surjCount graph148 5 = 840 := by decide +kernel

theorem s148_6 : surjCount graph148 6 = 720 := by
  rw [surjCount_card graph148]
  decide

/-! ### The chromatic polynomial and number -/

theorem count148 (k : ℕ) :
    properAssignmentCount graph148 k
      = 18 * k.choose 3 + 264 * k.choose 4 + 840 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph148 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s148_0, s148_1, s148_2, s148_3, s148_4, s148_5, s148_6]
  ring

theorem num148 : IsChromaticNumber graph148 3 where
  positive := by rw [count148]; decide
  zero_below k hk := by
    rw [count148]
    interval_cases k <;> decide

theorem chrom148 : IsChromaticPolynomial graph148
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph148 j : ℝ) / (j).factorial) * ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph148

/-! ### The catalogue proposition -/

set_option maxHeartbeats 1000000 in
/-- **Atlas 148 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_148 : Taeyoung.SatisfiesLowerBound graph148 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph148 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph148) hP chrom148
  have hreq : r = 3 := IsChromaticNumber.unique (H := graph148) hr num148
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := homDensity_graph148_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph148 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = cliqueDensity 2 W * (2 * cliqueDensity 2 W - 1) ^ 2 *
            (3 * cliqueDensity 2 W ^ 2 - 3 * cliqueDensity 2 W + 1) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s148_0, s148_1, s148_2, s148_3, s148_4, s148_5, s148_6,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

end Taeyoung.Methods.Atlas148
