import Taeyoung.Methods.CliqueLeaf.Density

/-!
# Cliques with common pendant leaves: the catalogue target

`H_{r,k}` has `χ_H(x) = (x)_r (x-1)^k`, so its catalogue target is

  `Φ_H(p) = (1-p)^{r+k} · (1/(1-p))_r · (1/(1-p) - 1)^k = p^k · A_r(p)`,

which is exactly what `cliqueLeaf_density` bounds `t(H,W)` below by.  This file
records that identification and packages the two halves into the shared
`SatisfiesLowerBound` predicate, in the same shape as
`satisfiesLowerBound_of_rootedTree`: the chromatic data is taken as a hypothesis,
so an Atlas module supplies it for its own labelling.
-/

open MeasureTheory Polynomial

namespace Taeyoung.Methods.CliqueLeaf

open Taeyoung Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The catalogue target of `H_{r,k}` is `p^k·A_r(p)`.** -/
theorem chromaticTarget_cliqueLeaf (s k : ℕ) {p : ℝ} (hp : p ≠ 1) :
    chromaticTarget (V := Fin (s + 2 + k + 1))
        ((∏ i ∈ Finset.range (s + 3), (X - C (i : ℝ))) * (X - C 1) ^ k) p =
      p ^ k * cliquePoly (s + 3) p := by
  have hq : (1 : ℝ) - p ≠ 0 := fun h ↦ hp (by linarith)
  rw [chromaticTarget_of_ne_one _ hp]
  simp only [Fintype.card_fin, eval_mul, eval_pow, eval_sub, eval_X, eval_C,
    eval_prod]
  have e1 : ∀ i ∈ Finset.range (s + 3),
      (1 / (1 - p) - (i : ℝ)) = (1 - (i : ℝ) * (1 - p)) / (1 - p) := by
    intro i _
    field_simp
  rw [Finset.prod_congr rfl e1, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_range, ← cliquePoly]
  have e2 : (1 / (1 - p) - 1) = p / (1 - p) := by
    field_simp
    ring
  rw [e2, div_pow, show s + 2 + k + 1 = (s + 3) + k by omega, pow_add]
  field_simp

@[simp] lemma cliquePoly_at_one (s : ℕ) : cliquePoly s 1 = 1 := by
  simp [cliquePoly]

/-- **The clique common-leaf family, packaged for an Atlas module.**  The
chromatic polynomial and chromatic number are hypotheses; the density bound is
`cliqueLeaf_density`. -/
theorem satisfiesLowerBound_of_cliqueLeaf (s k : ℕ)
    (hchrom : IsChromaticPolynomial (cliqueLeafGraph s k)
      ((∏ i ∈ Finset.range (s + 3), (X - C (i : ℝ))) * (X - C 1) ^ k))
    (hnum : IsChromaticNumber (cliqueLeafGraph s k) (s + 3)) :
    Taeyoung.SatisfiesLowerBound (cliqueLeafGraph s k) := by
  intro P r hP hr Ω instM μ instP W hp
  have hPeq : P = (∏ i ∈ Finset.range (s + 3), (X - C (i : ℝ))) * (X - C 1) ^ k :=
    IsChromaticPolynomial.unique (H := cliqueLeafGraph s k) hP hchrom
  have hreq : r = s + 3 :=
    IsChromaticNumber.unique (H := cliqueLeafGraph s k) hr hnum
  subst hPeq
  subst hreq
  have hthr : 1 - 1 / ((s : ℝ) + 2) ≤ cliqueDensity 2 W := by
    have h := hp
    simp only [admissibleDensity, edgeDensity] at h
    have hcast : ((s + 3 - 1 : ℕ) : ℝ) = (s : ℝ) + 2 := by
      push_cast [show s + 3 - 1 = s + 2 from rfl]
      ring
    rwa [hcast] at h
  have hkey := cliqueLeaf_density W s k hthr
  change chromaticTarget (V := Fin (s + 2 + k + 1)) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    simpa using hkey
  · rw [chromaticTarget_cliqueLeaf s k hone]
    exact hkey

end Taeyoung.Methods.CliqueLeaf
