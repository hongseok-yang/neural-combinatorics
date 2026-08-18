import Taeyoung.Methods.BaseCone
import Taeyoung.Methods.Link.ConeChromatic
import Taeyoung.Methods.OddCycleC5.Main
import Taeyoung.Methods.OddCycleC5.Chromatic

/-!
# The clique join of an odd cycle, at `K₁ ∨ C₅`

Atlas 187.  The base bound is the analytic `C₅` inequality of
`Methods/OddCycleC5`, which needs no hypothesis on the edge density at all, so
the only work is the shape of the target

```
Φ_{C₅}(z) = z⁵ - z(1-z)⁴ = 4z⁴ - 6z³ + 4z² - z = z(2z-1)(2z² - 2z + 1).
```

The last factor is `z² + (1-z)² > 0`, so `Φ_{C₅} ≥ 0` exactly on `[1/2,1]`, and
the quartic remainder of its tangent at `c` factors as

```
Φ_{C₅}(w) - Φ_{C₅}(c) - Φ_{C₅}'(c)(w-c) = (w-c)²(4w² + 8wc + 12c² - 6w - 12c + 4),
```

whose second factor is `1 + 2(w - ½) + 4(c - ½) + 4(w-½)² + 8(w-½)(c-½) + 12(c-½)²`
— every coefficient nonnegative.  So the affine minorant holds on `[1/2,1]` and
`coneGraph_pow_bound` applies.

`K₁ ∨ C₅` has no simplicial vertex, so its chromatic polynomial cannot come from
an attachment tower; it comes instead from `isChromaticPolynomial_coneGraph`.
-/

open MeasureTheory Polynomial

namespace Taeyoung.Methods.OddCycleCone

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link Taeyoung.Methods.OddCycleC5

-- `Ω` is fixed at universe `0`, as in `Methods/ConeBound.lean`.
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The five-cycle target -/

/-- `Φ_{C₅}(z)`, in the form the analytic inequality proves. -/
def c5Target (z : ℝ) : ℝ := z ^ 5 - z * (1 - z) ^ 4

/-- Its derivative.  `Φ_{C₅}` is a quartic: the two fifth-degree terms cancel. -/
def c5TargetDeriv (z : ℝ) : ℝ := 16 * z ^ 3 - 18 * z ^ 2 + 8 * z - 1

lemma c5Target_expand (z : ℝ) :
    c5Target z = 4 * z ^ 4 - 6 * z ^ 3 + 4 * z ^ 2 - z := by
  rw [c5Target]; ring

lemma c5Target_half : c5Target (1 / 2) = 0 := by norm_num [c5Target]

@[simp] lemma c5Target_one : c5Target 1 = 1 := by norm_num [c5Target]

lemma c5Target_nonneg {c : ℝ} (hc : 1 / 2 ≤ c) : 0 ≤ c5Target c := by
  have h1 : (0 : ℝ) ≤ c := by linarith
  have h2 : (0 : ℝ) ≤ 2 * c - 1 := by linarith
  have h3 : (0 : ℝ) ≤ 2 * c ^ 2 - 2 * c + 1 := by nlinarith [sq_nonneg (2 * c - 1)]
  rw [c5Target_expand]
  nlinarith [mul_nonneg (mul_nonneg h1 h2) h3]

lemma c5TargetDeriv_nonneg {c : ℝ} (hc : 1 / 2 ≤ c) : 0 ≤ c5TargetDeriv c := by
  have ht : (0 : ℝ) ≤ c - 1 / 2 := by linarith
  rw [c5TargetDeriv]
  nlinarith [mul_nonneg (mul_nonneg ht ht) ht, mul_nonneg ht ht]

/-- **The affine minorant of `Φ_{C₅}`.** -/
lemma c5Target_tangent {c : ℝ} (hc : 1 / 2 ≤ c) (w : ℝ) (hw : 1 / 2 ≤ w)
    (_hw1 : w ≤ 1) :
    c5Target c + c5TargetDeriv c * (w - c) ≤ c5Target w := by
  have hs : (0 : ℝ) ≤ w - 1 / 2 := by linarith
  have ht : (0 : ℝ) ≤ c - 1 / 2 := by linarith
  have hinner : (0 : ℝ) ≤ 4 * w ^ 2 + 8 * w * c + 12 * c ^ 2 - 6 * w - 12 * c + 4 := by
    nlinarith [mul_nonneg hs ht, sq_nonneg (w - 1 / 2), sq_nonneg (c - 1 / 2)]
  rw [c5Target_expand, c5Target_expand, c5TargetDeriv]
  nlinarith [mul_nonneg (sq_nonneg (w - c)) hinner]

/-! ### The base bound and the cone bound -/

theorem base_c5 {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (V : Graphon Ω ν)
    (_hz : 1 / 2 ≤ cliqueDensity 2 V) :
    c5Target (cliqueDensity 2 V) ≤ homDensity c5 V := by
  rw [c5Target]
  exact c5_homDensity_bound V

theorem coneC5_bound (W : Graphon Ω μ) (hp : 2 / 3 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 5 * c5Target (2 - 1 / cliqueDensity 2 W) ≤
      homDensity (coneGraph c5) W := by
  have hppos : (0 : ℝ) < cliqueDensity 2 W := by linarith
  have hinv : 1 / cliqueDensity 2 W ≤ 3 / 2 := by
    rw [div_le_iff₀ hppos]; linarith
  have hc : (1 : ℝ) / 2 ≤ 2 - 1 / cliqueDensity 2 W := by linarith
  exact BaseCone.coneGraph_pow_bound (h := 3) c5 W (φ := c5Target) (a := 1 / 2)
    (lam := c5TargetDeriv (2 - 1 / cliqueDensity 2 W))
    c5Target_half (c5TargetDeriv_nonneg hc) (by norm_num) hppos
    (c5Target_tangent hc) (c5Target_nonneg hc) base_c5

/-! ### Chromatic data and the catalogue proposition -/

theorem chrom187 : IsChromaticPolynomial (coneGraph c5)
    ((X : ℝ[X]) * ((((X : ℝ[X]) - 1) ^ 5 - ((X : ℝ[X]) - 1)).comp ((X : ℝ[X]) - 1))) :=
  isChromaticPolynomial_coneGraph c5 isChromaticPolynomial_c5

theorem num187 : IsChromaticNumber (coneGraph c5) 4 :=
  isChromaticNumber_coneGraph c5 isChromaticNumber_c5

lemma chromaticTarget_187 {p : ℝ} (hp : p ≠ 1) (hp0 : p ≠ 0) :
    Taeyoung.chromaticTarget (V := Fin 6)
        ((X : ℝ[X]) * ((((X : ℝ[X]) - 1) ^ 5 - ((X : ℝ[X]) - 1)).comp ((X : ℝ[X]) - 1))) p =
      p ^ 5 * c5Target (2 - 1 / p) := by
  have hq : (1 : ℝ) - p ≠ 0 := fun h ↦ hp (by linarith)
  rw [Taeyoung.chromaticTarget_of_ne_one _ hp]
  simp only [Fintype.card_fin, eval_mul, eval_comp, eval_sub, eval_pow, eval_X,
    eval_one]
  rw [c5Target]
  field_simp
  ring

/-- **Atlas 187 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_187 : Taeyoung.SatisfiesLowerBound (coneGraph c5) := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = (X : ℝ[X]) * ((((X : ℝ[X]) - 1) ^ 5 - ((X : ℝ[X]) - 1)).comp ((X : ℝ[X]) - 1)) :=
    IsChromaticPolynomial.unique (H := coneGraph c5) hP chrom187
  have hreq : r = 4 := IsChromaticNumber.unique (H := coneGraph c5) hr num187
  subst hPeq
  subst hreq
  have hp : (2 : ℝ) / 3 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hppos : (0 : ℝ) < cliqueDensity 2 W := by linarith
  have hkey := coneC5_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_187 hone (ne_of_gt hppos)]
    exact hkey

end Taeyoung.Methods.OddCycleCone
