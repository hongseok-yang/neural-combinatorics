import Taeyoung.Methods.Atlas178.Page
import Taeyoung.Methods.AffineProduct
import Taeyoung.Methods.BaseCone.Rows
import Taeyoung.Methods.PawCone.Rows

/-!
# Atlas 178: the catalogue row

`notes/atlas178_half_degree_weighted_k4.tex` Theorem 5.1.  Three inequalities
compose:

```
I₄² ≤ T·t(H₁₇₈,W)        the page compression      (`sq_halfK4_le`)
I₄  ≥ (3p-2)·I           the adjacent-clique ratio (`halfK4_ge`)
I²  ≥ p²(2p-1)·T         the triangle moment       (`sq_halfTri_ge`)
```

Multiplying and cancelling the single factor `T ≥ p(2p-1) ≥ 2/9 > 0` gives
`t(H₁₇₈,W) ≥ p²(2p-1)(3p-2)²`, which is the chromatic target of
`P₁₇₈(z) = z(z-1)²(z-2)(z-3)²`.

The chromatic tower is the spine triangle, then a page on the spine, then a
second page on the same spine, then a leaf on the first page: the three attached
cliques have sizes `3`, `3`, `1`.
-/

open MeasureTheory Polynomial Finset

namespace Taeyoung.Methods.Atlas178

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link Taeyoung.Methods.K4Tail
  Taeyoung.Methods.CliqueLeaf Taeyoung.Methods.PureChordal
  Taeyoung.Methods.TriangleDensity Taeyoung.Methods.BaseCone
  Taeyoung.Methods.PawCone

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The bound -/

/-- **Atlas 178 dominates its target.** -/
theorem graph178_bound (W : Graphon Ω μ) (hp : (2:ℝ)/3 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 2 * (2 * cliqueDensity 2 W - 1) *
        (3 * cliqueDensity 2 W - 2) ^ 2 ≤ homDensity graph178 W := by
  set p := cliqueDensity 2 W with hpdef
  set T := cliqueDensity 3 W with hTdef
  have hc4 : (0:ℝ) ≤ 3 * p - 2 := by linarith
  have hgood : p * (2 * p - 1) ≤ T := by
    rw [hpdef, hTdef]
    exact goodman_triangle_bound W (by rw [← hpdef]; linarith)
  have hT0 : (0:ℝ) < T := lt_of_lt_of_le (by nlinarith) hgood
  have hI0 : 0 ≤ halfTri W := halfTri_nonneg W
  have hI2 : p ^ 2 * (2 * p - 1) * T ≤ halfTri W ^ 2 := by
    rw [hpdef, hTdef]; exact sq_halfTri_ge W hp
  have hI4 : (3 * p - 2) * halfTri W ≤ halfK4 W := by
    rw [hpdef]; exact halfK4_ge W hp
  have step1 : (3 * p - 2) ^ 2 * (p ^ 2 * (2 * p - 1) * T) ≤
      (3 * p - 2) ^ 2 * halfTri W ^ 2 :=
    mul_le_mul_of_nonneg_left hI2 (sq_nonneg _)
  have step2 : (3 * p - 2) ^ 2 * halfTri W ^ 2 ≤ halfK4 W ^ 2 := by
    nlinarith [hI4, hI0, hc4, mul_nonneg hc4 hI0]
  have step3 : halfK4 W ^ 2 ≤ T * homDensity graph178 W := by
    rw [hTdef]; exact sq_halfK4_le W
  have final : T * (p ^ 2 * (2 * p - 1) * (3 * p - 2) ^ 2) ≤
      T * homDensity graph178 W := by nlinarith [step1, step2, step3]
  exact le_of_mul_le_mul_left final hT0

/-! ### Chromatic data and the catalogue proposition -/

lemma affineProd_178 (z : ℝ) :
    affineProd [0, 1, 1, 2, 3, 3] z = z ^ 2 * (2 * z - 1) * (3 * z - 2) ^ 2 := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_cons, affineProd_nil]
  ring

/-- The spine triangle `{0,1,2}`, then the page `3`, then the page `4`, then the
leaf `5` on the page `3`. -/
def equiv178 : Option (Option (Option (Fin 3))) ≃ Fin 6 where
  toFun a := match a with
    | none => 5
    | some none => 4
    | some (some none) => 3
    | some (some (some i)) => ![0, 1, 2] i
  invFun j := ![some (some (some 0)), some (some (some 1)), some (some (some 2)),
    some (some none), some none, none] j
  left_inv := by decide
  right_inv := by decide

def iso178 :
    attachVertex (attachVertex (attachVertex (⊤ : SimpleGraph (Fin 3))
      {0, 1, 2}) {some 0, some 1, some 2}) {some none} ≃g graph178 where
  toEquiv := equiv178
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom178 : IsChromaticPolynomial graph178
    ((([0, 1, 1, 2, 3, 3] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have hclique2 : (attachVertex (⊤ : SimpleGraph (Fin 3)) {0, 1, 2}).IsClique
      ({some 0, some 1, some 2} : Finset (Option (Fin 3))) := by decide
  have h := isChromaticPolynomial_of_attachIso (H' := graph178) iso178
    (isClique_singleton _ (some none))
    (isChromaticPolynomial_attachVertex hclique2
      (isChromaticPolynomial_attachVertex (isCliqueTop _)
        (isChromaticPolynomial_top 3)))
  rw [show ((({0, 1, 2} : Finset (Fin 3))).card) = 3 from by decide,
    show ((({some 0, some 1, some 2} : Finset (Option (Fin 3)))).card) = 3 from
      by decide,
    Finset.card_singleton] at h
  have hpoly :
      ((([0, 1, 1, 2, 3, 3] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) *
        ((X - C ((3 : ℕ) : ℝ)) * ((X - C ((3 : ℕ) : ℝ)) *
          ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ)))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count178 (k : ℕ) :
    properAssignmentCount graph178 k =
      (k - 1) * ((k - 3) * ((k - 3) * k.descFactorial 3)) := by
  have hclique2 : (attachVertex (⊤ : SimpleGraph (Fin 3)) {0, 1, 2}).IsClique
      ({some 0, some 1, some 2} : Finset (Option (Fin 3))) := by decide
  rw [properAssignmentCount_of_attachIso (H' := graph178) iso178
      (isClique_singleton _ (some none)) k,
    properAssignmentCount_attachVertex hclique2,
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show ((({0, 1, 2} : Finset (Fin 3))).card) = 3 from by decide,
    show ((({some 0, some 1, some 2} : Finset (Option (Fin 3)))).card) = 3 from
      by decide,
    Finset.card_singleton]

theorem num178 : IsChromaticNumber graph178 4 where
  positive := by rw [count178]; decide
  zero_below k hk := by
    rw [count178]
    have h3 : k - 3 = 0 := by omega
    simp [h3]

/-- **Atlas 178 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_178 : Taeyoung.SatisfiesLowerBound graph178 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P =
      (([0, 1, 1, 2, 3, 3] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := graph178) hP chrom178
  have hreq : r = 4 := IsChromaticNumber.unique (H := graph178) hr num178
  subst hPeq
  subst hreq
  have hp : (2 : ℝ) / 3 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := graph178_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 2, 3, 3] (by norm_num) hone,
      affineProd_178]
    exact hkey

end Taeyoung.Methods.Atlas178
