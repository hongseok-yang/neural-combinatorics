import Taeyoung.Methods.Link.WeightedGoodman
import Taeyoung.Methods.Chromatic.PawExample
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-!
# The paw: the first row from the link layer

The paw is `L₁` of the rooted triangle–tree family: a triangle with one leaf at
a distinguished root.  Conditioning on the root gives

```
t(L₁, W) = ∫ d(x) · τ(x) dμ(x)
```

and the weighted rooted-triangle inequality plus Jensen turn that into the
target `p²(2p-1)`.

This file supplies the analytic half; the chromatic half is
`Methods/Chromatic/PawExample.lean`.
-/

open MeasureTheory Finset

namespace Taeyoung.Methods.RootedTriangleTree

open Taeyoung Taeyoung.Methods.Link

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Jensen for the degree moments -/

/-- `M j ≥ pʲ`: the degree moments dominate the powers of the edge density. -/
theorem pow_le_moment (W : Graphon Ω μ) (j : ℕ) :
    cliqueDensity 2 W ^ j ≤ moment W j := by
  have hj := ConvexOn.map_integral_le (μ := μ) (s := Set.Ici 0)
    (g := fun t : ℝ => t ^ j) (f := degree W)
    (convexOn_pow (𝕜 := ℝ) j) ((continuous_pow j).continuousOn) isClosed_Ici
    (ae_of_all _ fun x => degree_nonneg W x)
    (integrable_degree W) (integrable_degree_pow W j)
  rwa [integral_degree] at hj

/-! ### The rooted paw, with the root at coordinate `0` -/

/-- The paw with its root first: `0` is joined to `1`, `2`, `3`, and `1`–`2`
closes the triangle. -/
def pawRooted : SimpleGraph (Fin 4) :=
  graphFromEdges 4 [(0, 1), (0, 2), (0, 3), (1, 2)]

instance : DecidableRel pawRooted.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_pawRooted :
    pawRooted.edgeFinset = {s(0, 1), s(0, 2), s(0, 3), s(1, 2)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_pawRooted (W : Graphon Ω μ) (x : Fin 4 → Ω) :
    graphWeight pawRooted W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 0) (x 3) * W (x 1) (x 2) := by
  rw [graphWeight, edgeFinset_pawRooted]
  simp
  ring

lemma graphWeight_pawRooted_cons (W : Graphon Ω μ) (a0 a1 a2 a3 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight pawRooted W
        (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))) =
      W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 := by
  rw [graphWeight_pawRooted]
  rfl

/-- **Rooted factorization.**  Conditioning on the root turns the paw density
into `∫ d · τ`. -/
theorem homDensity_pawRooted (W : Graphon Ω μ) :
    homDensity pawRooted W = ∫ a, degree W a * rootedTriangle W a ∂μ := by
  have hm : Measurable (graphWeight pawRooted W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight pawRooted W x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 => ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 3 → Ω => graphWeight pawRooted W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) (fun y => hb _)]
  -- inner: an integral in `a1`, `a2`, `a3`
  have hstep : ∀ a1 : Ω,
      (∫ y : Fin 2 → Ω,
          graphWeight pawRooted W (Fin.cons a0 (Fin.cons a1 y))
        ∂assignmentMeasure (Fin 2) μ) =
        ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 * degree W a0 ∂μ := by
    intro a1
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 2 → Ω =>
        graphWeight pawRooted W (Fin.cons a0 (Fin.cons a1 y)))
      (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
      (fun y => hb _)]
    refine integral_congr_ae (ae_of_all _ fun a2 => ?_)
    simp only []
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 1 → Ω =>
        graphWeight pawRooted W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
      (hm.comp ((measurable_fin_cons a0).comp
        ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
      (fun y => hb _)]
    -- the last coordinate is the leaf: it integrates to `d a0`
    have hlast : (∫ a3, (∫ y : Fin 0 → Ω,
        graphWeight pawRooted W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
          ∂assignmentMeasure (Fin 0) μ) ∂μ) =
        ∫ a3, (W a0 a1 * W a0 a2 * W a1 a2) * W a0 a3 ∂μ := by
      refine integral_congr_ae (ae_of_all _ fun a3 => ?_)
      simp only []
      rw [show (∫ y : Fin 0 → Ω,
          graphWeight pawRooted W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
            ∂assignmentMeasure (Fin 0) μ) =
          W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 by
        simp [graphWeight_pawRooted_cons]]
      ring
    rw [hlast, integral_const_mul]
    rfl
  rw [integral_congr_ae (ae_of_all _ hstep)]
  -- pull `d a0` out of the remaining double integral
  have hpull : (∫ a1, ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 * degree W a0 ∂μ ∂μ) =
      degree W a0 * rootedTriangle W a0 := by
    have h2 : ∀ a1 : Ω,
        (∫ a2, W a0 a1 * W a0 a2 * W a1 a2 * degree W a0 ∂μ) =
          degree W a0 * ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 ∂μ := by
      intro a1
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun a2 => by ring)
    rw [integral_congr_ae (ae_of_all _ h2), integral_const_mul]
    rfl
  exact hpull



/-! ### The family bound, once and for all

`L_r` is a triangle with `r` leaves at a distinguished root.  Everything about
the family except the rooted factorization is uniform in `r`, so it is proved
here once; an Atlas module then supplies only

* the chromatic polynomial `x(x-1)^{r+1}(x-2)`,
* the chromatic number `3`, and
* the factorization `t(H,W) = ∫ dʳ·τ`.
-/

open Polynomial in
/-- The chromatic target of `L_r` is `p^{r+1}(2p-1)`. -/
theorem chromaticTarget_rootedTree (r : ℕ) {p : ℝ} (hp : p ≠ 1) :
    chromaticTarget (V := Fin (r + 3))
        ((X : ℝ[X]) * (X - C 1) ^ (r + 1) * (X - C 2)) p =
      p ^ (r + 1) * (2 * p - 1) := by
  have hq : (1 : ℝ) - p ≠ 0 := fun h => hp (by linarith)
  rw [chromaticTarget_of_ne_one _ hp]
  simp only [Fintype.card_fin, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
  have e1 : 1 / (1 - p) - 1 = p / (1 - p) := by
    field_simp
    ring
  have e2 : 1 / (1 - p) - 2 = (2 * p - 1) / (1 - p) := by
    field_simp
    ring
  rw [e1, e2, div_pow]
  field_simp
  ring

/-- The analytic half of the family bound: the factorization plus the weighted
rooted-triangle inequality plus Jensen. -/
theorem rootedTree_bound {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj] (W : Graphon Ω μ) (r : ℕ)
    (hfac : homDensity H W = ∫ x, degree W x ^ r * rootedTriangle W x ∂μ)
    (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ (r + 1) * (2 * cliqueDensity 2 W - 1) ≤ homDensity H W := by
  set p := cliqueDensity 2 W with hpdef
  have hppos : 0 < p := by linarith
  have hbound := weighted_rootedTriangle W r
  rw [← hfac] at hbound
  have hM : p ^ (r + 2) ≤ moment W (r + 2) := pow_le_moment W (r + 2)
  have h1 : (2 * p - 1) * p ^ (r + 2) ≤ p * homDensity H W :=
    le_trans (mul_le_mul_of_nonneg_left hM (by linarith)) hbound
  have h3 : p * (p ^ (r + 1) * (2 * p - 1)) ≤ p * homDensity H W := by
    calc p * (p ^ (r + 1) * (2 * p - 1)) = (2 * p - 1) * p ^ (r + 2) := by ring
      _ ≤ p * homDensity H W := h1
  exact le_of_mul_le_mul_left h3 hppos

open Polynomial in
/-- **The rooted triangle–tree family bound**, packaged for an Atlas module. -/
theorem satisfiesLowerBound_of_rootedTree {r : ℕ}
    (H : SimpleGraph (Fin (r + 3))) [DecidableRel H.Adj]
    (hchrom : IsChromaticPolynomial H
      ((X : ℝ[X]) * (X - C 1) ^ (r + 1) * (X - C 2)))
    (hnum : IsChromaticNumber H 3)
    (hfac : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
      homDensity H W = ∫ x, degree W x ^ r * rootedTriangle W x ∂μ) :
    Taeyoung.SatisfiesLowerBound H := by
  intro P s hP hs Ω instM μ instP W hp
  have hPeq : P = (X : ℝ[X]) * (X - C 1) ^ (r + 1) * (X - C 2) :=
    IsChromaticPolynomial.unique (H := H) hP hchrom
  have hseq : s = 3 := IsChromaticNumber.unique (H := H) hs hnum
  subst hPeq
  subst hseq
  have hhalf : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hp
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := rootedTree_bound W r (hfac W) hhalf
  change chromaticTarget (V := Fin (r + 3)) _ (cliqueDensity 2 W) ≤ homDensity H W
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_rootedTree r hone]
    exact hkey



open Polynomial in
/-- **The family packaging, taking the bound directly.**  `L_r` supplies the
bound through its factorization; `Q_s` has a different factorization but the
same target, so it uses this form. -/
theorem satisfiesLowerBound_of_target {r : ℕ}
    (H : SimpleGraph (Fin (r + 3))) [DecidableRel H.Adj]
    (hchrom : IsChromaticPolynomial H
      ((X : ℝ[X]) * (X - C 1) ^ (r + 1) * (X - C 2)))
    (hnum : IsChromaticNumber H 3)
    (hbnd : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
      (1 : ℝ) / 2 ≤ cliqueDensity 2 W →
      cliqueDensity 2 W ^ (r + 1) * (2 * cliqueDensity 2 W - 1) ≤
        homDensity H W) :
    Taeyoung.SatisfiesLowerBound H := by
  intro P s hP hs Ω instM μ instP W hp
  have hPeq : P = (X : ℝ[X]) * (X - C 1) ^ (r + 1) * (X - C 2) :=
    IsChromaticPolynomial.unique (H := H) hP hchrom
  have hseq : s = 3 := IsChromaticNumber.unique (H := H) hs hnum
  subst hPeq
  subst hseq
  have hhalf : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hp
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := hbnd W hhalf
  change chromaticTarget (V := Fin (r + 3)) _ (cliqueDensity 2 W) ≤ homDensity H W
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_rootedTree r hone]
    exact hkey


/-! ### Identifying the rooted paw with the Atlas paw -/

open Taeyoung.Methods.Chromatic in
/-- The relabelling swapping root and leaf. -/
def pawRootedEquiv : Fin 4 ≃ Fin 4 where
  toFun := ![3, 1, 2, 0]
  invFun := ![3, 1, 2, 0]
  left_inv := by decide
  right_inv := by decide

open Taeyoung.Methods.Chromatic in
theorem pawRooted_adj (a b : Fin 4) :
    pawGraph.Adj (pawRootedEquiv a) (pawRootedEquiv b) ↔ pawRooted.Adj a b := by
  revert a b
  decide

open Taeyoung.Methods.Chromatic in
def pawRootedIso : pawRooted ≃g pawGraph where
  toEquiv := pawRootedEquiv
  map_rel_iff' := by intro a b; exact pawRooted_adj a b

/-! ### The chromatic number -/

open Taeyoung.Methods.Chromatic in
theorem paw_count (k : ℕ) :
    properAssignmentCount pawGraph k = (k - 1) * k.descFactorial 3 := by
  rw [properAssignmentCount_of_attachIso pawIso singleton_isClique k,
    properAssignmentCount_top]
  simp

open Taeyoung.Methods.Chromatic in
theorem paw_chromaticNumber : IsChromaticNumber pawGraph 3 where
  positive := by
    rw [paw_count]
    decide
  zero_below k hk := by
    rw [paw_count, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero]

/-! ### The catalogue proposition -/

open Taeyoung.Methods.Chromatic in
/-- The paw's rooted factorization, on the Atlas labelling. -/
theorem paw_factorization {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (W : Graphon Ω μ) :
    homDensity pawGraph W = ∫ x, degree W x ^ 1 * rootedTriangle W x ∂μ := by
  rw [← homDensity_iso W pawRootedIso, homDensity_pawRooted]
  exact integral_congr_ae (ae_of_all _ fun x => by simp)

open Taeyoung.Methods.Chromatic in
/-- **The paw satisfies the common catalogue proposition** — now an instance of
the family bound, which is what validates that packaging. -/
theorem paw_satisfiesLowerBound : Taeyoung.SatisfiesLowerBound pawGraph :=
  satisfiesLowerBound_of_rootedTree (r := 1) pawGraph paw_chromatic
    paw_chromaticNumber (fun W => paw_factorization W)

end Taeyoung.Methods.RootedTriangleTree
