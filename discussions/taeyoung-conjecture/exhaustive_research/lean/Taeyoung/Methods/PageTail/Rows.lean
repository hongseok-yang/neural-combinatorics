import Taeyoung.Methods.PageTail.Core
import Taeyoung.Methods.ForestCone.Rows
import Taeyoung.Methods.BaseCone.Rows

/-!
# Atlas 123: the two-page book with a two-edge tail on a page

`P₂` of `notes/triangle_book_page_two_edge_tail.tex`: spine `0,1`, pages `2,3`,
and a two-edge tail `2–4–5` hanging off the page `2`.  Peeling gives

```
t(P₂,W) = ∫∫ W(x,y)·G(x,y)·S(x,y),
G = ∫W(x,z)W(y,z)A(z)dz,   S = ∫W(x,z)W(y,z)dz,   A = T_W d.
```

The chain, with `R = ∫W(x,z)W(y,z)√(A(z))dz`:

```
t = ∫∫ W·G·S ≥ ∫∫ W·R²        (Cauchy--Schwarz inside the page, R² ≤ S·G)
             ≥ (∫∫W·R)²/p      (Cauchy--Schwarz on μ⊗μ, weight W)
             = (∫√A·τ)²/p      (Fubini)
             ≥ (p²(2p-1))²/p = p³(2p-1)² = Φ.
```

At `m = 2` the note's average over the page orbit, which distributes `A` with
exponent `1/m`, *is* the first Cauchy–Schwarz; nothing else of the general
argument is needed, and `m = 3` would already have seven vertices.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.PageTail

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PureChordal Taeyoung.Methods.PawCone
  Taeyoung.Methods.BaseCone Taeyoung.Methods.ForestCone
  Taeyoung.Methods.BookTail

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The graph -/

/-- Spine `0,1`; pages `2,3`; tail `2–4–5` on the page `2`. -/
def book123 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, 4), (4, 5)]

instance : DecidableRel book123.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_book123 :
    book123.edgeFinset =
      {s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(1, 3), s(2, 4), s(4, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_book123 (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight book123 W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
        W (x 1) (x 3) * W (x 2) (x 4) * W (x 4) (x 5) := by
  rw [graphWeight, edgeFinset_book123]
  simp
  ring

lemma graphWeight_book123_cons (W : Graphon Ω μ) (a0 a1 a2 a3 a4 a5 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight book123 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
        (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y)))))) =
      W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * W a2 a4 * W a4 a5 := by
  rw [graphWeight_book123]
  rfl

/-! ### The density identity -/

/-- **The density of Atlas 123 is `∫∫ W·G·S`.** -/
theorem homDensity_book123 (W : Graphon Ω μ) :
    homDensity book123 W =
      ∫ a0, ∫ a1, W a0 a1 * pageWeightOp W (pathOp W) a0 a1 *
        pageOp W 0 a0 a1 ∂μ ∂μ := by
  have hm : Measurable (graphWeight book123 W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight book123 W x| ≤ 1 := fun x ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 5 → Ω ↦ graphWeight book123 W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω ↦ graphWeight book123 W (Fin.cons a0 (Fin.cons a1 y)))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  have hstep2 : ∀ a2 : Ω,
      (∫ y : Fin 3 → Ω,
          graphWeight book123 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)))
        ∂assignmentMeasure (Fin 3) μ) =
        (W a0 a1 * W a0 a2 * W a1 a2 * pathOp W a2) * pageOp W 0 a0 a1 := by
    intro a2
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 3 → Ω ↦
        graphWeight book123 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
      (hm.comp ((measurable_fin_cons a0).comp
        ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
      fun y ↦ hb _]
    have hstep3 : ∀ a3 : Ω,
        (∫ y : Fin 2 → Ω,
            graphWeight book123 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
          ∂assignmentMeasure (Fin 2) μ) =
          ((W a0 a1 * W a0 a2 * W a1 a2) * pathOp W a2) *
            (W a0 a3 * W a1 a3 * degree W a3 ^ (0 : ℝ)) := by
      intro a3
      rw [integral_assignmentMeasure_succ
        (fun y : Fin 2 → Ω ↦ graphWeight book123 W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
        (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
          ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
        fun y ↦ hb _]
      have hstep4 : ∀ a4 : Ω,
          (∫ y : Fin 1 → Ω, graphWeight book123 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                (Fin.cons a4 y)))))
            ∂assignmentMeasure (Fin 1) μ) =
            (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3) *
              (W a2 a4 * degree W a4) := by
        intro a4
        rw [integral_assignmentMeasure_succ
          (fun y : Fin 1 → Ω ↦ graphWeight book123 W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
              (Fin.cons a4 y))))))
          (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
            ((measurable_fin_cons a2).comp ((measurable_fin_cons a3).comp
              (measurable_fin_cons a4))))))
          fun y ↦ hb _]
        have hval : ∀ a5 : Ω,
            (∫ y : Fin 0 → Ω, graphWeight book123 W
                (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                  (Fin.cons a4 (Fin.cons a5 y))))))
              ∂assignmentMeasure (Fin 0) μ) =
              (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * W a2 a4) *
                W a4 a5 := by
          intro a5
          rw [show (∫ y : Fin 0 → Ω, graphWeight book123 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                (Fin.cons a4 (Fin.cons a5 y))))))
                ∂assignmentMeasure (Fin 0) μ) =
              W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * W a2 a4 *
                W a4 a5 by simp [graphWeight_book123_cons]]
        rw [integral_congr_ae (ae_of_all _ hval), integral_const_mul]
        show (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * W a2 a4) *
            degree W a4 =
          (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3) *
            (W a2 a4 * degree W a4)
        ring
      rw [integral_congr_ae (ae_of_all _ hstep4), Real.rpow_zero,
        integral_const_mul, ← pathOp]
      ring
    rw [integral_congr_ae (ae_of_all _ hstep3), integral_const_mul, ← pageOp]
  rw [integral_congr_ae (ae_of_all _ hstep2)]
  have hre : ∀ a2 : Ω,
      (W a0 a1 * W a0 a2 * W a1 a2 * pathOp W a2) * pageOp W 0 a0 a1 =
        (W a0 a1 * pageOp W 0 a0 a1) *
          (W a0 a2 * W a1 a2 * pathOp W a2) := by
    intro a2; ring
  rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul, ← pageWeightOp]
  ring

/-! ### Integrability of the three edge-weighted page integrands -/

section Integrability

variable (W : Graphon Ω μ)

lemma integrable_edge_prod : Integrable (fun q : Ω × Ω ↦ W q.1 q.2) (μ.prod μ) :=
  integrable_prod_of_bdd W.measurable (C := 1) fun q ↦ by
    rw [abs_of_nonneg (W.nonneg q.1 q.2)]
    exact W.le_one q.1 q.2

lemma integrable_edge_pageWeight_mul_pageOp :
    Integrable (fun q : Ω × Ω ↦ W q.1 q.2 *
      pageWeightOp W (pathOp W) q.1 q.2 * pageOp W 0 q.1 q.2) (μ.prod μ) := by
  have hG0 := pageWeightOp_nonneg W (pathOp_nonneg W)
  have hG1 := pageWeightOp_le_one W (measurable_pathOp W) (pathOp_nonneg W)
    (pathOp_le_one W)
  refine integrable_prod_of_bdd
    ((W.measurable.mul (measurable_pageWeightOp W (measurable_pathOp W))).mul
      (measurable_pageOp W le_rfl)) (C := 1) fun q ↦ ?_
  show |W q.1 q.2 * pageWeightOp W (pathOp W) q.1 q.2 *
    pageOp W 0 q.1 q.2| ≤ 1
  have h0 : 0 ≤ W q.1 q.2 * pageWeightOp W (pathOp W) q.1 q.2 *
      pageOp W 0 q.1 q.2 :=
    mul_nonneg (mul_nonneg (W.nonneg _ _) (hG0 _ _))
      (pageOp_nonneg W le_rfl _ _)
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (mul_le_one₀ (W.le_one _ _) (hG0 _ _) (hG1 _ _))
    (pageOp_nonneg W le_rfl _ _) (pageOp_le_one W le_rfl _ _)

lemma integrable_edge_pageSqrt_pow (j : ℕ) :
    Integrable (fun q : Ω × Ω ↦ W q.1 q.2 *
      pageWeightOp W (sqrtPathOp W) q.1 q.2 ^ j) (μ.prod μ) := by
  have hR0 := pageWeightOp_nonneg W (sqrtPathOp_nonneg W)
  have hR1 := pageWeightOp_le_one W (measurable_sqrtPathOp W)
    (sqrtPathOp_nonneg W) (sqrtPathOp_le_one W)
  refine integrable_prod_of_bdd
    (W.measurable.mul
      ((measurable_pageWeightOp W (measurable_sqrtPathOp W)).pow_const j))
    (C := 1) fun q ↦ ?_
  show |W q.1 q.2 * pageWeightOp W (sqrtPathOp W) q.1 q.2 ^ j| ≤ 1
  have h0 : 0 ≤ W q.1 q.2 * pageWeightOp W (sqrtPathOp W) q.1 q.2 ^ j :=
    mul_nonneg (W.nonneg _ _) (pow_nonneg (hR0 _ _) j)
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (W.le_one _ _) (pow_nonneg (hR0 _ _) j)
    (pow_le_one₀ (hR0 _ _) (hR1 _ _))

lemma integrable_edge_pageSqrt :
    Integrable (fun q : Ω × Ω ↦ W q.1 q.2 *
      pageWeightOp W (sqrtPathOp W) q.1 q.2) (μ.prod μ) := by
  refine (integrable_edge_pageSqrt_pow W 1).congr (ae_of_all _ fun q ↦ ?_)
  show W q.1 q.2 * pageWeightOp W (sqrtPathOp W) q.1 q.2 ^ 1 =
    W q.1 q.2 * pageWeightOp W (sqrtPathOp W) q.1 q.2
  rw [pow_one]

end Integrability

/-! ### The bound -/

/-- **Atlas 123 dominates its target.** -/
theorem book123_bound (W : Graphon Ω μ)
    (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 3 * (2 * cliqueDensity 2 W - 1) ^ 2 ≤
      homDensity book123 W := by
  set p := cliqueDensity 2 W with hpdef
  have hppos : (0 : ℝ) < p := by linarith
  have h2p : (0 : ℝ) ≤ 2 * p - 1 := by linarith
  -- the density on the product measure
  have hprod : homDensity book123 W =
      ∫ q, W q.1 q.2 * pageWeightOp W (pathOp W) q.1 q.2 *
        pageOp W 0 q.1 q.2 ∂(μ.prod μ) := by
    rw [homDensity_book123]
    exact integral_integral (integrable_edge_pageWeight_mul_pageOp W)
  -- split the `A`-page: `R² ≤ S·G`
  have hsplit : (∫ q, W q.1 q.2 *
      pageWeightOp W (sqrtPathOp W) q.1 q.2 ^ 2 ∂(μ.prod μ)) ≤
      ∫ q, W q.1 q.2 * pageWeightOp W (pathOp W) q.1 q.2 *
        pageOp W 0 q.1 q.2 ∂(μ.prod μ) := by
    refine integral_mono (integrable_edge_pageSqrt_pow W 2)
      (integrable_edge_pageWeight_mul_pageOp W) fun q ↦ ?_
    calc W q.1 q.2 * pageWeightOp W (sqrtPathOp W) q.1 q.2 ^ 2
        ≤ W q.1 q.2 * (pageOp W 0 q.1 q.2 *
            pageWeightOp W (pathOp W) q.1 q.2) :=
          mul_le_mul_of_nonneg_left (sq_pageWeightOp_sqrt_le W q.1 q.2)
            (W.nonneg _ _)
      _ = W q.1 q.2 * pageWeightOp W (pathOp W) q.1 q.2 *
            pageOp W 0 q.1 q.2 := by ring
  -- Cauchy--Schwarz on the product measure, with weight `W`
  have hcs := integral_mul_sq_le_integral_mul_integral_mul_sq
    (μ := μ.prod μ) (A := fun q : Ω × Ω ↦ W q.1 q.2)
    (η := fun q : Ω × Ω ↦ pageWeightOp W (sqrtPathOp W) q.1 q.2)
    (integrable_edge_prod W) (integrable_edge_pageSqrt W)
    (integrable_edge_pageSqrt_pow W 2) (fun q ↦ W.nonneg _ _)
  rw [integral_prod_edge, ← hpdef] at hcs
  -- the paired `√A`-page collapses to `∫√A·τ`
  have hR : (∫ q, W q.1 q.2 * pageWeightOp W (sqrtPathOp W) q.1 q.2
      ∂(μ.prod μ)) = ∫ z, sqrtPathOp W z * rootedTriangle W z ∂μ :=
    integral_edge_pageWeightOp W (measurable_sqrtPathOp W)
      (sqrtPathOp_nonneg W) (sqrtPathOp_le_one W)
  rw [hR] at hcs
  have hlow : p ^ 2 * (2 * p - 1) ≤
      ∫ z, sqrtPathOp W z * rootedTriangle W z ∂μ :=
    sqrt_weighted_rootedTriangle W hp
  have hlow0 : (0 : ℝ) ≤ p ^ 2 * (2 * p - 1) := by positivity
  have hsq : (p ^ 2 * (2 * p - 1)) ^ 2 ≤
      (∫ z, sqrtPathOp W z * rootedTriangle W z ∂μ) ^ 2 :=
    pow_le_pow_left₀ hlow0 hlow 2
  -- assemble, then divide by `p`
  rw [hprod]
  have hfinal : p * (p ^ 3 * (2 * p - 1) ^ 2) ≤
      p * ∫ q, W q.1 q.2 * pageWeightOp W (pathOp W) q.1 q.2 *
        pageOp W 0 q.1 q.2 ∂(μ.prod μ) := by
    nlinarith [hcs, hsq, hsplit, hppos]
  exact le_of_mul_le_mul_left hfinal hppos

/-! ### Chromatic data and the catalogue proposition -/

lemma affineProd_123 (z : ℝ) :
    affineProd [0, 1, 1, 1, 2, 2] z = z ^ 3 * (2 * z - 1) ^ 2 := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_cons, affineProd_nil]
  ring

/-- `K₃` on the spine and one page, the second page on the spine edge, then the
tail hung off the page `2`. -/
def iso123 :
    attachVertex (attachVertex
      (attachVertex (⊤ : SimpleGraph (Fin 3)) {0, 1}) {some 2}) {none} ≃g
      book123 where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom123 : IsChromaticPolynomial book123
    ((([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := book123) iso123
    (isClique_singleton _ none)
    (isChromaticPolynomial_attachVertex (isClique_singleton _ (some 2))
      (isChromaticPolynomial_attachVertex (isCliqueTop _)
        (isChromaticPolynomial_top 3)))
  rw [show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide,
    Finset.card_singleton, Finset.card_singleton] at h
  have hpoly :
      ((([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) * ((X - C ((1 : ℕ) : ℝ)) *
        ((X - C ((2 : ℕ) : ℝ)) * ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ)))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count123 (k : ℕ) :
    properAssignmentCount book123 k =
      (k - 1) * ((k - 1) * ((k - 2) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := book123) iso123
      (isClique_singleton _ none) k,
    properAssignmentCount_attachVertex (isClique_singleton _ (some 2)),
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide,
    Finset.card_singleton, Finset.card_singleton]

theorem num123 : IsChromaticNumber book123 3 where
  positive := by rw [count123]; decide
  zero_below k hk := by
    rw [count123, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero, Nat.mul_zero]

/-- **Atlas 123 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_123 : Taeyoung.SatisfiesLowerBound book123 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P =
      (([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := book123) hP chrom123
  have hreq : r = 3 := IsChromaticNumber.unique (H := book123) hr num123
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := book123_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 1, 2, 2] (by norm_num) hone,
      affineProd_123]
    exact hkey

end Taeyoung.Methods.PageTail
