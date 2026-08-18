import Taeyoung.Methods.Link.PageOp
import Taeyoung.Methods.ForestCone.Rows

/-!
# Atlas 114: the two-page book with two leaves on one page

`P_{2;(2,0)}` in the notation of `notes/page_rooted_triangle_book_leaves.tex`:
spine `u,v`, two pages `z₁,z₂` adjacent to both, and two private leaves on
`z₁`.  Here `n = 2` and `m = 2`, so `α = n/m = 1` — this is the one scoped row
of that family whose exponent is an integer, and it therefore needs neither the
real-exponent port nor a genuine Hölder.

The chain is

```
t = ∫∫ W·H₂·H₀ ≥ ∫∫ W·H₁²      (sq_pageOp_le at s = 2)
                ≥ (∫∫ W·H₁)²/p  (weighted Cauchy–Schwarz on μ×μ, weight W)
                = (∫ d·τ)²/p     (integral_edge_pageOp at s = 1)
                ≥ ((2p-1)p²)²/p  (weighted_rootedTriangle at h = 1, and Jensen)
                = p³(2p-1)² = Φ.
```

Both Cauchy–Schwarz steps are the same lemma,
`integral_mul_sq_le_integral_mul_integral_mul_sq`, once with weight
`W(x,·)W(y,·)` on `μ` and once with weight `W` on `μ ⊗ μ`.

The vertex labelling is chosen so that coordinate peeling — which always removes
coordinate `0` — meets the leaves first and the spine last.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.PageBook

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PawCone Taeyoung.Methods.ForestCone
  Taeyoung.Methods.BaseCone Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The graph -/

/-- Spine `0,1`; pages `2,3`; leaves `4,5` on page `3`. -/
def book114 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (3, 4), (3, 5)]

instance : DecidableRel book114.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_book114 :
    book114.edgeFinset =
      {s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(3, 4), s(3, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_book114 (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight book114 W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 0) (x 3) * W (x 1) (x 2) *
        W (x 1) (x 3) * W (x 3) (x 4) * W (x 3) (x 5) := by
  rw [graphWeight, edgeFinset_book114]
  simp
  ring

lemma graphWeight_book114_cons (W : Graphon Ω μ) (a0 a1 a2 a3 a4 a5 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight book114 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
        (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y)))))) =
      W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a3 * W a3 a4 * W a3 a5 := by
  rw [graphWeight_book114]
  rfl

/-! ### The density identity -/

private lemma rpow_two_degree (W : Graphon Ω μ) (z : Ω) :
    degree W z ^ (2 : ℝ) = degree W z * degree W z := by
  rw [Real.rpow_two, sq]

/-- **The density factors through the two page operators.** -/
theorem homDensity_book114 (W : Graphon Ω μ) :
    homDensity book114 W =
      ∫ a0, ∫ a1, W a0 a1 * pageOp W 0 a0 a1 * pageOp W 2 a0 a1 ∂μ ∂μ := by
  have hm : Measurable (graphWeight book114 W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight book114 W x| ≤ 1 := fun x ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 5 → Ω ↦ graphWeight book114 W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω ↦ graphWeight book114 W (Fin.cons a0 (Fin.cons a1 y)))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  -- the page `a2` contributes `H₀`
  have hstep2 : ∀ a2 : Ω,
      (∫ y : Fin 3 → Ω,
          graphWeight book114 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)))
        ∂assignmentMeasure (Fin 3) μ) =
        (W a0 a1 * W a0 a2 * W a1 a2) * pageOp W 2 a0 a1 := by
    intro a2
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 3 → Ω ↦
        graphWeight book114 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
      (hm.comp ((measurable_fin_cons a0).comp
        ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
      fun y ↦ hb _]
    -- the page `a3` contributes `H₂`, after its two leaves become `d(a3)²`
    have hstep3 : ∀ a3 : Ω,
        (∫ y : Fin 2 → Ω,
            graphWeight book114 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
          ∂assignmentMeasure (Fin 2) μ) =
          (W a0 a1 * W a0 a2 * W a1 a2) *
            (W a0 a3 * W a1 a3 * degree W a3 ^ (2 : ℝ)) := by
      intro a3
      rw [integral_assignmentMeasure_succ
        (fun y : Fin 2 → Ω ↦ graphWeight book114 W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
        (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
          ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
        fun y ↦ hb _]
      have hstep4 : ∀ a4 : Ω,
          (∫ y : Fin 1 → Ω,
              graphWeight book114 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
                (Fin.cons a3 (Fin.cons a4 y)))))
            ∂assignmentMeasure (Fin 1) μ) =
            (W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a3 * W a3 a4) *
              degree W a3 := by
        intro a4
        rw [integral_assignmentMeasure_succ
          (fun y : Fin 1 → Ω ↦ graphWeight book114 W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
              (Fin.cons a3 (Fin.cons a4 y))))))
          (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
            ((measurable_fin_cons a2).comp ((measurable_fin_cons a3).comp
              (measurable_fin_cons a4))))))
          fun y ↦ hb _]
        have hval : ∀ a5 : Ω,
            (∫ y : Fin 0 → Ω, graphWeight book114 W
                (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                  (Fin.cons a4 (Fin.cons a5 y))))))
              ∂assignmentMeasure (Fin 0) μ) =
              (W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a3 * W a3 a4) *
                W a3 a5 := by
          intro a5
          rw [show (∫ y : Fin 0 → Ω, graphWeight book114 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                (Fin.cons a4 (Fin.cons a5 y))))))
                ∂assignmentMeasure (Fin 0) μ) =
              W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a3 * W a3 a4 *
                W a3 a5 by simp [graphWeight_book114_cons]]
        rw [integral_congr_ae (ae_of_all _ hval), integral_const_mul]
        rfl
      rw [integral_congr_ae (ae_of_all _ hstep4)]
      have hpull : (∫ a4, (W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a3 *
          W a3 a4) * degree W a3 ∂μ) =
            (W a0 a1 * W a0 a2 * W a1 a2) *
              (W a0 a3 * W a1 a3 * (degree W a3 * degree W a3)) := by
        have hre : ∀ a4 : Ω, (W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a3 *
            W a3 a4) * degree W a3 =
              ((W a0 a1 * W a0 a2 * W a1 a2) *
                (W a0 a3 * W a1 a3 * degree W a3)) * W a3 a4 := by
          intro a4; ring
        rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
        show _ * degree W a3 = _
        ring
      rw [hpull, rpow_two_degree]
    rw [integral_congr_ae (ae_of_all _ hstep3)]
    rw [pageOp, ← integral_const_mul]
  rw [integral_congr_ae (ae_of_all _ hstep2)]
  have hpull2 : (∫ a2, (W a0 a1 * W a0 a2 * W a1 a2) * pageOp W 2 a0 a1 ∂μ) =
      W a0 a1 * pageOp W 0 a0 a1 * pageOp W 2 a0 a1 := by
    have hre : ∀ a2 : Ω, (W a0 a1 * W a0 a2 * W a1 a2) * pageOp W 2 a0 a1 =
        (W a0 a1 * pageOp W 2 a0 a1) * (W a0 a2 * W a1 a2 * degree W a2 ^ (0 : ℝ)) := by
      intro a2
      rw [Real.rpow_zero]
      ring
    rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul, ← pageOp]
    ring
  exact hpull2

/-! ### The bound -/

lemma integrable_edge_pageOp (W : Graphon Ω μ) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun q : Ω × Ω ↦ W q.1 q.2 * pageOp W s q.1 q.2) (μ.prod μ) := by
  refine integrable_prod_of_bdd (W.measurable.mul (measurable_pageOp W hs))
    (C := 1) fun q ↦ ?_
  show |W q.1 q.2 * pageOp W s q.1 q.2| ≤ 1
  have h0 : 0 ≤ W q.1 q.2 * pageOp W s q.1 q.2 :=
    mul_nonneg (W.nonneg _ _) (pageOp_nonneg W hs _ _)
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (W.le_one _ _) (pageOp_nonneg W hs _ _) (pageOp_le_one W hs _ _)

lemma integrable_edge_pageOp_mul (W : Graphon Ω μ) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * pageOp W s q.1 q.2 * pageOp W t q.1 q.2) (μ.prod μ) := by
  refine integrable_prod_of_bdd ((W.measurable.mul (measurable_pageOp W hs)).mul
    (measurable_pageOp W ht)) (C := 1) fun q ↦ ?_
  show |W q.1 q.2 * pageOp W s q.1 q.2 * pageOp W t q.1 q.2| ≤ 1
  have h0 : 0 ≤ W q.1 q.2 * pageOp W s q.1 q.2 * pageOp W t q.1 q.2 :=
    mul_nonneg (mul_nonneg (W.nonneg _ _) (pageOp_nonneg W hs _ _))
      (pageOp_nonneg W ht _ _)
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (mul_le_one₀ (W.le_one _ _) (pageOp_nonneg W hs _ _)
    (pageOp_le_one W hs _ _)) (pageOp_nonneg W ht _ _) (pageOp_le_one W ht _ _)

/-- **Atlas 114 dominates its target.** -/
theorem book114_bound (W : Graphon Ω μ) (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 3 * (2 * cliqueDensity 2 W - 1) ^ 2 ≤
      homDensity book114 W := by
  set p := cliqueDensity 2 W with hpdef
  have hppos : (0 : ℝ) < p := by linarith
  -- move the density onto the product measure
  have hprod : homDensity book114 W =
      ∫ q, W q.1 q.2 * pageOp W 0 q.1 q.2 * pageOp W 2 q.1 q.2 ∂(μ.prod μ) := by
    rw [homDensity_book114]
    exact integral_integral (integrable_edge_pageOp_mul W le_rfl (by norm_num))
  -- compress the two pages to one
  have hmono : (∫ q, W q.1 q.2 * pageOp W 1 q.1 q.2 ^ 2 ∂(μ.prod μ)) ≤
      ∫ q, W q.1 q.2 * pageOp W 0 q.1 q.2 * pageOp W 2 q.1 q.2 ∂(μ.prod μ) := by
    have hint1 : Integrable (fun q : Ω × Ω ↦
        W q.1 q.2 * pageOp W 1 q.1 q.2 ^ 2) (μ.prod μ) := by
      refine (integrable_edge_pageOp_mul W (s := 1) (t := 1) zero_le_one zero_le_one).congr
        (ae_of_all _ fun q ↦ ?_)
      simp only []
      ring
    refine integral_mono hint1
      (integrable_edge_pageOp_mul W le_rfl (by norm_num)) fun q ↦ ?_
    have hcs := sq_pageOp_le W (s := 2) (by norm_num) q.1 q.2
    norm_num at hcs
    calc W q.1 q.2 * pageOp W 1 q.1 q.2 ^ 2
        ≤ W q.1 q.2 * (pageOp W 0 q.1 q.2 * pageOp W 2 q.1 q.2) :=
          mul_le_mul_of_nonneg_left hcs (W.nonneg _ _)
      _ = W q.1 q.2 * pageOp W 0 q.1 q.2 * pageOp W 2 q.1 q.2 := by ring
  -- Cauchy--Schwarz on the product, with weight `W`
  have hcs2 := integral_mul_sq_le_integral_mul_integral_mul_sq
    (μ := μ.prod μ) (A := fun q : Ω × Ω ↦ W q.1 q.2)
    (η := fun q : Ω × Ω ↦ pageOp W 1 q.1 q.2)
    (integrable_prod_of_bdd W.measurable (C := 1) fun q ↦ by
      rw [abs_of_nonneg (W.nonneg q.1 q.2)]; exact W.le_one q.1 q.2)
    (integrable_edge_pageOp W (s := 1) zero_le_one)
    (by
      refine (integrable_edge_pageOp_mul W (s := 1) (t := 1) zero_le_one zero_le_one).congr
        (ae_of_all _ fun q ↦ ?_)
      simp only []
      ring)
    fun q ↦ W.nonneg _ _
  rw [integral_prod_edge] at hcs2
  -- the paired page collapses to the rooted triangle
  have hA : (∫ q, W q.1 q.2 * pageOp W 1 q.1 q.2 ∂(μ.prod μ)) =
      ∫ z, degree W z * rootedTriangle W z ∂μ := by
    rw [integral_edge_pageOp W (s := 1) zero_le_one]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    simp only []
    rw [Real.rpow_one]
  rw [hA] at hcs2
  -- the weighted rooted-triangle inequality and Jensen
  have hwrt : (2 * p - 1) * moment W 3 ≤
      p * ∫ z, degree W z * rootedTriangle W z ∂μ := by
    have h := weighted_rootedTriangle (W := W) 1
    rw [← hpdef] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    simp only []
    rw [pow_one]
  have hmom : p ^ 3 ≤ moment W 3 := by
    have := RootedTriangleTree.pow_le_moment W 3
    rwa [← hpdef] at this
  have hAlow : (2 * p - 1) * p ^ 2 ≤ ∫ z, degree W z * rootedTriangle W z ∂μ := by
    have h1 : (2 * p - 1) * p ^ 3 ≤ p * ∫ z, degree W z * rootedTriangle W z ∂μ :=
      le_trans (mul_le_mul_of_nonneg_left hmom (by linarith)) hwrt
    nlinarith [h1]
  have hAnn : 0 ≤ ∫ z, degree W z * rootedTriangle W z ∂μ :=
    integral_nonneg fun z ↦
      mul_nonneg (degree_nonneg W z) (rootedTriangle_nonneg W z)
  -- assemble
  rw [hprod]
  refine le_trans ?_ hmono
  have h2p : (0 : ℝ) ≤ 2 * p - 1 := by linarith
  have hAsq : ((2 * p - 1) * p ^ 2) ^ 2 ≤
      (∫ z, degree W z * rootedTriangle W z ∂μ) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg h2p (sq_nonneg p)) hAlow 2
  have hmul : p * (p ^ 3 * (2 * p - 1) ^ 2) ≤
      p * ∫ q, W q.1 q.2 * pageOp W 1 q.1 q.2 ^ 2 ∂(μ.prod μ) := by
    nlinarith [hcs2, hAsq]
  exact le_of_mul_le_mul_left hmul hppos

/-! ### Chromatic data and the catalogue proposition -/

lemma affineProd_114 (z : ℝ) :
    affineProd [0, 1, 1, 1, 2, 2] z = z ^ 3 * (2 * z - 1) ^ 2 := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_cons, affineProd_nil]
  ring

/-- `K₃` on the spine and one page, then the other page on the spine edge, then
its two leaves. -/
def iso114 :
    attachVertex (attachVertex
      (attachVertex (⊤ : SimpleGraph (Fin 3)) {0, 1}) {none}) {some none} ≃g
      book114 where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom114 : IsChromaticPolynomial book114
    ((([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := book114) iso114
    (isClique_singleton _ (some none))
    (isChromaticPolynomial_attachVertex (isClique_singleton _ none)
      (isChromaticPolynomial_attachVertex (isCliqueTop _)
        (isChromaticPolynomial_top 3)))
  rw [show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide,
    Finset.card_singleton, Finset.card_singleton] at h
  have hpoly : ((([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) * ((X - C ((1 : ℕ) : ℝ)) *
        ((X - C ((2 : ℕ) : ℝ)) * ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ)))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count114 (k : ℕ) :
    properAssignmentCount book114 k =
      (k - 1) * ((k - 1) * ((k - 2) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := book114) iso114
      (isClique_singleton _ (some none)) k,
    properAssignmentCount_attachVertex (isClique_singleton _ none),
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide,
    Finset.card_singleton, Finset.card_singleton]

theorem num114 : IsChromaticNumber book114 3 where
  positive := by rw [count114]; decide
  zero_below k hk := by
    rw [count114, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero, Nat.mul_zero]

/-- **Atlas 114 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_114 : Taeyoung.SatisfiesLowerBound book114 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = (([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := book114) hP chrom114
  have hreq : r = 3 := IsChromaticNumber.unique (H := book114) hr num114
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := book114_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 1, 2, 2] (by norm_num) hone,
      affineProd_114]
    exact hkey

end Taeyoung.Methods.PageBook
