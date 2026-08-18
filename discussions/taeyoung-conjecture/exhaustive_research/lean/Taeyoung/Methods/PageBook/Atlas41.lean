import Taeyoung.Methods.PageBook.Atlas114
import Taeyoung.Methods.Link.ConeChromatic

/-!
# Atlas 41: the two-page book with one leaf on one page

`P_{2;(1,0)}`: spine `u,v`, two pages `z₁,z₂`, one private leaf on `z₁`.  Here
`n = 1` and `m = 2`, so `α = n/m = 1/2` — this is where the real-exponent port
of `Methods/Link/WeightedGoodmanRpow.lean` is actually needed.

The chain is the one of `Atlas114.lean` with the exponents halved:

```
t = ∫∫ W·H₁·H₀ ≥ ∫∫ W·H_{1/2}²     (sq_pageOp_le at s = 1)
                ≥ (∫∫ W·H_{1/2})²/p (weighted Cauchy–Schwarz on μ×μ)
                = (∫ d^{1/2}·τ)²/p   (integral_edge_pageOp at s = 1/2)
                ≥ ((2p-1)p^{3/2})²/p (weighted_rootedTriangle_rpow at s = 1/2,
                                      rpow_le_momentR at 5/2)
                = p²(2p-1)² = Φ.
```

The chromatic tower and its relabelling are the ones already used for Atlas 40,
and the root list `[0,1,1,2,2]` already has its `affineProd` evaluated.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.PageBook

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PawCone Taeyoung.Methods.ForestCone
  Taeyoung.Methods.BaseCone Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The graph -/

/-- Spine `0,1`; pages `2,3`; one leaf `4` on page `3`. -/
def book41 : SimpleGraph (Fin 5) :=
  graphFromEdges 5 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (3, 4)]

instance : DecidableRel book41.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_book41 :
    book41.edgeFinset = {s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(3, 4)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_book41 (W : Graphon Ω μ) (x : Fin 5 → Ω) :
    graphWeight book41 W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 0) (x 3) * W (x 1) (x 2) *
        W (x 1) (x 3) * W (x 3) (x 4) := by
  rw [graphWeight, edgeFinset_book41]
  simp
  ring

lemma graphWeight_book41_cons (W : Graphon Ω μ) (a0 a1 a2 a3 a4 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight book41 W
        (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y))))) =
      W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a3 * W a3 a4 := by
  rw [graphWeight_book41]
  rfl

/-! ### The density identity -/

/-- **The density factors through the two page operators.** -/
theorem homDensity_book41 (W : Graphon Ω μ) :
    homDensity book41 W =
      ∫ a0, ∫ a1, W a0 a1 * pageOp W 0 a0 a1 * pageOp W 1 a0 a1 ∂μ ∂μ := by
  have hm : Measurable (graphWeight book41 W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight book41 W x| ≤ 1 := fun x ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω ↦ graphWeight book41 W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 3 → Ω ↦ graphWeight book41 W (Fin.cons a0 (Fin.cons a1 y)))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  have hstep2 : ∀ a2 : Ω,
      (∫ y : Fin 2 → Ω,
          graphWeight book41 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)))
        ∂assignmentMeasure (Fin 2) μ) =
        (W a0 a1 * W a0 a2 * W a1 a2) * pageOp W 1 a0 a1 := by
    intro a2
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 2 → Ω ↦
        graphWeight book41 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
      (hm.comp ((measurable_fin_cons a0).comp
        ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
      fun y ↦ hb _]
    have hstep3 : ∀ a3 : Ω,
        (∫ y : Fin 1 → Ω,
            graphWeight book41 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
          ∂assignmentMeasure (Fin 1) μ) =
          (W a0 a1 * W a0 a2 * W a1 a2) *
            (W a0 a3 * W a1 a3 * degree W a3 ^ (1 : ℝ)) := by
      intro a3
      rw [integral_assignmentMeasure_succ
        (fun y : Fin 1 → Ω ↦ graphWeight book41 W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
        (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
          ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
        fun y ↦ hb _]
      have hval : ∀ a4 : Ω,
          (∫ y : Fin 0 → Ω, graphWeight book41 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                (Fin.cons a4 y)))))
            ∂assignmentMeasure (Fin 0) μ) =
            ((W a0 a1 * W a0 a2 * W a1 a2) * (W a0 a3 * W a1 a3)) * W a3 a4 := by
        intro a4
        rw [show (∫ y : Fin 0 → Ω, graphWeight book41 W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
              (Fin.cons a4 y)))))
              ∂assignmentMeasure (Fin 0) μ) =
            W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a3 * W a3 a4 by
          simp [graphWeight_book41_cons]]
        ring
      rw [integral_congr_ae (ae_of_all _ hval), integral_const_mul,
        Real.rpow_one]
      show _ * degree W a3 = _
      ring
    rw [integral_congr_ae (ae_of_all _ hstep3)]
    rw [pageOp, ← integral_const_mul]
  rw [integral_congr_ae (ae_of_all _ hstep2)]
  have hpull2 : (∫ a2, (W a0 a1 * W a0 a2 * W a1 a2) * pageOp W 1 a0 a1 ∂μ) =
      W a0 a1 * pageOp W 0 a0 a1 * pageOp W 1 a0 a1 := by
    have hre : ∀ a2 : Ω, (W a0 a1 * W a0 a2 * W a1 a2) * pageOp W 1 a0 a1 =
        (W a0 a1 * pageOp W 1 a0 a1) *
          (W a0 a2 * W a1 a2 * degree W a2 ^ (0 : ℝ)) := by
      intro a2
      rw [Real.rpow_zero]
      ring
    rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul, ← pageOp]
    ring
  exact hpull2

/-! ### The bound -/

/-- **Atlas 41 dominates its target.** -/
theorem book41_bound (W : Graphon Ω μ) (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 2 * (2 * cliqueDensity 2 W - 1) ^ 2 ≤
      homDensity book41 W := by
  set p := cliqueDensity 2 W with hpdef
  have hppos : (0 : ℝ) < p := by linarith
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hprod : homDensity book41 W =
      ∫ q, W q.1 q.2 * pageOp W 0 q.1 q.2 * pageOp W 1 q.1 q.2 ∂(μ.prod μ) := by
    rw [homDensity_book41]
    exact integral_integral (integrable_edge_pageOp_mul W le_rfl zero_le_one)
  -- compress the two pages
  have hmono : (∫ q, W q.1 q.2 * pageOp W (1 / 2) q.1 q.2 ^ 2 ∂(μ.prod μ)) ≤
      ∫ q, W q.1 q.2 * pageOp W 0 q.1 q.2 * pageOp W 1 q.1 q.2 ∂(μ.prod μ) := by
    have hint1 : Integrable (fun q : Ω × Ω ↦
        W q.1 q.2 * pageOp W (1 / 2) q.1 q.2 ^ 2) (μ.prod μ) := by
      refine (integrable_edge_pageOp_mul W (s := 1 / 2) (t := 1 / 2) hhalf
        hhalf).congr (ae_of_all _ fun q ↦ ?_)
      simp only []
      ring
    refine integral_mono hint1
      (integrable_edge_pageOp_mul W le_rfl zero_le_one) fun q ↦ ?_
    have hcs := sq_pageOp_le W (s := 1) zero_le_one q.1 q.2
    calc W q.1 q.2 * pageOp W (1 / 2) q.1 q.2 ^ 2
        ≤ W q.1 q.2 * (pageOp W 0 q.1 q.2 * pageOp W 1 q.1 q.2) :=
          mul_le_mul_of_nonneg_left hcs (W.nonneg _ _)
      _ = W q.1 q.2 * pageOp W 0 q.1 q.2 * pageOp W 1 q.1 q.2 := by ring
  -- Cauchy--Schwarz on the product
  have hcs2 := integral_mul_sq_le_integral_mul_integral_mul_sq
    (μ := μ.prod μ) (A := fun q : Ω × Ω ↦ W q.1 q.2)
    (η := fun q : Ω × Ω ↦ pageOp W (1 / 2) q.1 q.2)
    (integrable_prod_of_bdd W.measurable (C := 1) fun q ↦ by
      show |W q.1 q.2| ≤ 1
      rw [abs_of_nonneg (W.nonneg q.1 q.2)]; exact W.le_one q.1 q.2)
    (integrable_edge_pageOp W hhalf)
    (by
      refine (integrable_edge_pageOp_mul W (s := 1 / 2) (t := 1 / 2) hhalf
        hhalf).congr (ae_of_all _ fun q ↦ ?_)
      simp only []
      ring)
    fun q ↦ W.nonneg _ _
  rw [integral_prod_edge] at hcs2
  have hA : (∫ q, W q.1 q.2 * pageOp W (1 / 2) q.1 q.2 ∂(μ.prod μ)) =
      ∫ z, degree W z ^ (1 / 2 : ℝ) * rootedTriangle W z ∂μ :=
    integral_edge_pageOp W hhalf
  rw [hA] at hcs2
  -- the real-exponent weighted rooted-triangle inequality and Jensen
  have hwrt : (2 * p - 1) * momentR W (1 / 2 + 2) ≤
      p * ∫ z, degree W z ^ (1 / 2 : ℝ) * rootedTriangle W z ∂μ := by
    have h := weighted_rootedTriangle_rpow (W := W) hhalf
    rwa [← hpdef] at h
  have hmom : p ^ ((5 : ℝ) / 2) ≤ momentR W (1 / 2 + 2) := by
    have h := rpow_le_momentR (W := W) (s := (5 : ℝ) / 2) (by norm_num)
    rw [← hpdef] at h
    rwa [show (1 : ℝ) / 2 + 2 = (5 : ℝ) / 2 by norm_num]
  have h2p : (0 : ℝ) ≤ 2 * p - 1 := by linarith
  have hq : (2 * p - 1) * p ^ ((5 : ℝ) / 2) ≤
      p * ∫ z, degree W z ^ (1 / 2 : ℝ) * rootedTriangle W z ∂μ :=
    le_trans (mul_le_mul_of_nonneg_left hmom h2p) hwrt
  have h52 : (p ^ ((5 : ℝ) / 2)) ^ (2 : ℕ) = p ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast (p ^ ((5 : ℝ) / 2)) 2, ← Real.rpow_mul hppos.le,
      show (5 : ℝ) / 2 * (2 : ℕ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hqnn : 0 ≤ (2 * p - 1) * p ^ ((5 : ℝ) / 2) :=
    mul_nonneg h2p (Real.rpow_nonneg hppos.le _)
  have hsq := pow_le_pow_left₀ hqnn hq 2
  rw [mul_pow, h52] at hsq
  -- assemble
  rw [hprod]
  refine le_trans ?_ hmono
  have hfin : p ^ 3 * (p ^ 2 * (2 * p - 1) ^ 2) ≤
      p ^ 3 * ∫ q, W q.1 q.2 * pageOp W (1 / 2) q.1 q.2 ^ 2 ∂(μ.prod μ) := by
    nlinarith [hcs2, hsq, hppos]
  exact le_of_mul_le_mul_left hfin (by positivity)

/-! ### Chromatic data and the catalogue proposition -/

def iso41 :
    attachVertex (attachVertex (⊤ : SimpleGraph (Fin 3)) {0, 1}) {none} ≃g
      book41 where
  toEquiv := equiv40
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom41 : IsChromaticPolynomial book41
    ((([0, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := book41) iso41
    (isClique_singleton _ none)
    (isChromaticPolynomial_attachVertex (isCliqueTop _)
      (isChromaticPolynomial_top 3))
  rw [show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide,
    Finset.card_singleton] at h
  have hpoly : ((([0, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) *
        ((X - C ((2 : ℕ) : ℝ)) * ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count41' (k : ℕ) :
    properAssignmentCount book41 k = (k - 1) * ((k - 2) * k.descFactorial 3) := by
  rw [properAssignmentCount_of_attachIso (H' := book41) iso41
      (isClique_singleton _ none) k,
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide, Finset.card_singleton]

theorem num41' : IsChromaticNumber book41 3 where
  positive := by rw [count41']; decide
  zero_below k hk := by
    rw [count41', Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero]

/-- **Atlas 41 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_41' : Taeyoung.SatisfiesLowerBound book41 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = (([0, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := book41) hP chrom41
  have hreq : r = 3 := IsChromaticNumber.unique (H := book41) hr num41'
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := book41_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 5) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 2, 2] (by norm_num) hone,
      affineProd_01122]
    exact hkey

/-! ### Atlas 193, the cone over Atlas 41

The chromatic polynomial comes from `isChromaticPolynomial_coneGraph` rather
than an attachment tower — `χ_{K₁∨F}(x) = x·χ_F(x-1)` shifts every root by one,
which is exactly the list operation `satisfiesLowerBound_of_baseCone` expects. -/

theorem chrom193 : IsChromaticPolynomial (coneGraph book41)
    ((((0 : ℝ) :: ([0, 1, 1, 2, 2] : List ℝ).map (· + 1)).map fun k ↦
      (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_coneGraph book41 chrom41
  rw [show ((0 : ℝ) :: ([0, 1, 1, 2, 2] : List ℝ).map (· + 1)) =
    [0, 1, 2, 2, 3, 3] from by norm_num]
  have hpoly : (([0, 1, 2, 2, 3, 3] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod =
      X * ((([0, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod).comp
        (X - 1) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    simp only [mul_comp, sub_comp, X_comp, C_comp, one_comp]
    simp only [map_zero, map_one, map_ofNat, sub_zero, mul_one]
    ring
  rw [hpoly]
  exact h

/-- **Atlas 193 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_193 :
    Taeyoung.SatisfiesLowerBound (coneGraph book41) :=
  satisfiesLowerBound_of_baseCone (h := 3) book41 [0, 1, 1, 2, 2]
    (kmax := 2) (r := 4) rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) chrom193 (isChromaticNumber_coneGraph book41 num41')
    (by norm_num)
    (fun V hz ↦ by
      rw [affineProd_01122]
      refine book41_bound V ?_
      norm_num at hz ⊢
      linarith)

end Taeyoung.Methods.PageBook
