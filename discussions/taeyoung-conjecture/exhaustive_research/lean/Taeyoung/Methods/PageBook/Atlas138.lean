import Taeyoung.Methods.PageBook.Atlas41

/-!
# Atlas 138: the three-page book with one leaf

`P_{3;(1,0,0)}`: spine `u,v`, three pages, one private leaf on the first.  Here
`n = 1` and `m = 3`, so `α = 1/3` — the only scoped row of this family with
three pages, and therefore the only one needing a three-factor compression
rather than a single Cauchy–Schwarz.

Both compressions are still built out of the same weighted Cauchy–Schwarz,
applied twice at staggered exponents:

* on the page variable, `cube_pageOp_le : H_{1/3}³ ≤ H₀²·H₁`;
* on the spine, `(∫∫W·H)³ ≤ (∫∫W)²·(∫∫W·H³)`, from
  `(∫WH)² ≤ (∫W)(∫WH²)` and `(∫WH²)² ≤ (∫WH)(∫WH³)`.

so no genuine Hölder is needed anywhere in this family after all.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.PageBook

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PawCone Taeyoung.Methods.ForestCone
  Taeyoung.Methods.BaseCone Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The graph -/

/-- Spine `0,1`; pages `2,3,4`; one leaf `5` on page `4`. -/
def book138 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (4, 5)]

instance : DecidableRel book138.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_book138 :
    book138.edgeFinset =
      {s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(1, 2), s(1, 3), s(1, 4), s(4, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_book138 (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight book138 W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 0) (x 3) * W (x 0) (x 4) *
        W (x 1) (x 2) * W (x 1) (x 3) * W (x 1) (x 4) * W (x 4) (x 5) := by
  rw [graphWeight, edgeFinset_book138]
  simp
  ring

lemma graphWeight_book138_cons (W : Graphon Ω μ) (a0 a1 a2 a3 a4 a5 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight book138 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
        (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y)))))) =
      W a0 a1 * W a0 a2 * W a0 a3 * W a0 a4 * W a1 a2 * W a1 a3 * W a1 a4 *
        W a4 a5 := by
  rw [graphWeight_book138]
  rfl

/-! ### The density identity -/

/-- **The density factors through the three page operators.** -/
theorem homDensity_book138 (W : Graphon Ω μ) :
    homDensity book138 W =
      ∫ a0, ∫ a1, W a0 a1 * pageOp W 0 a0 a1 * pageOp W 0 a0 a1 *
        pageOp W 1 a0 a1 ∂μ ∂μ := by
  have hm : Measurable (graphWeight book138 W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight book138 W x| ≤ 1 := fun x ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 5 → Ω ↦ graphWeight book138 W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω ↦ graphWeight book138 W (Fin.cons a0 (Fin.cons a1 y)))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  have hstep2 : ∀ a2 : Ω,
      (∫ y : Fin 3 → Ω,
          graphWeight book138 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)))
        ∂assignmentMeasure (Fin 3) μ) =
        (W a0 a1 * (W a0 a2 * W a1 a2)) *
          (pageOp W 0 a0 a1 * pageOp W 1 a0 a1) := by
    intro a2
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 3 → Ω ↦
        graphWeight book138 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
      (hm.comp ((measurable_fin_cons a0).comp
        ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
      fun y ↦ hb _]
    have hstep3 : ∀ a3 : Ω,
        (∫ y : Fin 2 → Ω,
            graphWeight book138 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
          ∂assignmentMeasure (Fin 2) μ) =
          (W a0 a1 * (W a0 a2 * W a1 a2) * pageOp W 1 a0 a1) *
            (W a0 a3 * W a1 a3 * degree W a3 ^ (0 : ℝ)) := by
      intro a3
      rw [integral_assignmentMeasure_succ
        (fun y : Fin 2 → Ω ↦ graphWeight book138 W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
        (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
          ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
        fun y ↦ hb _]
      have hstep4 : ∀ a4 : Ω,
          (∫ y : Fin 1 → Ω,
              graphWeight book138 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
                (Fin.cons a3 (Fin.cons a4 y)))))
            ∂assignmentMeasure (Fin 1) μ) =
            (W a0 a1 * (W a0 a2 * W a1 a2) * (W a0 a3 * W a1 a3)) *
              (W a0 a4 * W a1 a4 * degree W a4 ^ (1 : ℝ)) := by
        intro a4
        rw [integral_assignmentMeasure_succ
          (fun y : Fin 1 → Ω ↦ graphWeight book138 W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
              (Fin.cons a3 (Fin.cons a4 y))))))
          (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
            ((measurable_fin_cons a2).comp ((measurable_fin_cons a3).comp
              (measurable_fin_cons a4))))))
          fun y ↦ hb _]
        have hval : ∀ a5 : Ω,
            (∫ y : Fin 0 → Ω, graphWeight book138 W
                (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                  (Fin.cons a4 (Fin.cons a5 y))))))
              ∂assignmentMeasure (Fin 0) μ) =
              ((W a0 a1 * (W a0 a2 * W a1 a2) * (W a0 a3 * W a1 a3)) *
                (W a0 a4 * W a1 a4)) * W a4 a5 := by
          intro a5
          rw [show (∫ y : Fin 0 → Ω, graphWeight book138 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                (Fin.cons a4 (Fin.cons a5 y))))))
                ∂assignmentMeasure (Fin 0) μ) =
              W a0 a1 * W a0 a2 * W a0 a3 * W a0 a4 * W a1 a2 * W a1 a3 *
                W a1 a4 * W a4 a5 by simp [graphWeight_book138_cons]]
          ring
        rw [integral_congr_ae (ae_of_all _ hval), integral_const_mul,
          Real.rpow_one]
        show _ * degree W a4 = _
        ring
      rw [integral_congr_ae (ae_of_all _ hstep4), integral_const_mul, ← pageOp,
        Real.rpow_zero]
      ring
    rw [integral_congr_ae (ae_of_all _ hstep3), integral_const_mul, ← pageOp]
    ring
  rw [integral_congr_ae (ae_of_all _ hstep2)]
  have hre : ∀ a2 : Ω,
      (W a0 a1 * (W a0 a2 * W a1 a2)) *
        (pageOp W 0 a0 a1 * pageOp W 1 a0 a1) =
      (W a0 a1 * (pageOp W 0 a0 a1 * pageOp W 1 a0 a1)) *
        (W a0 a2 * W a1 a2 * degree W a2 ^ (0 : ℝ)) := by
    intro a2
    rw [Real.rpow_zero]
    ring
  rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul, ← pageOp]
  ring

/-! ### The bound -/

/-- **Atlas 138 dominates its target.** -/
theorem book138_bound (W : Graphon Ω μ) (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 2 * (2 * cliqueDensity 2 W - 1) ^ 3 ≤
      homDensity book138 W := by
  set p := cliqueDensity 2 W with hpdef
  have hppos : (0 : ℝ) < p := by linarith
  have hthird : (0 : ℝ) ≤ 1 / 3 := by norm_num
  have hWi : Integrable (fun q : Ω × Ω ↦ W q.1 q.2) (μ.prod μ) :=
    integrable_prod_of_bdd W.measurable (C := 1) fun q ↦ by
      show |W q.1 q.2| ≤ 1
      rw [abs_of_nonneg (W.nonneg q.1 q.2)]; exact W.le_one q.1 q.2
  -- the density, on the product measure
  have hintRHS : Integrable (fun q : Ω × Ω ↦ W q.1 q.2 * pageOp W 0 q.1 q.2 *
      pageOp W 0 q.1 q.2 * pageOp W 1 q.1 q.2) (μ.prod μ) := by
    refine integrable_prod_of_bdd (((W.measurable.mul
      (measurable_pageOp W (le_refl (0:ℝ)))).mul
      (measurable_pageOp W (le_refl (0:ℝ)))).mul
      (measurable_pageOp W zero_le_one)) (C := 1) fun q ↦ ?_
    show |W q.1 q.2 * pageOp W 0 q.1 q.2 * pageOp W 0 q.1 q.2 *
      pageOp W 1 q.1 q.2| ≤ 1
    have h0 : 0 ≤ W q.1 q.2 * pageOp W 0 q.1 q.2 * pageOp W 0 q.1 q.2 *
        pageOp W 1 q.1 q.2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (W.nonneg _ _)
        (pageOp_nonneg W le_rfl _ _)) (pageOp_nonneg W le_rfl _ _))
        (pageOp_nonneg W zero_le_one _ _)
    rw [abs_of_nonneg h0]
    exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (W.le_one _ _)
      (pageOp_nonneg W le_rfl _ _) (pageOp_le_one W le_rfl _ _))
      (pageOp_nonneg W le_rfl _ _) (pageOp_le_one W le_rfl _ _))
      (pageOp_nonneg W zero_le_one _ _) (pageOp_le_one W zero_le_one _ _)
  have hprod : homDensity book138 W =
      ∫ q, W q.1 q.2 * pageOp W 0 q.1 q.2 * pageOp W 0 q.1 q.2 *
        pageOp W 1 q.1 q.2 ∂(μ.prod μ) := by
    rw [homDensity_book138]
    exact integral_integral hintRHS
  -- the integrability of the three powers of `H_{1/3}` against `W`
  have hint : ∀ n : ℕ, Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * pageOp W (1 / 3) q.1 q.2 ^ n) (μ.prod μ) := by
    intro n
    refine integrable_prod_of_bdd (W.measurable.mul
      ((measurable_pageOp W hthird).pow_const n)) (C := 1) fun q ↦ ?_
    show |W q.1 q.2 * pageOp W (1 / 3) q.1 q.2 ^ n| ≤ 1
    have h0 : 0 ≤ W q.1 q.2 * pageOp W (1 / 3) q.1 q.2 ^ n :=
      mul_nonneg (W.nonneg _ _) (pow_nonneg (pageOp_nonneg W hthird _ _) n)
    rw [abs_of_nonneg h0]
    exact mul_le_one₀ (W.le_one _ _) (pow_nonneg (pageOp_nonneg W hthird _ _) n)
      (pow_le_one₀ (pageOp_nonneg W hthird _ _) (pageOp_le_one W hthird _ _))
  -- compress the three pages
  have hmono : (∫ q, W q.1 q.2 * pageOp W (1 / 3) q.1 q.2 ^ 3 ∂(μ.prod μ)) ≤
      ∫ q, W q.1 q.2 * pageOp W 0 q.1 q.2 * pageOp W 0 q.1 q.2 *
        pageOp W 1 q.1 q.2 ∂(μ.prod μ) := by
    refine integral_mono (hint 3) hintRHS fun q ↦ ?_
    · have hcs := cube_pageOp_le W q.1 q.2
      calc W q.1 q.2 * pageOp W (1 / 3) q.1 q.2 ^ 3
          ≤ W q.1 q.2 * (pageOp W 0 q.1 q.2 ^ 2 * pageOp W 1 q.1 q.2) :=
            mul_le_mul_of_nonneg_left hcs (W.nonneg _ _)
        _ = W q.1 q.2 * pageOp W 0 q.1 q.2 * pageOp W 0 q.1 q.2 *
              pageOp W 1 q.1 q.2 := by ring
  -- the two spine Cauchy--Schwarz steps
  have hcs1 := integral_mul_sq_le_integral_mul_integral_mul_sq
    (μ := μ.prod μ) (A := fun q : Ω × Ω ↦ W q.1 q.2)
    (η := fun q : Ω × Ω ↦ pageOp W (1 / 3) q.1 q.2) hWi
    ((hint 1).congr (ae_of_all _ fun q ↦ by simp only []; rw [pow_one]))
    (hint 2) fun q ↦ W.nonneg _ _
  rw [integral_prod_edge] at hcs1
  have hcs2 := integral_mul_sq_le_integral_mul_integral_mul_sq
    (μ := μ.prod μ)
    (A := fun q : Ω × Ω ↦ W q.1 q.2 * pageOp W (1 / 3) q.1 q.2)
    (η := fun q : Ω × Ω ↦ pageOp W (1 / 3) q.1 q.2)
    ((hint 1).congr (ae_of_all _ fun q ↦ by simp only []; rw [pow_one]))
    ((hint 2).congr (ae_of_all _ fun q ↦ by simp only []; ring))
    ((hint 3).congr (ae_of_all _ fun q ↦ by simp only []; ring))
    (fun q ↦ mul_nonneg (W.nonneg _ _) (pageOp_nonneg W hthird _ _))
  -- name the four moments
  set B := ∫ q, W q.1 q.2 * pageOp W (1 / 3) q.1 q.2 ∂(μ.prod μ) with hBdef
  set C := ∫ q, W q.1 q.2 * pageOp W (1 / 3) q.1 q.2 ^ 2 ∂(μ.prod μ) with hCdef
  set D := ∫ q, W q.1 q.2 * pageOp W (1 / 3) q.1 q.2 ^ 3 ∂(μ.prod μ) with hDdef
  have hC1 : B ^ 2 ≤ p * C := hcs1
  have hC2 : C ^ 2 ≤ B * D := by
    have e1 : (∫ q, W q.1 q.2 * pageOp W (1 / 3) q.1 q.2 *
        pageOp W (1 / 3) q.1 q.2 ∂(μ.prod μ)) = C := by
      rw [hCdef]
      exact integral_congr_ae (ae_of_all _ fun q ↦ by simp only []; ring)
    have e2 : (∫ q, W q.1 q.2 * pageOp W (1 / 3) q.1 q.2 *
        pageOp W (1 / 3) q.1 q.2 ^ 2 ∂(μ.prod μ)) = D := by
      rw [hDdef]
      exact integral_congr_ae (ae_of_all _ fun q ↦ by simp only []; ring)
    rw [e1, e2] at hcs2
    exact hcs2
  have hBn : 0 ≤ B := integral_nonneg fun q ↦
    mul_nonneg (W.nonneg _ _) (pageOp_nonneg W hthird _ _)
  have hDn : 0 ≤ D := integral_nonneg fun q ↦
    mul_nonneg (W.nonneg _ _) (pow_nonneg (pageOp_nonneg W hthird _ _) 3)
  -- `B³ ≤ p²·D`
  have hcube : B ^ 3 ≤ p ^ 2 * D := by
    rcases eq_or_lt_of_le hBn with hB0 | hBpos
    · rw [← hB0, zero_pow (by norm_num : (3 : ℕ) ≠ 0)]
      positivity
    · have h3 : B ^ 4 ≤ p ^ 2 * C ^ 2 := by nlinarith [pow_le_pow_left₀ (sq_nonneg B) hC1 2]
      have h4 : p ^ 2 * C ^ 2 ≤ p ^ 2 * (B * D) :=
        mul_le_mul_of_nonneg_left hC2 (sq_nonneg p)
      have h5 : B * B ^ 3 ≤ B * (p ^ 2 * D) := by nlinarith [h3, h4]
      exact le_of_mul_le_mul_left h5 hBpos
  -- the rooted-triangle input
  have hA : B = ∫ z, degree W z ^ (1 / 3 : ℝ) * rootedTriangle W z ∂μ := by
    rw [hBdef]
    exact integral_edge_pageOp W hthird
  have hwrt : (2 * p - 1) * momentR W (1 / 3 + 2) ≤ p * B := by
    have h := weighted_rootedTriangle_rpow (W := W) hthird
    rw [← hpdef] at h
    rw [hA]
    exact h
  have hmom : p ^ ((7 : ℝ) / 3) ≤ momentR W (1 / 3 + 2) := by
    have h := rpow_le_momentR (W := W) (s := (7 : ℝ) / 3) (by norm_num)
    rw [← hpdef] at h
    rwa [show (1 : ℝ) / 3 + 2 = (7 : ℝ) / 3 by norm_num]
  have h2p : (0 : ℝ) ≤ 2 * p - 1 := by linarith
  have hq : (2 * p - 1) * p ^ ((7 : ℝ) / 3) ≤ p * B :=
    le_trans (mul_le_mul_of_nonneg_left hmom h2p) hwrt
  have h73 : (p ^ ((7 : ℝ) / 3)) ^ (3 : ℕ) = p ^ (7 : ℕ) := by
    rw [← Real.rpow_natCast (p ^ ((7 : ℝ) / 3)) 3, ← Real.rpow_mul hppos.le,
      show (7 : ℝ) / 3 * (3 : ℕ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hqnn : 0 ≤ (2 * p - 1) * p ^ ((7 : ℝ) / 3) :=
    mul_nonneg h2p (Real.rpow_nonneg hppos.le _)
  have hcubed := pow_le_pow_left₀ hqnn hq 3
  rw [mul_pow, h73] at hcubed
  -- assemble
  rw [hprod]
  refine le_trans ?_ hmono
  have hstepD : p ^ 3 * B ^ 3 ≤ p ^ 3 * (p ^ 2 * D) :=
    mul_le_mul_of_nonneg_left hcube (by positivity)
  have hfin : p ^ 5 * (p ^ 2 * (2 * p - 1) ^ 3) ≤ p ^ 5 * D := by
    nlinarith [hcubed, hstepD]
  exact le_of_mul_le_mul_left hfin (by positivity)

/-! ### Chromatic data and the catalogue proposition -/

lemma affineProd_138 (z : ℝ) :
    affineProd [0, 1, 1, 2, 2, 2] z = z ^ 2 * (2 * z - 1) ^ 3 := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_cons, affineProd_nil]
  ring

def iso138 :
    attachVertex (attachVertex
      (attachVertex (⊤ : SimpleGraph (Fin 3)) {0, 1}) {some 0, some 1})
      {none} ≃g book138 where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom138 : IsChromaticPolynomial book138
    ((([0, 1, 1, 2, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := book138) iso138
    (isClique_singleton _ none)
    (isChromaticPolynomial_attachVertex (isClique_attach_pair {0, 1} (by decide))
      (isChromaticPolynomial_attachVertex (isCliqueTop _)
        (isChromaticPolynomial_top 3)))
  rw [show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide,
    show (({some 0, some 1} : Finset (Option (Fin 3))).card) = 2 from by decide,
    Finset.card_singleton] at h
  have hpoly : ((([0, 1, 1, 2, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) * ((X - C ((2 : ℕ) : ℝ)) *
        ((X - C ((2 : ℕ) : ℝ)) * ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ)))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count138 (k : ℕ) :
    properAssignmentCount book138 k =
      (k - 1) * ((k - 2) * ((k - 2) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := book138) iso138
      (isClique_singleton _ none) k,
    properAssignmentCount_attachVertex (isClique_attach_pair {0, 1} (by decide)),
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide,
    show (({some 0, some 1} : Finset (Option (Fin 3))).card) = 2 from by decide,
    Finset.card_singleton]

theorem num138 : IsChromaticNumber book138 3 where
  positive := by rw [count138]; decide
  zero_below k hk := by
    rw [count138, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero, Nat.mul_zero]

/-- **Atlas 138 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_138 : Taeyoung.SatisfiesLowerBound book138 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = (([0, 1, 1, 2, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := book138) hP chrom138
  have hreq : r = 3 := IsChromaticNumber.unique (H := book138) hr num138
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := book138_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 2, 2, 2] (by norm_num) hone,
      affineProd_138]
    exact hkey

end Taeyoung.Methods.PageBook
