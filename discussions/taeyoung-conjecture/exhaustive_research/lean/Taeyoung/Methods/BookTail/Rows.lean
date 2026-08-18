import Taeyoung.Methods.BookTail.Core
import Taeyoung.Methods.ForestCone.Rows
import Taeyoung.Methods.BaseCone.Rows

/-!
# Atlas 120: the two-page book with a two-edge tail on the spine

`R₂` in the notation of `notes/triangle_book_two_edge_tail.tex`: spine `0,1`,
two pages `2,3` adjacent to both, and a two-edge tail `0–4–5` at the spine
endpoint `0`.  Peeling gives

```
t(R₂,W) = ∫∫ W(x,y)·A(x)·S(x,y)²,
```

with `A = T_W d = pathOp` and `S = H₀ = pageOp 0`.  One weighted Cauchy–Schwarz
on `μ ⊗ μ`, with weight `W(x,y)A(x)`, turns that into `F²/B`, where
`Methods/BookTail/Core.lean` supplies

```
B = ∫A·d = t(P₄,W) ≥ p³ > 0,      F = ∫A·τ ≥ max{(2p-1)B, p³(2p-1)}.
```

Multiplying the two lower bounds for `F` gives `t·B ≥ p³(2p-1)²·B`, and `B > 0`
finishes — no division by `2p-1`, which vanishes at the threshold.

Only `m ≤ 2` is in scope: `R₁` is the five-vertex triangle-with-a-two-edge-tail
(already `verified` by the rooted-tree route) and `R₃` has seven vertices.  So
the note's Jensen step for `s ↦ s^m` at general `m` is not needed here, and the
`m = 2` instance is exactly Cauchy–Schwarz.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.BookTail

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PureChordal Taeyoung.Methods.PawCone
  Taeyoung.Methods.ForestCone Taeyoung.Methods.BaseCone
  Taeyoung.Methods.PathSidorenko

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The graph -/

/-- Spine `0,1`; pages `2,3`; tail `0–4–5`. -/
def book120 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (4, 5)]

instance : DecidableRel book120.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_book120 :
    book120.edgeFinset =
      {s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(1, 3), s(0, 4), s(4, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_book120 (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight book120 W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
        W (x 1) (x 3) * W (x 0) (x 4) * W (x 4) (x 5) := by
  rw [graphWeight, edgeFinset_book120]
  simp
  ring

lemma graphWeight_book120_cons (W : Graphon Ω μ) (a0 a1 a2 a3 a4 a5 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight book120 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
        (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y)))))) =
      W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * W a0 a4 * W a4 a5 := by
  rw [graphWeight_book120]
  rfl

/-! ### The density identity -/

/-- **The density of Atlas 120 is `∫∫ W·A·S²`.** -/
theorem homDensity_book120 (W : Graphon Ω μ) :
    homDensity book120 W =
      ∫ a0, ∫ a1, W a0 a1 * pathOp W a0 * pageOp W 0 a0 a1 ^ 2 ∂μ ∂μ := by
  have hm : Measurable (graphWeight book120 W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight book120 W x| ≤ 1 := fun x ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 5 → Ω ↦ graphWeight book120 W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω ↦ graphWeight book120 W (Fin.cons a0 (Fin.cons a1 y)))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  have hstep2 : ∀ a2 : Ω,
      (∫ y : Fin 3 → Ω,
          graphWeight book120 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)))
        ∂assignmentMeasure (Fin 3) μ) =
        (W a0 a1 * W a0 a2 * W a1 a2) *
          (pathOp W a0 * pageOp W 0 a0 a1) := by
    intro a2
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 3 → Ω ↦
        graphWeight book120 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
      (hm.comp ((measurable_fin_cons a0).comp
        ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
      fun y ↦ hb _]
    have hstep3 : ∀ a3 : Ω,
        (∫ y : Fin 2 → Ω,
            graphWeight book120 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
          ∂assignmentMeasure (Fin 2) μ) =
          ((W a0 a1 * W a0 a2 * W a1 a2) * pathOp W a0) *
            (W a0 a3 * W a1 a3 * degree W a3 ^ (0 : ℝ)) := by
      intro a3
      rw [integral_assignmentMeasure_succ
        (fun y : Fin 2 → Ω ↦ graphWeight book120 W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
        (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
          ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
        fun y ↦ hb _]
      have hstep4 : ∀ a4 : Ω,
          (∫ y : Fin 1 → Ω, graphWeight book120 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                (Fin.cons a4 y)))))
            ∂assignmentMeasure (Fin 1) μ) =
            (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3) *
              (W a0 a4 * degree W a4) := by
        intro a4
        rw [integral_assignmentMeasure_succ
          (fun y : Fin 1 → Ω ↦ graphWeight book120 W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
              (Fin.cons a4 y))))))
          (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
            ((measurable_fin_cons a2).comp ((measurable_fin_cons a3).comp
              (measurable_fin_cons a4))))))
          fun y ↦ hb _]
        have hval : ∀ a5 : Ω,
            (∫ y : Fin 0 → Ω, graphWeight book120 W
                (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                  (Fin.cons a4 (Fin.cons a5 y))))))
              ∂assignmentMeasure (Fin 0) μ) =
              (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * W a0 a4) *
                W a4 a5 := by
          intro a5
          rw [show (∫ y : Fin 0 → Ω, graphWeight book120 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                (Fin.cons a4 (Fin.cons a5 y))))))
                ∂assignmentMeasure (Fin 0) μ) =
              W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * W a0 a4 *
                W a4 a5 by simp [graphWeight_book120_cons]]
        rw [integral_congr_ae (ae_of_all _ hval), integral_const_mul]
        show (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * W a0 a4) *
            degree W a4 =
          (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3) *
            (W a0 a4 * degree W a4)
        ring
      rw [integral_congr_ae (ae_of_all _ hstep4), Real.rpow_zero,
        integral_const_mul, ← pathOp]
      ring
    rw [integral_congr_ae (ae_of_all _ hstep3), integral_const_mul, ← pageOp]
    ring
  rw [integral_congr_ae (ae_of_all _ hstep2)]
  have hre : ∀ a2 : Ω,
      (W a0 a1 * W a0 a2 * W a1 a2) * (pathOp W a0 * pageOp W 0 a0 a1) =
        (W a0 a1 * pathOp W a0 * pageOp W 0 a0 a1) *
          (W a0 a2 * W a1 a2 * degree W a2 ^ (0 : ℝ)) := by
    intro a2
    rw [Real.rpow_zero]
    ring
  rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul, ← pageOp]
  ring

/-! ### The two Fubini identities for the edge weight `W(x,y)A(x)` -/

/-- The weight `W(x,y)·A(x)`, as a function on `Ω × Ω`. -/
noncomputable def tailWeight (W : Graphon Ω μ) (q : Ω × Ω) : ℝ :=
  W q.1 q.2 * pathOp W q.1

lemma measurable_tailWeight (W : Graphon Ω μ) : Measurable (tailWeight W) :=
  W.measurable.mul ((measurable_pathOp W).comp measurable_fst)

lemma tailWeight_nonneg (W : Graphon Ω μ) (q : Ω × Ω) : 0 ≤ tailWeight W q :=
  mul_nonneg (W.nonneg _ _) (pathOp_nonneg W _)

lemma tailWeight_le_one (W : Graphon Ω μ) (q : Ω × Ω) : tailWeight W q ≤ 1 :=
  mul_le_one₀ (W.le_one _ _) (pathOp_nonneg W _) (pathOp_le_one W _)

lemma integrable_tailWeight (W : Graphon Ω μ) :
    Integrable (tailWeight W) (μ.prod μ) :=
  integrable_prod_of_bdd (measurable_tailWeight W) (C := 1) fun q ↦ by
    rw [abs_of_nonneg (tailWeight_nonneg W q)]
    exact tailWeight_le_one W q

lemma integrable_tailWeight_mul_pow (W : Graphon Ω μ) (j : ℕ) :
    Integrable (fun q : Ω × Ω ↦ tailWeight W q * pageOp W 0 q.1 q.2 ^ j)
      (μ.prod μ) := by
  refine integrable_prod_of_bdd
    ((measurable_tailWeight W).mul ((measurable_pageOp W le_rfl).pow_const j))
    (C := 1) fun q ↦ ?_
  have h0 : 0 ≤ tailWeight W q * pageOp W 0 q.1 q.2 ^ j :=
    mul_nonneg (tailWeight_nonneg W q) (pow_nonneg (pageOp_nonneg W le_rfl _ _) j)
  show |tailWeight W q * pageOp W 0 q.1 q.2 ^ j| ≤ 1
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (tailWeight_le_one W q)
    (pow_nonneg (pageOp_nonneg W le_rfl _ _) j)
    (pow_le_one₀ (pageOp_nonneg W le_rfl _ _) (pageOp_le_one W le_rfl _ _))

lemma integrable_tailWeight_mul_pageOp (W : Graphon Ω μ) :
    Integrable (fun q : Ω × Ω ↦ tailWeight W q * pageOp W 0 q.1 q.2)
      (μ.prod μ) := by
  refine integrable_prod_of_bdd
    ((measurable_tailWeight W).mul (measurable_pageOp W le_rfl)) (C := 1) fun q ↦ ?_
  have h0 : 0 ≤ tailWeight W q * pageOp W 0 q.1 q.2 :=
    mul_nonneg (tailWeight_nonneg W q) (pageOp_nonneg W le_rfl _ _)
  show |tailWeight W q * pageOp W 0 q.1 q.2| ≤ 1
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (tailWeight_le_one W q) (pageOp_nonneg W le_rfl _ _)
    (pageOp_le_one W le_rfl _ _)

/-- `∫ W(x,y)·S(x,y) dμ(y) = τ(x)`. -/
lemma integral_edge_pageOp_row (W : Graphon Ω μ) (x : Ω) :
    (∫ y, W x y * pageOp W 0 x y ∂μ) = rootedTriangle W x := by
  rw [rootedTriangle]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  show W x y * pageOp W 0 x y = ∫ z, W x y * W x z * W y z ∂μ
  rw [pageOp_zero_eq, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun z ↦ by ring)

/-- `∫∫ W(x,y)A(x) = B`. -/
theorem integral_tailWeight (W : Graphon Ω μ) :
    (∫ q, tailWeight W q ∂(μ.prod μ)) = ∫ x, pathOp W x * degree W x ∂μ := by
  rw [← integral_integral (f := fun x y ↦ tailWeight W (x, y))
    (integrable_tailWeight W)]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  show (∫ y, W x y * pathOp W x ∂μ) = pathOp W x * degree W x
  rw [integral_mul_const]
  show degree W x * pathOp W x = pathOp W x * degree W x
  ring

/-- `∫∫ W(x,y)A(x)S(x,y) = F`. -/
theorem integral_tailWeight_mul_pageOp (W : Graphon Ω μ) :
    (∫ q, tailWeight W q * pageOp W 0 q.1 q.2 ∂(μ.prod μ)) =
      ∫ x, pathOp W x * rootedTriangle W x ∂μ := by
  rw [← integral_integral
    (f := fun x y ↦ tailWeight W (x, y) * pageOp W 0 (x, y).1 (x, y).2)
    (integrable_tailWeight_mul_pageOp W)]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  show (∫ y, W x y * pathOp W x * pageOp W 0 x y ∂μ) =
    pathOp W x * rootedTriangle W x
  have hre : ∀ y : Ω, W x y * pathOp W x * pageOp W 0 x y =
      pathOp W x * (W x y * pageOp W 0 x y) := by
    intro y; ring
  rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul,
    integral_edge_pageOp_row]

/-! ### The bound -/

/-- **Atlas 120 dominates its target.** -/
theorem book120_bound (W : Graphon Ω μ)
    (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 3 * (2 * cliqueDensity 2 W - 1) ^ 2 ≤
      homDensity book120 W := by
  set p := cliqueDensity 2 W with hpdef
  set B := ∫ x, pathOp W x * degree W x ∂μ with hBdef
  set F := ∫ x, pathOp W x * rootedTriangle W x ∂μ with hFdef
  -- the density on the product measure
  have hprod : homDensity book120 W =
      ∫ q, tailWeight W q * pageOp W 0 q.1 q.2 ^ 2 ∂(μ.prod μ) := by
    rw [homDensity_book120]
    exact integral_integral (f := fun a0 a1 ↦
      tailWeight W (a0, a1) * pageOp W 0 (a0, a1).1 (a0, a1).2 ^ 2)
      (integrable_tailWeight_mul_pow W 2)
  -- weighted Cauchy--Schwarz with weight `W(x,y)A(x)`
  have hcs := integral_mul_sq_le_integral_mul_integral_mul_sq
    (μ := μ.prod μ) (A := tailWeight W)
    (η := fun q : Ω × Ω ↦ pageOp W 0 q.1 q.2)
    (integrable_tailWeight W)
    (integrable_tailWeight_mul_pageOp W)
    (integrable_tailWeight_mul_pow W 2)
    (tailWeight_nonneg W)
  rw [integral_tailWeight_mul_pageOp, integral_tailWeight, ← hBdef, ← hFdef,
    ← hprod] at hcs
  -- the two lower bounds on `F`, and `B > 0`
  have hFB : (2 * p - 1) * B ≤ F :=
    weighted_le_integral_pathOp_mul_rootedTriangle W hp
  have hFp : p ^ 3 * (2 * p - 1) ≤ F := firstPage_bound W hp
  have hBpos : (0 : ℝ) < B := by
    have h := pow_three_le_pathIntegral W
    have hre : (∫ x, degree W x * pathOp W x ∂μ) = B := by
      rw [hBdef]
      exact integral_congr_ae (ae_of_all _ fun x ↦ mul_comm _ _)
    rw [hre, ← hpdef] at h
    have : (0 : ℝ) < p ^ 3 := by positivity
    linarith
  have h2p : (0 : ℝ) ≤ 2 * p - 1 := by linarith
  have hF0 : 0 ≤ F := le_trans (mul_nonneg h2p hBpos.le) hFB
  -- multiply the two bounds and divide by `B`
  have hmul : p ^ 3 * (2 * p - 1) * ((2 * p - 1) * B) ≤ F * F :=
    mul_le_mul hFp hFB (mul_nonneg h2p hBpos.le) hF0
  have hfinal : p ^ 3 * (2 * p - 1) ^ 2 * B ≤ homDensity book120 W * B := by
    nlinarith [hcs, hmul]
  exact le_of_mul_le_mul_right hfinal hBpos

/-! ### Chromatic data and the catalogue proposition -/

lemma affineProd_120 (z : ℝ) :
    affineProd [0, 1, 1, 1, 2, 2] z = z ^ 3 * (2 * z - 1) ^ 2 := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_cons, affineProd_nil]
  ring

/-- `K₃` on the spine and one page, the second page on the spine edge, then the
tail hung off the spine endpoint `0`. -/
def iso120 :
    attachVertex (attachVertex
      (attachVertex (⊤ : SimpleGraph (Fin 3)) {0, 1}) {some 0}) {none} ≃g
      book120 where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom120 : IsChromaticPolynomial book120
    ((([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := book120) iso120
    (isClique_singleton _ none)
    (isChromaticPolynomial_attachVertex (isClique_singleton _ (some 0))
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

theorem count120 (k : ℕ) :
    properAssignmentCount book120 k =
      (k - 1) * ((k - 1) * ((k - 2) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := book120) iso120
      (isClique_singleton _ none) k,
    properAssignmentCount_attachVertex (isClique_singleton _ (some 0)),
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide,
    Finset.card_singleton, Finset.card_singleton]

theorem num120 : IsChromaticNumber book120 3 where
  positive := by rw [count120]; decide
  zero_below k hk := by
    rw [count120, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero, Nat.mul_zero]

/-- **Atlas 120 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_120 : Taeyoung.SatisfiesLowerBound book120 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P =
      (([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := book120) hP chrom120
  have hreq : r = 3 := IsChromaticNumber.unique (H := book120) hr num120
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := book120_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 1, 2, 2] (by norm_num) hone,
      affineProd_120]
    exact hkey

end Taeyoung.Methods.BookTail
