import Taeyoung.Methods.Peeling
import Taeyoung.Methods.PathSidorenko
import Taeyoung.Methods.ForestCone.Rows
import Taeyoung.Methods.BaseCone.Rows

/-!
# Atlas 95: a triangle with one leaf and one two-edge tail at the same vertex

`R_{1,1}` of `notes/mixed_rooted_triangle_branches.tex`.  Peeling every branch
at the root gives

```
t(R_{1,1},W) = ∫ τ(x)·A(x)·d(x) dμ(x),      A = T_W d.
```

**The route here is not the note's.**  The note proves, for general `(r,s)`, a
complement-kernel symmetrization showing that the mean two-edge-tail density
under the `d^r`-biased measure is at least `p²`, and then treats all `s` tails
with one convex Jensen step.  At `(r,s) = (1,1)` — the only scoped case — none
of that is needed.  The pointwise Goodman bound `τ ≥ 2A - p` turns the density
into two moments of the *already available* weight `d·A`,

```
t ≥ 2∫d·A² - p∫d·A,
```

and then the weighted Cauchy–Schwarz `(∫d·A)² ≤ (∫d)(∫d·A²)` and path Sidorenko
`∫d·A ≥ p³` close it through the factorization

```
p·(2C - pB) - p·(2p⁵ - p⁴) ≥ (B - p³)(2(B + p³) - p²) ≥ 0,
```

with `B = ∫d·A`, `C = ∫d·A²`.  Both inputs predate this row:
`Link.rootedTriangle_ge`, `PureChordal.integral_mul_sq_le_integral_mul_integral_mul_sq`
and `PathSidorenko.pow_three_le_pathIntegral`.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.MixedBranch

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PureChordal Taeyoung.Methods.PawCone
  Taeyoung.Methods.BaseCone Taeyoung.Methods.ForestCone
  Taeyoung.Methods.PathSidorenko

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The graph -/

/-- Triangle `0,1,2`; leaf `3` at the root `0`; two-edge tail `0–4–5`. -/
def r11 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (4, 5)]

instance : DecidableRel r11.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_r11 :
    r11.edgeFinset = {s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(0, 4), s(4, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_r11 (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight r11 W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
        W (x 0) (x 4) * W (x 4) (x 5) := by
  rw [graphWeight, edgeFinset_r11]
  simp
  ring

section Peel

variable (W : Graphon Ω μ)

private lemma meas_r11 : Measurable fun y : Fin 6 → Ω ↦
    W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) * W (y 0) (y 3) *
      W (y 0) (y 4) * W (y 4) (y 5) :=
  (((((measurable_coord_pair W 0 1).mul (measurable_coord_pair W 0 2)).mul
    (measurable_coord_pair W 1 2)).mul (measurable_coord_pair W 0 3)).mul
    (measurable_coord_pair W 0 4)).mul (measurable_coord_pair W 4 5)

private lemma bdd_r11 (x : Fin 6 → Ω) :
    |W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
      W (x 0) (x 4) * W (x 4) (x 5)| ≤ 1 := by
  have h0 : 0 ≤ W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
      W (x 0) (x 4) * W (x 4) (x 5) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_) ?_ <;>
      exact W.nonneg _ _
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (mul_le_one₀
    (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _)

/-- **The density of Atlas 95 is `∫ τ·A·d`.** -/
theorem homDensity_r11 :
    homDensity r11 W =
      ∫ x, rootedTriangle W x * (pathOp W x * degree W x) ∂μ := by
  rw [homDensity, integral_congr_ae (ae_of_all _ (graphWeight_r11 W)),
    integral_assignment_fin_six
      (g := fun a0 a1 a2 a3 a4 a5 ↦ W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 *
        W a0 a4 * W a4 a5)
      (meas_r11 W) (bdd_r11 W)]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  -- the three branch integrals, at fixed `a0`
  have hinner : ∀ a1 a2 : Ω,
      (∫ a3, ∫ a4, ∫ a5, W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 *
          W a0 a4 * W a4 a5 ∂μ ∂μ ∂μ) =
        (W a0 a1 * W a0 a2 * W a1 a2) * (pathOp W a0 * degree W a0) := by
    intro a1 a2
    have h5 : ∀ a3 a4 : Ω,
        (∫ a5, W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a0 a4 * W a4 a5 ∂μ) =
          ((W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * W a0 a4) * degree W a4 := by
      intro a3 a4
      have hre : ∀ a5 : Ω,
          W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a0 a4 * W a4 a5 =
            ((W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * W a0 a4) * W a4 a5 :=
        fun a5 ↦ by ring
      rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
      rfl
    have h4 : ∀ a3 : Ω,
        (∫ a4, ∫ a5, W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 *
            W a0 a4 * W a4 a5 ∂μ ∂μ) =
          (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * pathOp W a0 := by
      intro a3
      rw [integral_congr_ae (ae_of_all _ (h5 a3))]
      have hre : ∀ a4 : Ω,
          ((W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * W a0 a4) * degree W a4 =
            (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) *
              (W a0 a4 * degree W a4) := fun a4 ↦ by ring
      rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul, ← pathOp]
    rw [integral_congr_ae (ae_of_all _ h4)]
    have hre : ∀ a3 : Ω,
        (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * pathOp W a0 =
          ((W a0 a1 * W a0 a2 * W a1 a2) * pathOp W a0) * W a0 a3 :=
      fun a3 ↦ by ring
    rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
    show (W a0 a1 * W a0 a2 * W a1 a2) * pathOp W a0 * degree W a0 = _
    ring
  -- the triangle is the last two coordinates
  have h12 : (∫ a1, ∫ a2, (W a0 a1 * W a0 a2 * W a1 a2) *
      (pathOp W a0 * degree W a0) ∂μ ∂μ) =
      rootedTriangle W a0 * (pathOp W a0 * degree W a0) := by
    have h2 : ∀ a1 : Ω,
        (∫ a2, (W a0 a1 * W a0 a2 * W a1 a2) *
            (pathOp W a0 * degree W a0) ∂μ) =
          (pathOp W a0 * degree W a0) *
            ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 ∂μ := by
      intro a1
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun a2 ↦ by ring)
    rw [integral_congr_ae (ae_of_all _ h2), integral_const_mul]
    show (pathOp W a0 * degree W a0) * rootedTriangle W a0 = _
    ring
  rw [← h12]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  exact hinner a1 a2

end Peel

/-! ### The bound -/

/-- **Atlas 95 dominates its target.** -/
theorem r11_bound (W : Graphon Ω μ) (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 4 * (2 * cliqueDensity 2 W - 1) ≤ homDensity r11 W := by
  set p := cliqueDensity 2 W with hpdef
  have hppos : (0 : ℝ) < p := by linarith
  -- integrability of the three integrands
  have hdA : Integrable (fun x ↦ degree W x * pathOp W x) μ :=
    integrable_of_bdd ((measurable_degree W).mul (measurable_pathOp W)) (C := 1)
      fun x ↦ by
        rw [abs_of_nonneg (mul_nonneg (degree_nonneg W x) (pathOp_nonneg W x))]
        exact mul_le_one₀ (degree_le_one W x) (pathOp_nonneg W x)
          (pathOp_le_one W x)
  have hdA2 : Integrable (fun x ↦ degree W x * pathOp W x ^ 2) μ :=
    integrable_of_bdd
      ((measurable_degree W).mul ((measurable_pathOp W).pow_const 2)) (C := 1)
      fun x ↦ by
        have h0 : 0 ≤ degree W x * pathOp W x ^ 2 :=
          mul_nonneg (degree_nonneg W x) (pow_nonneg (pathOp_nonneg W x) 2)
        rw [abs_of_nonneg h0]
        exact mul_le_one₀ (degree_le_one W x) (pow_nonneg (pathOp_nonneg W x) 2)
          (pow_le_one₀ (pathOp_nonneg W x) (pathOp_le_one W x))
  have hlin : Integrable
      (fun x ↦ (2 * pathOp W x - p) * (pathOp W x * degree W x)) μ := by
    refine Integrable.congr ((hdA2.const_mul 2).sub (hdA.const_mul p))
      (ae_of_all _ fun x ↦ ?_)
    show 2 * (degree W x * pathOp W x ^ 2) - p * (degree W x * pathOp W x) =
      (2 * pathOp W x - p) * (pathOp W x * degree W x)
    ring
  have hτ : Integrable
      (fun x ↦ rootedTriangle W x * (pathOp W x * degree W x)) μ :=
    integrable_of_bdd ((measurable_rootedTriangle W).mul
      ((measurable_pathOp W).mul (measurable_degree W))) (C := 1) fun x ↦ by
        have h0 : 0 ≤ rootedTriangle W x * (pathOp W x * degree W x) :=
          mul_nonneg (rootedTriangle_nonneg W x)
            (mul_nonneg (pathOp_nonneg W x) (degree_nonneg W x))
        rw [abs_of_nonneg h0]
        exact mul_le_one₀ (rootedTriangle_le_one W x)
          (mul_nonneg (pathOp_nonneg W x) (degree_nonneg W x))
          (mul_le_one₀ (pathOp_le_one W x) (degree_nonneg W x)
            (degree_le_one W x))
  -- the pointwise Goodman bound
  have hmono : (∫ x, (2 * pathOp W x - p) * (pathOp W x * degree W x) ∂μ) ≤
      ∫ x, rootedTriangle W x * (pathOp W x * degree W x) ∂μ :=
    integral_mono hlin hτ fun x ↦
      mul_le_mul_of_nonneg_right (by rw [hpdef]; exact rootedTriangle_ge W x)
        (mul_nonneg (pathOp_nonneg W x) (degree_nonneg W x))
  -- the two moments
  set B := ∫ x, degree W x * pathOp W x ∂μ with hBdef
  set C := ∫ x, degree W x * pathOp W x ^ 2 ∂μ with hCdef
  have hval : (∫ x, (2 * pathOp W x - p) * (pathOp W x * degree W x) ∂μ) =
      2 * C - p * B := by
    have hre : ∀ x : Ω, (2 * pathOp W x - p) * (pathOp W x * degree W x) =
        2 * (degree W x * pathOp W x ^ 2) - p * (degree W x * pathOp W x) :=
      fun x ↦ by ring
    rw [integral_congr_ae (ae_of_all _ hre),
      integral_sub (hdA2.const_mul 2) (hdA.const_mul p),
      integral_const_mul, integral_const_mul]
  rw [hval] at hmono
  -- weighted Cauchy--Schwarz with weight `d`, and path Sidorenko
  have hcs := integral_mul_sq_le_integral_mul_integral_mul_sq (μ := μ)
    (A := degree W) (η := pathOp W) (integrable_degree W) hdA hdA2
    (degree_nonneg W)
  rw [integral_degree, ← hpdef, ← hBdef, ← hCdef] at hcs
  have hB : p ^ 3 ≤ B := by
    rw [hBdef, hpdef]
    exact pow_three_le_pathIntegral W
  have hB0 : 0 ≤ B :=
    integral_nonneg fun x ↦ mul_nonneg (degree_nonneg W x) (pathOp_nonneg W x)
  -- the scalar factorization
  have hfac : 0 ≤ (B - p ^ 3) * (2 * (B + p ^ 3) - p ^ 2) := by
    refine mul_nonneg (by linarith) ?_
    have h1 : 0 ≤ p ^ 2 * (2 * p - 1) :=
      mul_nonneg (sq_nonneg p) (by linarith)
    nlinarith [hB0, h1]
  have hstep : p * (p ^ 4 * (2 * p - 1)) ≤ p * (2 * C - p * B) := by
    nlinarith [hcs, hfac, hppos]
  rw [homDensity_r11 W]
  exact le_trans (le_of_mul_le_mul_left hstep hppos) hmono

/-! ### Chromatic data and the catalogue proposition -/

lemma affineProd_95 (z : ℝ) :
    affineProd [0, 1, 1, 1, 1, 2] z = z ^ 4 * (2 * z - 1) := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_cons, affineProd_nil]
  ring

/-- `K₃` on the triangle, then the leaf at `0`, then the tail hung off it. -/
def iso95 :
    attachVertex (attachVertex
      (attachVertex (⊤ : SimpleGraph (Fin 3)) {0}) {some 0}) {none} ≃g
      r11 where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom95 : IsChromaticPolynomial r11
    ((([0, 1, 1, 1, 1, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := r11) iso95
    (isClique_singleton _ none)
    (isChromaticPolynomial_attachVertex (isClique_singleton _ (some 0))
      (isChromaticPolynomial_attachVertex (isCliqueTop _)
        (isChromaticPolynomial_top 3)))
  rw [show (({0} : Finset (Fin 3)).card) = 1 from by decide,
    Finset.card_singleton, Finset.card_singleton] at h
  have hpoly :
      ((([0, 1, 1, 1, 1, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) * ((X - C ((1 : ℕ) : ℝ)) *
        ((X - C ((1 : ℕ) : ℝ)) * ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ)))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count95 (k : ℕ) :
    properAssignmentCount r11 k =
      (k - 1) * ((k - 1) * ((k - 1) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := r11) iso95
      (isClique_singleton _ none) k,
    properAssignmentCount_attachVertex (isClique_singleton _ (some 0)),
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0} : Finset (Fin 3)).card) = 1 from by decide,
    Finset.card_singleton, Finset.card_singleton]

theorem num95 : IsChromaticNumber r11 3 where
  positive := by rw [count95]; decide
  zero_below k hk := by
    rw [count95, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero, Nat.mul_zero]

/-- **Atlas 95 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_95 : Taeyoung.SatisfiesLowerBound r11 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P =
      (([0, 1, 1, 1, 1, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := r11) hP chrom95
  have hreq : r = 3 := IsChromaticNumber.unique (H := r11) hr num95
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := r11_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 1, 1, 2] (by norm_num) hone,
      affineProd_95]
    exact hkey

end Taeyoung.Methods.MixedBranch
