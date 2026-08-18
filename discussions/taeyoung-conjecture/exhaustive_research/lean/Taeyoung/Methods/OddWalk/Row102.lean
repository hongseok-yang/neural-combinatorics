import Taeyoung.Methods.OddWalk.Limit
import Taeyoung.Methods.PathSidorenko
import Taeyoung.Methods.Peeling
import Taeyoung.Methods.ForestCone.Rows
import Taeyoung.Methods.AffineProduct
import Taeyoung.Methods.PawCone.Rows
import Taeyoung.Methods.BaseCone.Rows

/-!
# Atlas 102: a triangle with a three-edge tail

`notes/triangle_three_edge_tail.tex` reduces the row to the odd-walk inequality
`a₅³ ≥ a₃⁵`, now available as `a3_pow_five_le_a5_pow_three`.  This file carries
out the reduction, in the shorter form of Appendix A of that note.

Two simplifications over the body of the note.  First, the rooted-triangle bound
`τ ≥ 2A - p` is only ever integrated against `B ≥ 0`, so

```
t(R₃,W) = ∫ τ·B ≥ ∫ (2A - p)·B = 2a₅ - p·a₃ ,
```

with no auxiliary probability measure, no Jensen and no convexity.  Second, the
full odd-walk theorem is stronger than needed: only

```
a₅ ≥ p²·a₃
```

is used, and it follows from `a₅³ ≥ a₃⁵` together with Blakley--Roy
`a₃ ≥ p³`, since `a₃⁵ = a₃³·a₃² ≥ a₃³·p⁶ = (p²a₃)³`.
-/

namespace Taeyoung.Methods.OddWalk

open MeasureTheory
open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.PathSidorenko
open Taeyoung.Methods.ForestCone Taeyoung.Methods.PawCone Taeyoung.Methods.BaseCone
open Finset Polynomial

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Blakley–Roy, in the walk notation -/

/-- `t(P₃,W) ≥ p³`.  This is `PathSidorenko.pow_three_le_pathIntegral`, restated
through `walkIter`. -/
theorem edgeDensity_pow_three_le_a3 (W : Graphon Ω μ) :
    cliqueDensity 2 W ^ 3 ≤ a3 W := by
  have h := pow_three_le_pathIntegral W
  have e : ∫ x, degree W x * pathOp W x ∂μ = a3 W := by
    rw [← integral_degree_mul_pathOp W]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    show degree W x * pathOp W x = walkIter W 1 x * walkIter W 2 x
    rw [walkIter_one, walkIter_two]
  rwa [e] at h

/-! ### The consequence of the odd-walk inequality that the row needs -/

/-- `a₅ ≥ p²·a₃`, strictly weaker than `a₅³ ≥ a₃⁵`. -/
theorem sq_mul_a3_le_a5 (W : Graphon Ω μ) :
    cliqueDensity 2 W ^ 2 * a3 W ≤ a5 W := by
  have hBR : cliqueDensity 2 W ^ 3 ≤ a3 W := edgeDensity_pow_three_le_a3 W
  have hodd : a3 W ^ 5 ≤ a5 W ^ 3 := a3_pow_five_le_a5_pow_three W
  have ha3 : 0 ≤ a3 W := a3_nonneg W
  have hp : 0 ≤ cliqueDensity 2 W := cliqueDensity_nonneg 2 W
  have hsq : cliqueDensity 2 W ^ 6 ≤ a3 W ^ 2 := by
    nlinarith [hBR, pow_nonneg hp 3, ha3]
  have key : (cliqueDensity 2 W ^ 2 * a3 W) ^ 3 ≤ a5 W ^ 3 := by
    calc (cliqueDensity 2 W ^ 2 * a3 W) ^ 3
        = a3 W ^ 3 * cliqueDensity 2 W ^ 6 := by ring
      _ ≤ a3 W ^ 3 * a3 W ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = a3 W ^ 5 := by ring
      _ ≤ a5 W ^ 3 := hodd
  exact le_of_pow_le_pow_left₀ (by norm_num) (a5_nonneg W) key

/-! ### The rooted density of `R₃` -/

/-- The pointwise Goodman bound, integrated against the three-edge walk density.
No Jensen: `B ≥ 0`, so the linearisation may be integrated directly. -/
theorem two_a5_sub_le_rooted (W : Graphon Ω μ) :
    2 * a5 W - cliqueDensity 2 W * a3 W
      ≤ ∫ x, rootedTriangle W x * walkIter W 3 x ∂μ := by
  have hle : ∀ x : Ω,
      (2 * walkIter W 2 x - cliqueDensity 2 W) * walkIter W 3 x
        ≤ rootedTriangle W x * walkIter W 3 x := by
    intro x
    refine mul_le_mul_of_nonneg_right ?_ (walkIter_nonneg W 3 x)
    rw [walkIter_two]
    exact rootedTriangle_ge W x
  have i1 : Integrable (fun x ↦ (2 * walkIter W 2 x - cliqueDensity 2 W)
      * walkIter W 3 x) μ :=
    integrable_of_bdd
      ((((measurable_walkIter W 2).const_mul 2).sub measurable_const).mul
        (measurable_walkIter W 3))
      (C := (2 + |cliqueDensity 2 W|) * 1) fun x ↦ by
        rw [abs_mul]
        refine mul_le_mul ?_ ?_ (abs_nonneg _) (by positivity)
        · calc |2 * walkIter W 2 x - cliqueDensity 2 W|
              ≤ |2 * walkIter W 2 x| + |cliqueDensity 2 W| := abs_sub _ _
            _ ≤ 2 + |cliqueDensity 2 W| := by
                have : |2 * walkIter W 2 x| ≤ 2 := by
                  rw [abs_mul, abs_of_nonneg (walkIter_nonneg W 2 x)]
                  simpa using
                    mul_le_mul_of_nonneg_left (walkIter_le_one W 2 x) (by norm_num : (0:ℝ) ≤ 2)
                linarith
        · rw [abs_of_nonneg (walkIter_nonneg W 3 x)]
          exact walkIter_le_one W 3 x
  have i2 : Integrable (fun x ↦ rootedTriangle W x * walkIter W 3 x) μ :=
    integrable_of_bdd ((measurable_rootedTriangle W).mul (measurable_walkIter W 3))
      (C := 1) fun x ↦ by
        rw [abs_of_nonneg (mul_nonneg (rootedTriangle_nonneg W x)
          (walkIter_nonneg W 3 x))]
        exact mul_le_one₀ (rootedTriangle_le_one W x) (walkIter_nonneg W 3 x)
          (walkIter_le_one W 3 x)
  have hsplit : ∫ x, (2 * walkIter W 2 x - cliqueDensity 2 W) * walkIter W 3 x ∂μ
      = 2 * a5 W - cliqueDensity 2 W * a3 W := by
    have e : ∀ x : Ω, (2 * walkIter W 2 x - cliqueDensity 2 W) * walkIter W 3 x
        = 2 * (walkIter W 2 x * walkIter W 3 x)
          - cliqueDensity 2 W * walkIter W 3 x := fun x ↦ by ring
    have j1 : Integrable (fun x ↦ 2 * (walkIter W 2 x * walkIter W 3 x)) μ := by
      refine Integrable.const_mul ?_ 2
      exact integrable_of_bdd
        ((measurable_walkIter W 2).mul (measurable_walkIter W 3)) (C := 1) fun x ↦ by
          rw [abs_of_nonneg (mul_nonneg (walkIter_nonneg W 2 x)
            (walkIter_nonneg W 3 x))]
          exact mul_le_one₀ (walkIter_le_one W 2 x) (walkIter_nonneg W 3 x)
            (walkIter_le_one W 3 x)
    have j2 : Integrable (fun x ↦ cliqueDensity 2 W * walkIter W 3 x) μ :=
      (integrable_walkIter W 3).const_mul _
    rw [integral_congr_ae (ae_of_all _ e), integral_sub j1 j2,
      integral_const_mul, integral_const_mul]
    rfl
  calc 2 * a5 W - cliqueDensity 2 W * a3 W
      = ∫ x, (2 * walkIter W 2 x - cliqueDensity 2 W) * walkIter W 3 x ∂μ :=
        hsplit.symm
    _ ≤ ∫ x, rootedTriangle W x * walkIter W 3 x ∂μ := integral_mono i1 i2 hle

/-! ### The bound -/

/-- **The analytic content of Atlas 102.**  For `p ≥ 1/2`,
`∫ τ·B ≥ p⁴(2p-1)`. -/
theorem target_le_rooted (W : Graphon Ω μ)
    (hp : 1 / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 4 * (2 * cliqueDensity 2 W - 1)
      ≤ ∫ x, rootedTriangle W x * walkIter W 3 x ∂μ := by
  have h1 := sq_mul_a3_le_a5 W
  have h2 := edgeDensity_pow_three_le_a3 W
  have hp0 : 0 ≤ cliqueDensity 2 W := cliqueDensity_nonneg 2 W
  have hkey : 0 ≤ cliqueDensity 2 W
      * ((2 * cliqueDensity 2 W - 1) * (a3 W - cliqueDensity 2 W ^ 3)) :=
    mul_nonneg hp0 (mul_nonneg (by linarith) (by linarith))
  have hmain : cliqueDensity 2 W ^ 4 * (2 * cliqueDensity 2 W - 1)
      ≤ 2 * a5 W - cliqueDensity 2 W * a3 W := by nlinarith [h1, hkey, hp0]
  exact le_trans hmain (two_a5_sub_le_rooted W)


/-! ### The graph -/

/-- Atlas 102: the triangle `0,1,2` with the three-edge tail `0-3-4-5`. -/
def r3 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (1, 2), (0, 3), (3, 4), (4, 5)]

instance : DecidableRel r3.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_r3 :
    r3.edgeFinset = {s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(3, 4), s(4, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_r3 (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight r3 W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
        W (x 3) (x 4) * W (x 4) (x 5) := by
  rw [graphWeight, edgeFinset_r3]
  simp
  ring

section Peel

variable (W : Graphon Ω μ)

private lemma meas_r3 : Measurable fun y : Fin 6 → Ω ↦
    W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) * W (y 0) (y 3) *
      W (y 3) (y 4) * W (y 4) (y 5) :=
  (((((measurable_coord_pair W 0 1).mul (measurable_coord_pair W 0 2)).mul
    (measurable_coord_pair W 1 2)).mul (measurable_coord_pair W 0 3)).mul
    (measurable_coord_pair W 3 4)).mul (measurable_coord_pair W 4 5)

private lemma bdd_r3 (x : Fin 6 → Ω) :
    |W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
      W (x 3) (x 4) * W (x 4) (x 5)| ≤ 1 := by
  have h0 : 0 ≤ W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
      W (x 3) (x 4) * W (x 4) (x 5) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_) ?_ <;>
      exact W.nonneg _ _
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (mul_le_one₀
    (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _)

/-- **The density of Atlas 102 is `∫ τ·B`.**  Peeling the tail from its free end
towards the root turns the three tail edges into `walkIter W 3`. -/
theorem homDensity_r3 :
    homDensity r3 W = ∫ x, rootedTriangle W x * walkIter W 3 x ∂μ := by
  rw [homDensity, integral_congr_ae (ae_of_all _ (graphWeight_r3 W)),
    integral_assignment_fin_six
      (g := fun a0 a1 a2 a3 a4 a5 ↦ W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 *
        W a3 a4 * W a4 a5)
      (meas_r3 W) (bdd_r3 W)]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  have hinner : ∀ a1 a2 : Ω,
      (∫ a3, ∫ a4, ∫ a5, W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 *
          W a3 a4 * W a4 a5 ∂μ ∂μ ∂μ) =
        (W a0 a1 * W a0 a2 * W a1 a2) * walkIter W 3 a0 := by
    intro a1 a2
    have h5 : ∀ a3 a4 : Ω,
        (∫ a5, W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a3 a4 * W a4 a5 ∂μ) =
          ((W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * W a3 a4) * walkIter W 1 a4 := by
      intro a3 a4
      have hre : ∀ a5 : Ω,
          W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a3 a4 * W a4 a5 =
            ((W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * W a3 a4) * W a4 a5 :=
        fun a5 ↦ by ring
      rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul, walkIter_one]
      rfl
    have h4 : ∀ a3 : Ω,
        (∫ a4, ∫ a5, W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 *
            W a3 a4 * W a4 a5 ∂μ ∂μ) =
          (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * walkIter W 2 a3 := by
      intro a3
      rw [integral_congr_ae (ae_of_all _ (h5 a3))]
      have hre : ∀ a4 : Ω,
          ((W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * W a3 a4) * walkIter W 1 a4 =
            (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) *
              (W a3 a4 * walkIter W 1 a4) := fun a4 ↦ by ring
      rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
      rfl
    rw [integral_congr_ae (ae_of_all _ h4)]
    have hre : ∀ a3 : Ω,
        (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * walkIter W 2 a3 =
          (W a0 a1 * W a0 a2 * W a1 a2) * (W a0 a3 * walkIter W 2 a3) :=
      fun a3 ↦ by ring
    rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
    rfl
  have h12 : (∫ a1, ∫ a2, (W a0 a1 * W a0 a2 * W a1 a2) * walkIter W 3 a0 ∂μ ∂μ) =
      rootedTriangle W a0 * walkIter W 3 a0 := by
    have h2 : ∀ a1 : Ω,
        (∫ a2, (W a0 a1 * W a0 a2 * W a1 a2) * walkIter W 3 a0 ∂μ) =
          walkIter W 3 a0 * ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 ∂μ := by
      intro a1
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun a2 ↦ by ring)
    rw [integral_congr_ae (ae_of_all _ h2), integral_const_mul]
    show walkIter W 3 a0 * rootedTriangle W a0 = _
    ring
  rw [← h12]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  exact hinner a1 a2

end Peel

/-! ### The chromatic data

`R₃` is `K₃` with three vertices attached in a chain, each to a single earlier
vertex, so its chromatic polynomial is `x(x-1)⁴(x-2)` — the same as the broom's,
and the same target `p⁴(2p-1)`. -/

lemma affineProd_102 (z : ℝ) :
    affineProd [0, 1, 1, 1, 1, 2] z = z ^ 4 * (2 * z - 1) := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_cons, affineProd_nil]
  ring

/-- `K₃`, then `3` on the root `0`, then `4` on `3`, then `5` on `4`. -/
def iso102 :
    attachVertex (attachVertex
      (attachVertex (⊤ : SimpleGraph (Fin 3)) {0}) {none}) {none} ≃g r3 where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom102 : IsChromaticPolynomial r3
    ((([0, 1, 1, 1, 1, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := r3) iso102
    (isClique_singleton _ none)
    (isChromaticPolynomial_attachVertex (isClique_singleton _ none)
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

theorem count102 (k : ℕ) :
    properAssignmentCount r3 k =
      (k - 1) * ((k - 1) * ((k - 1) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := r3) iso102
      (isClique_singleton _ none) k,
    properAssignmentCount_attachVertex (isClique_singleton _ none),
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0} : Finset (Fin 3)).card) = 1 from by decide,
    Finset.card_singleton, Finset.card_singleton]

theorem num102 : IsChromaticNumber r3 3 where
  positive := by rw [count102]; decide
  zero_below k hk := by
    rw [count102, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero, Nat.mul_zero]

/-- **Atlas 102 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_102 : Taeyoung.SatisfiesLowerBound r3 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P =
      (([0, 1, 1, 1, 1, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := r3) hP chrom102
  have hreq : r = 3 := IsChromaticNumber.unique (H := r3) hr num102
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := target_le_rooted W hp
  rw [← homDensity_r3 W] at hkey
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 1, 1, 2] (by norm_num) hone,
      affineProd_102]
    exact hkey

end Taeyoung.Methods.OddWalk
