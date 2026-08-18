import Taeyoung.Methods.OddLeaf.Holder
import Taeyoung.Methods.K4Tail.Link
import Taeyoung.Methods.BookTail.Core
import Taeyoung.Methods.ForestCone.Rows
import Taeyoung.Methods.BaseCone.Rows

/-!
# Atlas 119: a leaf on the bowtie's outer orbit

`notes/bowtie_outer_leaves.tex` at `h = 1`.  The bowtie has five vertices, so
the only scoped member of the family carries a single leaf, and the note's two
symmetrisation exponents are

```
α = h/4 = 1/4   (the four outer vertices are one orbit),
β = h/6 = 1/6   (a second symmetrisation inside a triangle).
```

Both are reciprocal integers, so `Methods/OddLeaf/Bias.lean` applies unchanged
and the note's Lemma 2.1 is `OddLeaf.pow_eight_le_pow_rootEdge` at `m = 6`.

The chain: peel the leaf, symmetrise the degree over the four outer vertices
and apply the arithmetic–geometric mean inequality, factor the result over the
two triangles as `∫ R²` with

```
R(x) = ∫∫ W(x,y)W(x,z)W(y,z)·d(y)^{1/4}d(z)^{1/4},
```

drop to `(∫R)²` by Cauchy–Schwarz, symmetrise `∫R` over the three triangle
rotations and apply the arithmetic–geometric mean inequality again to reach
exponent `1/6` at every vertex, and finish with Goodman on the `d^{1/6}`-biased
probability space.

**The scalar rescaling is proved differently from the note.**  The note's
Lemma 2.2 introduces `s₀ = p(p^{h/2}/z)^{2/3}` and proves `zA₃(s₀) ≥ p^{h/2}A₃(p)`
by differentiating `ψ(s) = A₃(s)/s^{3/2} = 2√s - 1/√s`.  At `h = 1` that
statement contains `p^{1/2}`, and the formalization forms no square root at all:
since the quantity actually needed downstream is the *square* `(∫R)²`, the whole
rescaling is

```
p·A₃(p)² ≤ K·A₃(s)²,      K = M⁶,
```

from `K ≤ p` (Jensen) and `p⁸ ≤ K²s⁶` (the fractional Hölder).  Clearing it
reduces to `p(2s-1)² ≥ s(2p-1)²`, which is the single factorisation

```
p(2s-1)² - s(2p-1)² = (s-p)(4ps-1) ≥ 0     (1/2 ≤ p ≤ s),
```

the same factor as the `CliqueDist/Diamond` rescaling.  No derivative, no `ψ`,
and no half-integer power appears.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.BowtieLeaf

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.BookTail Taeyoung.Methods.OddLeaf
  Taeyoung.Methods.BaseCone Taeyoung.Methods.ForestCone
  Taeyoung.Methods.PawCone

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The scalar rescaling -/

/-- **The biased edge density dominates the original one.** -/
theorem le_biased {p s K : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hs0 : 0 ≤ s)
    (hK0 : 0 < K) (hKp : K ≤ p) (hKs : p ^ 8 ≤ K ^ 2 * s ^ 6) : p ≤ s := by
  have hp0 : (0 : ℝ) < p := by linarith
  refine le_of_pow_le_pow_left₀ (n := 6) (by norm_num) hs0 ?_
  have hK2 : K ^ 2 ≤ p ^ 2 := by nlinarith [hK0, hKp]
  have h1 : K ^ 2 * s ^ 6 ≤ p ^ 2 * s ^ 6 :=
    mul_le_mul_of_nonneg_right hK2 (pow_nonneg hs0 6)
  have h3 : p ^ 2 * p ^ 6 ≤ p ^ 2 * s ^ 6 := by
    rw [show p ^ 2 * p ^ 6 = p ^ 8 by ring]
    exact le_trans hKs h1
  exact le_of_mul_le_mul_left h3 (by positivity)

/-- **The bowtie rescaling.**  `A₃(u) = u(2u-1)`. -/
theorem transfer {p s K : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hs0 : 0 ≤ s)
    (hK0 : 0 < K) (hKp : K ≤ p) (hKs : p ^ 8 ≤ K ^ 2 * s ^ 6) :
    p * (p * (2 * p - 1)) ^ 2 ≤ K * (s * (2 * s - 1)) ^ 2 := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hps : p ≤ s := le_biased hp hs0 hK0 hKp hKs
  have hs2 : (1 : ℝ) / 2 ≤ s := le_trans hp hps
  have hs0' : (0 : ℝ) < s := by linarith
  -- `K·s³ ≥ p⁴`, the unsquared Hölder bound
  have hKs3 : p ^ 4 ≤ K * s ^ 3 := by
    refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity) ?_
    calc (p ^ 4) ^ 2 = p ^ 8 := by ring
      _ ≤ K ^ 2 * s ^ 6 := hKs
      _ = (K * s ^ 3) ^ 2 := by ring
  -- the cleared monotonicity `p(2s-1)² ≥ s(2p-1)²`
  have hmono : s * (2 * p - 1) ^ 2 ≤ p * (2 * s - 1) ^ 2 := by
    have hid : p * (2 * s - 1) ^ 2 - s * (2 * p - 1) ^ 2 =
        (s - p) * (4 * p * s - 1) := by ring
    have h1 : (0 : ℝ) ≤ s - p := by linarith
    have h2 : (0 : ℝ) ≤ 4 * p * s - 1 := by nlinarith [hp, hs2]
    nlinarith [hid, mul_nonneg h1 h2]
  -- assemble, after clearing `s³`
  have hB0 : (0 : ℝ) ≤ (s * (2 * s - 1)) ^ 2 := sq_nonneg _
  have hstep1 : p ^ 4 * (s * (2 * s - 1)) ^ 2 ≤ (K * s ^ 3) * (s * (2 * s - 1)) ^ 2 :=
    mul_le_mul_of_nonneg_right hKs3 hB0
  have hstep2 : p * (p * (2 * p - 1)) ^ 2 * s ^ 3 ≤ p ^ 4 * (s * (2 * s - 1)) ^ 2 := by
    have hexp : p ^ 4 * (s * (2 * s - 1)) ^ 2 -
        p * (p * (2 * p - 1)) ^ 2 * s ^ 3 =
        p ^ 3 * s ^ 2 * (p * (2 * s - 1) ^ 2 - s * (2 * p - 1) ^ 2) := by ring
    have hnn : (0 : ℝ) ≤ p ^ 3 * s ^ 2 *
        (p * (2 * s - 1) ^ 2 - s * (2 * p - 1) ^ 2) :=
      mul_nonneg (mul_nonneg (pow_nonneg hp0.le 3) (sq_nonneg s)) (by linarith)
    linarith [hexp, hnn]
  have hcancel : p * (p * (2 * p - 1)) ^ 2 * s ^ 3 ≤
      K * (s * (2 * s - 1)) ^ 2 * s ^ 3 := by
    calc p * (p * (2 * p - 1)) ^ 2 * s ^ 3
        ≤ p ^ 4 * (s * (2 * s - 1)) ^ 2 := hstep2
      _ ≤ (K * s ^ 3) * (s * (2 * s - 1)) ^ 2 := hstep1
      _ = K * (s * (2 * s - 1)) ^ 2 * s ^ 3 := by ring
  exact le_of_mul_le_mul_right hcancel (by positivity)

/-! ### The pair-weighted rooted triangle -/

/-- `R(x) = ∫∫ W(x,y)W(x,z)W(y,z)·d(y)^{1/4}d(z)^{1/4}`. -/
noncomputable def pairTri (W : Graphon Ω μ) (x : Ω) : ℝ :=
  ∫ y, ∫ z, W x y * W x z * W y z * rootDegree W 4 y * rootDegree W 4 z ∂μ ∂μ

section PairTri

variable (W : Graphon Ω μ)

private lemma bdd_pairTri (x y z : Ω) :
    |W x y * W x z * W y z * rootDegree W 4 y * rootDegree W 4 z| ≤ 1 := by
  have h0 : 0 ≤ W x y * W x z * W y z * rootDegree W 4 y * rootDegree W 4 z :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (W.nonneg _ _) (W.nonneg _ _))
      (W.nonneg _ _)) (rootDegree_nonneg W _)) (rootDegree_nonneg W _)
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (W.le_one _ _)
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _))
    (rootDegree_nonneg W _) (rootDegree_le_one W _))
    (rootDegree_nonneg W _) (rootDegree_le_one W _)

private lemma ker_pairTri (x : Ω) : Measurable
    (Function.uncurry fun y z ↦
      W x y * W x z * W y z * rootDegree W 4 y * rootDegree W 4 z) :=
  ((((W.measurable.comp (measurable_const.prodMk measurable_fst)).mul
    (W.measurable.comp (measurable_const.prodMk measurable_snd))).mul
    W.measurable).mul ((measurable_rootDegree W).comp measurable_fst)).mul
    ((measurable_rootDegree W).comp measurable_snd)

lemma pairTri_nonneg (x : Ω) : 0 ≤ pairTri W x :=
  integral_nonneg fun y ↦ integral_nonneg fun z ↦
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (W.nonneg _ _) (W.nonneg _ _))
      (W.nonneg _ _)) (rootDegree_nonneg W _)) (rootDegree_nonneg W _)

lemma measurable_pairTri : Measurable (pairTri W) := by
  have hg : StronglyMeasurable (fun q : (Ω × Ω) × Ω ↦
      W q.1.1 q.1.2 * W q.1.1 q.2 * W q.1.2 q.2 *
        rootDegree W 4 q.1.2 * rootDegree W 4 q.2) := by
    refine (?_ : Measurable _).stronglyMeasurable
    exact ((((W.measurable.comp measurable_fst).mul
      (W.measurable.comp ((measurable_fst.comp measurable_fst).prodMk
        measurable_snd))).mul
      (W.measurable.comp ((measurable_snd.comp measurable_fst).prodMk
        measurable_snd))).mul
      ((measurable_rootDegree W).comp (measurable_snd.comp measurable_fst))).mul
      ((measurable_rootDegree W).comp measurable_snd)
  have hinner : Measurable
      (Function.uncurry fun x y ↦ ∫ z, W x y * W x z * W y z *
        rootDegree W 4 y * rootDegree W 4 z ∂μ) :=
    (hg.integral_prod_right' (ν := μ)).measurable
  exact (hinner.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

lemma pairTri_le_one (x : Ω) : pairTri W x ≤ 1 := by
  have hb : ∀ y, |∫ z, W x y * W x z * W y z * rootDegree W 4 y *
      rootDegree W 4 z ∂μ| ≤ 1 := fun y ↦
    abs_integral_le_of_bdd (measurable_row (ker_pairTri W x) y) (bdd_pairTri W x y)
  have hfin := abs_integral_le_of_bdd (μ := μ)
    (measurable_integral_right (ker_pairTri W x)) hb
  rw [abs_le] at hfin
  exact hfin.2

lemma integrable_pairTri : Integrable (pairTri W) μ :=
  integrable_of_bdd (measurable_pairTri W) (C := 1) fun x ↦ by
    rw [abs_of_nonneg (pairTri_nonneg W x)]
    exact pairTri_le_one W x

lemma integrable_sq_pairTri : Integrable (fun x ↦ pairTri W x ^ 2) μ :=
  integrable_of_bdd ((measurable_pairTri W).pow_const 2) (C := 1) fun x ↦ by
    rw [abs_of_nonneg (pow_nonneg (pairTri_nonneg W x) 2)]
    exact pow_le_one₀ (pairTri_nonneg W x) (pairTri_le_one W x)

/-- **Cauchy–Schwarz against the constant `1`.** -/
theorem sq_integral_pairTri_le :
    (∫ x, pairTri W x ∂μ) ^ 2 ≤ ∫ x, pairTri W x ^ 2 ∂μ := by
  have h := sq_integral_mul_le (ν := μ) (f := pairTri W) (g := fun _ ↦ (1 : ℝ))
    (integrable_sq_pairTri W) (by simpa using (integrable_const (1 : ℝ)))
    (by simpa using integrable_pairTri W)
  simpa using h

end PairTri

/-! ### The triangle symmetrisation

`∫R` is a triangle density carrying `d^{1/4}` at two of its three vertices.
Averaging the three rotations and applying the arithmetic–geometric mean
inequality moves it to `d^{1/6}` at all three. -/

lemma graphWeight_top_three (W : Graphon Ω μ) (x : Fin 3 → Ω) :
    graphWeight (⊤ : SimpleGraph (Fin 3)) W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) := by
  have hedge : (⊤ : SimpleGraph (Fin 3)).edgeFinset =
      {s(0, 1), s(0, 2), s(1, 2)} := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      revert u v
      decide
  rw [graphWeight, hedge]
  simp
  ring

/-- The three-term arithmetic–geometric mean step of the triangle
symmetrisation: the geometric mean of the three pair weights is the `1/6`-power
weight at every vertex. -/
theorem prod_pair_rootDegree (W : Graphon Ω μ) (u v w : Ω) :
    rootDegree W 6 u * rootDegree W 6 v * rootDegree W 6 w ≤
      ((3 : ℝ))⁻¹ * (rootDegree W 4 v * rootDegree W 4 w) +
        ((3 : ℝ))⁻¹ * (rootDegree W 4 w * rootDegree W 4 u) +
        ((3 : ℝ))⁻¹ * (rootDegree W 4 u * rootDegree W 4 v) := by
  set z : Fin 3 → ℝ := ![rootDegree W 4 v * rootDegree W 4 w,
    rootDegree W 4 w * rootDegree W 4 u,
    rootDegree W 4 u * rootDegree W 4 v] with hz
  have hz0 : ∀ i ∈ (univ : Finset (Fin 3)), 0 ≤ z i := by
    intro i _
    fin_cases i <;>
      exact mul_nonneg (rootDegree_nonneg W _) (rootDegree_nonneg W _)
  have hagm := Real.geom_mean_le_arith_mean_weighted (univ : Finset (Fin 3))
    (fun _ ↦ ((3 : ℝ))⁻¹) z (fun i _ ↦ by norm_num)
    (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num) hz0
  refine le_trans (le_of_eq ?_) (le_of_le_of_eq hagm ?_)
  · -- the geometric mean is the `1/6`-power weight
    rw [Fin.prod_univ_three]
    have hpair : ∀ a b : Ω,
        (rootDegree W 4 a * rootDegree W 4 b) ^ ((3 : ℝ))⁻¹ =
          degree W a ^ ((12 : ℝ))⁻¹ * degree W b ^ ((12 : ℝ))⁻¹ := by
      intro a b
      rw [rootDegree, rootDegree,
        Real.mul_rpow (Real.rpow_nonneg (degree_nonneg W a) _)
          (Real.rpow_nonneg (degree_nonneg W b) _),
        ← Real.rpow_mul (degree_nonneg W a), ← Real.rpow_mul (degree_nonneg W b)]
      norm_num
    have hsix : ∀ a : Ω,
        degree W a ^ ((12 : ℝ))⁻¹ * degree W a ^ ((12 : ℝ))⁻¹ =
          rootDegree W 6 a := by
      intro a
      rw [rootDegree, ← Real.rpow_add' (degree_nonneg W a) (by norm_num)]
      norm_num
    show _ = z 0 ^ ((3 : ℝ))⁻¹ * z 1 ^ ((3 : ℝ))⁻¹ * z 2 ^ ((3 : ℝ))⁻¹
    simp only [hz, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [hpair, hpair, hpair, ← hsix u, ← hsix v, ← hsix w]
    ring
  · rw [Fin.sum_univ_three]
    simp only [hz, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- Every permutation of three points is an automorphism of `K₃`. -/
def topIso (e : Fin 3 ≃ Fin 3) :
    (⊤ : SimpleGraph (Fin 3)) ≃g (⊤ : SimpleGraph (Fin 3)) where
  toEquiv := e
  map_rel_iff' := by
    intro a b
    simp only [SimpleGraph.top_adj, ne_eq, EmbeddingLike.apply_eq_iff_eq]

/-- The rotation `0 ↦ 1 ↦ 2 ↦ 0`. -/
def rot1 : Fin 3 ≃ Fin 3 where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide
  right_inv := by decide

/-- The rotation `0 ↦ 2 ↦ 1 ↦ 0`. -/
def rot2 : Fin 3 ≃ Fin 3 where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by decide
  right_inv := by decide

/-- **The triangle symmetrisation.**  Averaging the three rotations of the pair
weight and applying the arithmetic–geometric mean inequality moves the exponent
from `1/4` at two vertices to `1/6` at all three. -/
theorem integral_prod_rootDegree_le (W : Graphon Ω μ) :
    (∫ y, (∏ i, rootDegree W 6 (y i)) * graphWeight (⊤ : SimpleGraph (Fin 3)) W y
        ∂assignmentMeasure (Fin 3) μ) ≤ ∫ x, pairTri W x ∂μ := by
  set ν := assignmentMeasure (Fin 3) μ with hν
  -- the three rotated integrands
  set g : Fin 3 → (Fin 3 → Ω) → ℝ :=
    ![fun y ↦ graphWeight (⊤ : SimpleGraph (Fin 3)) W y *
        (rootDegree W 4 (y 1) * rootDegree W 4 (y 2)),
      fun y ↦ graphWeight (⊤ : SimpleGraph (Fin 3)) W y *
        (rootDegree W 4 (y 2) * rootDegree W 4 (y 0)),
      fun y ↦ graphWeight (⊤ : SimpleGraph (Fin 3)) W y *
        (rootDegree W 4 (y 0) * rootDegree W 4 (y 1))] with hg
  have hshape : ∀ j : Fin 3, ∃ a b : Fin 3,
      g j = fun y ↦ graphWeight (⊤ : SimpleGraph (Fin 3)) W y *
        (rootDegree W 4 (y a) * rootDegree W 4 (y b)) := by
    intro j
    fin_cases j
    · exact ⟨1, 2, rfl⟩
    · exact ⟨2, 0, rfl⟩
    · exact ⟨0, 1, rfl⟩
  have hmeasg : ∀ j, Measurable (g j) := by
    intro j
    obtain ⟨a, b, hj⟩ := hshape j
    rw [hj]
    exact (measurable_graphWeight _ W).mul
      (((measurable_rootDegree W).comp (measurable_pi_apply a)).mul
        ((measurable_rootDegree W).comp (measurable_pi_apply b)))
  have hbddg : ∀ j y, |g j y| ≤ 1 := by
    intro j y
    obtain ⟨a, b, hj⟩ := hshape j
    rw [hj]
    have h0 : 0 ≤ graphWeight (⊤ : SimpleGraph (Fin 3)) W y *
        (rootDegree W 4 (y a) * rootDegree W 4 (y b)) :=
      mul_nonneg (graphWeight_nonneg _ W y)
        (mul_nonneg (rootDegree_nonneg W _) (rootDegree_nonneg W _))
    rw [abs_of_nonneg h0]
    exact mul_le_one₀ (graphWeight_le_one _ W y)
      (mul_nonneg (rootDegree_nonneg W _) (rootDegree_nonneg W _))
      (mul_le_one₀ (rootDegree_le_one W _) (rootDegree_nonneg W _)
        (rootDegree_le_one W _))
  have hintg : ∀ j, Integrable (g j) ν := fun j ↦
    integrable_of_bounded (hmeasg j) (hbddg j)
  -- rotating the coordinates leaves the integral unchanged
  have hrot1 : (∫ y, g 1 y ∂ν) = ∫ y, g 0 y ∂ν := by
    rw [integral_assignment_perm rot1 (g 0)]
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    have hw : graphWeight (⊤ : SimpleGraph (Fin 3)) W (fun v ↦ y (rot1 v)) =
        graphWeight (⊤ : SimpleGraph (Fin 3)) W y :=
      graphWeight_iso W (topIso rot1) y
    show graphWeight (⊤ : SimpleGraph (Fin 3)) W y *
        (rootDegree W 4 (y 2) * rootDegree W 4 (y 0)) =
      graphWeight (⊤ : SimpleGraph (Fin 3)) W (fun v ↦ y (rot1 v)) *
        (rootDegree W 4 (y (rot1 1)) * rootDegree W 4 (y (rot1 2)))
    rw [hw, show rot1 1 = 2 from rfl, show rot1 2 = 0 from rfl]
  have hrot2 : (∫ y, g 2 y ∂ν) = ∫ y, g 0 y ∂ν := by
    rw [integral_assignment_perm rot2 (g 0)]
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    have hw : graphWeight (⊤ : SimpleGraph (Fin 3)) W (fun v ↦ y (rot2 v)) =
        graphWeight (⊤ : SimpleGraph (Fin 3)) W y :=
      graphWeight_iso W (topIso rot2) y
    show graphWeight (⊤ : SimpleGraph (Fin 3)) W y *
        (rootDegree W 4 (y 0) * rootDegree W 4 (y 1)) =
      graphWeight (⊤ : SimpleGraph (Fin 3)) W (fun v ↦ y (rot2 v)) *
        (rootDegree W 4 (y (rot2 1)) * rootDegree W 4 (y (rot2 2)))
    rw [hw, show rot2 1 = 0 from rfl, show rot2 2 = 1 from rfl]
  have hrot : ∀ j : Fin 3, (∫ y, g j y ∂ν) = ∫ y, g 0 y ∂ν := by
    intro j
    fin_cases j
    · rfl
    · exact hrot1
    · exact hrot2
  -- the arithmetic–geometric mean step
  have hagm : (∫ y, (∏ i, rootDegree W 6 (y i)) *
      graphWeight (⊤ : SimpleGraph (Fin 3)) W y ∂ν) ≤ ∫ y, g 0 y ∂ν := by
    have hleft : Integrable (fun y : Fin 3 → Ω ↦ (∏ i, rootDegree W 6 (y i)) *
        graphWeight (⊤ : SimpleGraph (Fin 3)) W y) ν := by
      refine integrable_of_bounded (C := 1) ?_ ?_
      · exact (Finset.measurable_prod _ fun i _ ↦
          (measurable_rootDegree W).comp (measurable_pi_apply i)).mul
          (measurable_graphWeight _ W)
      · intro y
        have hp0 : 0 ≤ ∏ i, rootDegree W 6 (y i) :=
          Finset.prod_nonneg fun i _ ↦ rootDegree_nonneg W _
        have hp1 : (∏ i, rootDegree W 6 (y i)) ≤ 1 :=
          Finset.prod_le_one (fun i _ ↦ rootDegree_nonneg W _)
            (fun i _ ↦ rootDegree_le_one W _)
        rw [abs_of_nonneg (mul_nonneg hp0 (graphWeight_nonneg _ W y))]
        exact mul_le_one₀ hp1 (graphWeight_nonneg _ W y) (graphWeight_le_one _ W y)
    have hright : Integrable (fun y : Fin 3 → Ω ↦
        ∑ j, ((3 : ℝ))⁻¹ * g j y) ν :=
      integrable_finsetSum _ fun j _ ↦ (hintg j).const_mul _
    have hstep : (∫ y, (∏ i, rootDegree W 6 (y i)) *
        graphWeight (⊤ : SimpleGraph (Fin 3)) W y ∂ν) ≤
        ∫ y, ∑ j, ((3 : ℝ))⁻¹ * g j y ∂ν := by
      refine integral_mono hleft hright fun y ↦ ?_
      have hpt := prod_pair_rootDegree W (y 0) (y 1) (y 2)
      have hexp : ∑ j, ((3 : ℝ))⁻¹ * g j y =
          graphWeight (⊤ : SimpleGraph (Fin 3)) W y *
            (((3 : ℝ))⁻¹ * (rootDegree W 4 (y 1) * rootDegree W 4 (y 2)) +
              ((3 : ℝ))⁻¹ * (rootDegree W 4 (y 2) * rootDegree W 4 (y 0)) +
              ((3 : ℝ))⁻¹ * (rootDegree W 4 (y 0) * rootDegree W 4 (y 1))) := by
        rw [Fin.sum_univ_three]
        show ((3 : ℝ))⁻¹ * (graphWeight (⊤ : SimpleGraph (Fin 3)) W y *
              (rootDegree W 4 (y 1) * rootDegree W 4 (y 2))) +
            ((3 : ℝ))⁻¹ * (graphWeight (⊤ : SimpleGraph (Fin 3)) W y *
              (rootDegree W 4 (y 2) * rootDegree W 4 (y 0))) +
            ((3 : ℝ))⁻¹ * (graphWeight (⊤ : SimpleGraph (Fin 3)) W y *
              (rootDegree W 4 (y 0) * rootDegree W 4 (y 1))) = _
        ring
      have hprod : (∏ i, rootDegree W 6 (y i)) =
          rootDegree W 6 (y 0) * rootDegree W 6 (y 1) * rootDegree W 6 (y 2) := by
        rw [Fin.prod_univ_three]
      rw [hexp, hprod, mul_comm (graphWeight (⊤ : SimpleGraph (Fin 3)) W y)]
      exact mul_le_mul_of_nonneg_right hpt (graphWeight_nonneg _ W y)
    refine le_trans hstep (le_of_eq ?_)
    rw [integral_finsetSum _ fun j _ ↦ (hintg j).const_mul _]
    have hterm : ∀ j : Fin 3, (∫ y, ((3 : ℝ))⁻¹ * g j y ∂ν) =
        ((3 : ℝ))⁻¹ * ∫ y, g 0 y ∂ν := by
      intro j
      rw [integral_const_mul, hrot j]
    rw [Finset.sum_congr rfl fun j _ ↦ hterm j, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    ring
  -- and `∫ g 0` is `∫ R`
  refine le_trans hagm (le_of_eq ?_)
  have hm0 : Measurable fun y : Fin 3 → Ω ↦
      (W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2)) *
        (rootDegree W 4 (y 1) * rootDegree W 4 (y 2)) :=
    (((measurable_coord_pair W 0 1).mul (measurable_coord_pair W 0 2)).mul
      (measurable_coord_pair W 1 2)).mul
      (((measurable_rootDegree W).comp (measurable_pi_apply 1)).mul
        ((measurable_rootDegree W).comp (measurable_pi_apply 2)))
  have hcongr : ∀ y : Fin 3 → Ω, g 0 y =
      (W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2)) *
        (rootDegree W 4 (y 1) * rootDegree W 4 (y 2)) := by
    intro y
    show graphWeight (⊤ : SimpleGraph (Fin 3)) W y *
      (rootDegree W 4 (y 1) * rootDegree W 4 (y 2)) = _
    rw [graphWeight_top_three]
  have hb0 : ∀ y : Fin 3 → Ω,
      |(W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2)) *
        (rootDegree W 4 (y 1) * rootDegree W 4 (y 2))| ≤ 1 := by
    intro y
    rw [← hcongr y]
    exact hbddg 0 y
  rw [integral_congr_ae (ae_of_all _ hcongr),
    integral_assignment_fin_three
      (g := fun a0 a1 a2 ↦ (W a0 a1 * W a0 a2 * W a1 a2) *
        (rootDegree W 4 a1 * rootDegree W 4 a2)) hm0 hb0]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only [pairTri]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  ring

/-! ### The graphs and their peeling -/

/-- The bowtie: centre `0`, triangles `{0,1,2}` and `{0,3,4}`. -/
def bowtie : SimpleGraph (Fin 5) :=
  graphFromEdges 5 [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)]

instance : DecidableRel bowtie.Adj := graphFromEdges_decidableAdj _ _

/-- The bowtie with one pendant leaf `5` on the outer vertex `1`. -/
def bowtieLeaf : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4), (1, 5)]

instance : DecidableRel bowtieLeaf.Adj := graphFromEdges_decidableAdj _ _

lemma graphWeight_bowtie (W : Graphon Ω μ) (x : Fin 5 → Ω) :
    graphWeight bowtie W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
        W (x 0) (x 4) * W (x 3) (x 4) := by
  have hedge : bowtie.edgeFinset =
      {s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(0, 4), s(3, 4)} := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      revert u v
      decide
  rw [graphWeight, hedge]
  simp
  ring

lemma graphWeight_bowtieLeaf (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight bowtieLeaf W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
        W (x 0) (x 4) * W (x 3) (x 4) * W (x 1) (x 5) := by
  have hedge : bowtieLeaf.edgeFinset =
      {s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(0, 4), s(3, 4), s(1, 5)} := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      revert u v
      decide
  rw [graphWeight, hedge]
  simp
  ring

section Peel

variable (W : Graphon Ω μ)

private lemma meas_core : Measurable fun y : Fin 5 → Ω ↦
    (W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) * W (y 0) (y 3) *
      W (y 0) (y 4) * W (y 3) (y 4)) * degree W (y 1) :=
  (((((measurable_coord_pair W 0 1).mul (measurable_coord_pair W 0 2)).mul
    (measurable_coord_pair W 1 2)).mul (measurable_coord_pair W 0 3)).mul
    (measurable_coord_pair W 0 4)).mul (measurable_coord_pair W 3 4) |>.mul
    ((measurable_degree W).comp (measurable_pi_apply 1))

private lemma bdd_core (y : Fin 5 → Ω) :
    |(W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) * W (y 0) (y 3) *
      W (y 0) (y 4) * W (y 3) (y 4)) * degree W (y 1)| ≤ 1 := by
  have h0 : 0 ≤ (W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) * W (y 0) (y 3) *
      W (y 0) (y 4) * W (y 3) (y 4)) * degree W (y 1) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg ?_ ?_) ?_) ?_) ?_) ?_) (degree_nonneg W _) <;> exact W.nonneg _ _
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (mul_le_one₀
    (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _))
    (degree_nonneg W _) (degree_le_one W _)

private lemma meas_leaf : Measurable fun y : Fin 6 → Ω ↦
    W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) * W (y 0) (y 3) *
      W (y 0) (y 4) * W (y 3) (y 4) * W (y 1) (y 5) :=
  ((((((measurable_coord_pair W 0 1).mul (measurable_coord_pair W 0 2)).mul
    (measurable_coord_pair W 1 2)).mul (measurable_coord_pair W 0 3)).mul
    (measurable_coord_pair W 0 4)).mul (measurable_coord_pair W 3 4)).mul
    (measurable_coord_pair W 1 5)

omit [IsProbabilityMeasure μ] in
private lemma bdd_leaf (x : Fin 6 → Ω) :
    |W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
      W (x 0) (x 4) * W (x 3) (x 4) * W (x 1) (x 5)| ≤ 1 := by
  have h0 : 0 ≤ W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
      W (x 0) (x 4) * W (x 3) (x 4) * W (x 1) (x 5) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg ?_ ?_) ?_) ?_) ?_) ?_) ?_ <;> exact W.nonneg _ _
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (mul_le_one₀
    (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)

/-- **The density of Atlas 119 is the bowtie weight against an outer degree.** -/
theorem homDensity_bowtieLeaf :
    homDensity bowtieLeaf W =
      ∫ y, graphWeight bowtie W y * degree W (y 1)
        ∂assignmentMeasure (Fin 5) μ := by
  have hright : (∫ y, graphWeight bowtie W y * degree W (y 1)
      ∂assignmentMeasure (Fin 5) μ) =
      ∫ a0, ∫ a1, ∫ a2, ∫ a3, ∫ a4,
        (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a0 a4 * W a3 a4) *
          degree W a1 ∂μ ∂μ ∂μ ∂μ ∂μ := by
    rw [integral_congr_ae (ae_of_all _ fun y ↦ by rw [graphWeight_bowtie]),
      integral_assignment_fin_five
        (g := fun a0 a1 a2 a3 a4 ↦
          (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a0 a4 * W a3 a4) *
            degree W a1)
        (meas_core W) (bdd_core W)]
  rw [hright, homDensity,
    integral_congr_ae (ae_of_all _ (graphWeight_bowtieLeaf W)),
    integral_assignment_fin_six
      (g := fun a0 a1 a2 a3 a4 a5 ↦ W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 *
        W a0 a4 * W a3 a4 * W a1 a5)
      (meas_leaf W) (bdd_leaf W)]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a3 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a4 ↦ ?_)
  simp only []
  have hre : ∀ a5 : Ω,
      W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a0 a4 * W a3 a4 * W a1 a5 =
        (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a0 a4 * W a3 a4) * W a1 a5 :=
    fun a5 ↦ by ring
  rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
  rfl

end Peel

/-! ### The outer-orbit symmetrisation -/

/-- Swap the two vertices of the first outer edge. -/
def aut2 : Fin 5 ≃ Fin 5 where
  toFun := ![0, 2, 1, 3, 4]
  invFun := ![0, 2, 1, 3, 4]
  left_inv := by decide
  right_inv := by decide

/-- Swap the two triangles. -/
def aut3 : Fin 5 ≃ Fin 5 where
  toFun := ![0, 3, 4, 1, 2]
  invFun := ![0, 3, 4, 1, 2]
  left_inv := by decide
  right_inv := by decide

/-- Swap the two triangles and the endpoints of one outer edge. -/
def aut4 : Fin 5 ≃ Fin 5 where
  toFun := ![0, 4, 3, 1, 2]
  invFun := ![0, 3, 4, 2, 1]
  left_inv := by decide
  right_inv := by decide

def autIso2 : bowtie ≃g bowtie where
  toEquiv := aut2
  map_rel_iff' := by intro a b; revert a b; decide

def autIso3 : bowtie ≃g bowtie where
  toEquiv := aut3
  map_rel_iff' := by intro a b; revert a b; decide

def autIso4 : bowtie ≃g bowtie where
  toEquiv := aut4
  map_rel_iff' := by intro a b; revert a b; decide

/-- **The degree may sit at the second vertex of the same outer edge.** -/
theorem integral_outer2 (W : Graphon Ω μ) :
    (∫ y, graphWeight bowtie W y * degree W (y 1)
        ∂assignmentMeasure (Fin 5) μ) =
      ∫ y, graphWeight bowtie W y * degree W (y 2)
        ∂assignmentMeasure (Fin 5) μ := by
  rw [integral_assignment_perm aut2
    (fun y ↦ graphWeight bowtie W y * degree W (y 1))]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only []
  have hw : graphWeight bowtie W (fun v ↦ y (aut2 v)) = graphWeight bowtie W y :=
    graphWeight_iso W autIso2 y
  rw [hw, show (aut2 1 : Fin 5) = 2 by decide]

/-- **The degree may sit on the other triangle.** -/
theorem integral_outer3 (W : Graphon Ω μ) :
    (∫ y, graphWeight bowtie W y * degree W (y 1)
        ∂assignmentMeasure (Fin 5) μ) =
      ∫ y, graphWeight bowtie W y * degree W (y 3)
        ∂assignmentMeasure (Fin 5) μ := by
  rw [integral_assignment_perm aut3
    (fun y ↦ graphWeight bowtie W y * degree W (y 1))]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only []
  have hw : graphWeight bowtie W (fun v ↦ y (aut3 v)) = graphWeight bowtie W y :=
    graphWeight_iso W autIso3 y
  rw [hw, show (aut3 1 : Fin 5) = 3 by decide]

/-- **The degree may sit at the fourth outer vertex.** -/
theorem integral_outer4 (W : Graphon Ω μ) :
    (∫ y, graphWeight bowtie W y * degree W (y 1)
        ∂assignmentMeasure (Fin 5) μ) =
      ∫ y, graphWeight bowtie W y * degree W (y 4)
        ∂assignmentMeasure (Fin 5) μ := by
  rw [integral_assignment_perm aut4
    (fun y ↦ graphWeight bowtie W y * degree W (y 1))]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only []
  have hw : graphWeight bowtie W (fun v ↦ y (aut4 v)) = graphWeight bowtie W y :=
    graphWeight_iso W autIso4 y
  rw [hw, show (aut4 1 : Fin 5) = 4 by decide]

/-! ### The outer arithmetic–geometric mean step and the factorisation -/

/-- Four-term arithmetic–geometric mean at the outer orbit. -/
theorem prod_outer_rootDegree (W : Graphon Ω μ) (a b c d : Ω) :
    rootDegree W 4 a * rootDegree W 4 b * rootDegree W 4 c * rootDegree W 4 d ≤
      ((4 : ℝ))⁻¹ * degree W a + ((4 : ℝ))⁻¹ * degree W b +
        ((4 : ℝ))⁻¹ * degree W c + ((4 : ℝ))⁻¹ * degree W d := by
  set z : Fin 4 → ℝ := ![degree W a, degree W b, degree W c, degree W d] with hz
  have hz0 : ∀ i ∈ (univ : Finset (Fin 4)), 0 ≤ z i := by
    intro i _
    fin_cases i <;> exact degree_nonneg W _
  have hagm := Real.geom_mean_le_arith_mean_weighted (univ : Finset (Fin 4))
    (fun _ ↦ ((4 : ℝ))⁻¹) z (fun i _ ↦ by norm_num)
    (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num) hz0
  refine le_trans (le_of_eq ?_) (le_of_le_of_eq hagm ?_)
  · rw [Fin.prod_univ_four]
    simp only [hz, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, rootDegree]
    norm_num
  · rw [Fin.sum_univ_four]
    simp only [hz, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]

section Factor

variable (W : Graphon Ω μ)

private lemma meas_outer : Measurable fun y : Fin 5 → Ω ↦
    (rootDegree W 4 (y 1) * rootDegree W 4 (y 2) * rootDegree W 4 (y 3) *
      rootDegree W 4 (y 4)) *
      (W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) * W (y 0) (y 3) *
        W (y 0) (y 4) * W (y 3) (y 4)) :=
  ((((measurable_rootDegree W).comp (measurable_pi_apply 1)).mul
    ((measurable_rootDegree W).comp (measurable_pi_apply 2))).mul
    ((measurable_rootDegree W).comp (measurable_pi_apply 3))).mul
    ((measurable_rootDegree W).comp (measurable_pi_apply 4)) |>.mul
    (((((measurable_coord_pair W 0 1).mul (measurable_coord_pair W 0 2)).mul
      (measurable_coord_pair W 1 2)).mul (measurable_coord_pair W 0 3)).mul
      (measurable_coord_pair W 0 4) |>.mul (measurable_coord_pair W 3 4))

private lemma bdd_outer (y : Fin 5 → Ω) :
    |(rootDegree W 4 (y 1) * rootDegree W 4 (y 2) * rootDegree W 4 (y 3) *
      rootDegree W 4 (y 4)) *
      (W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) * W (y 0) (y 3) *
        W (y 0) (y 4) * W (y 3) (y 4))| ≤ 1 := by
  have hr0 : 0 ≤ rootDegree W 4 (y 1) * rootDegree W 4 (y 2) *
      rootDegree W 4 (y 3) * rootDegree W 4 (y 4) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_ <;>
      exact rootDegree_nonneg W _
  have hr1 : rootDegree W 4 (y 1) * rootDegree W 4 (y 2) *
      rootDegree W 4 (y 3) * rootDegree W 4 (y 4) ≤ 1 :=
    mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (rootDegree_le_one W _)
      (rootDegree_nonneg W _) (rootDegree_le_one W _)) (rootDegree_nonneg W _)
      (rootDegree_le_one W _)) (rootDegree_nonneg W _) (rootDegree_le_one W _)
  have hw0 : 0 ≤ W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) * W (y 0) (y 3) *
      W (y 0) (y 4) * W (y 3) (y 4) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_) ?_ <;>
      exact W.nonneg _ _
  have hw1 : W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) * W (y 0) (y 3) *
      W (y 0) (y 4) * W (y 3) (y 4) ≤ 1 :=
    mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (mul_le_one₀
      (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _))
      (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _))
      (W.nonneg _ _) (W.le_one _ _)
  rw [abs_of_nonneg (mul_nonneg hr0 hw0)]
  exact mul_le_one₀ hr1 hw0 hw1

/-- **The two triangles factorise**: the outer-weighted bowtie integral is the
integral of the square of `R`. -/
theorem integral_outer_factor :
    (∫ y, (rootDegree W 4 (y 1) * rootDegree W 4 (y 2) * rootDegree W 4 (y 3) *
        rootDegree W 4 (y 4)) * graphWeight bowtie W y
        ∂assignmentMeasure (Fin 5) μ) = ∫ x, pairTri W x ^ 2 ∂μ := by
  rw [integral_congr_ae (ae_of_all _ fun y ↦ by rw [graphWeight_bowtie]),
    integral_assignment_fin_five
      (g := fun a0 a1 a2 a3 a4 ↦
        (rootDegree W 4 a1 * rootDegree W 4 a2 * rootDegree W 4 a3 *
          rootDegree W 4 a4) *
          (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a0 a4 * W a3 a4))
      (meas_outer W) (bdd_outer W)]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  -- the second triangle integrates to `R(a0)`
  have hinner : ∀ a1 a2 : Ω,
      (∫ a3, ∫ a4, (rootDegree W 4 a1 * rootDegree W 4 a2 * rootDegree W 4 a3 *
          rootDegree W 4 a4) *
          (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a0 a4 * W a3 a4)
          ∂μ ∂μ) =
        ((W a0 a1 * W a0 a2 * W a1 a2) *
          (rootDegree W 4 a1 * rootDegree W 4 a2)) * pairTri W a0 := by
    intro a1 a2
    have h4 : ∀ a3 : Ω,
        (∫ a4, (rootDegree W 4 a1 * rootDegree W 4 a2 * rootDegree W 4 a3 *
            rootDegree W 4 a4) *
            (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a0 a4 * W a3 a4) ∂μ) =
          ((W a0 a1 * W a0 a2 * W a1 a2) *
            (rootDegree W 4 a1 * rootDegree W 4 a2)) *
            ∫ a4, W a0 a3 * W a0 a4 * W a3 a4 * rootDegree W 4 a3 *
              rootDegree W 4 a4 ∂μ := by
      intro a3
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun a4 ↦ by ring)
    rw [integral_congr_ae (ae_of_all _ h4), integral_const_mul, ← pairTri]
  rw [integral_congr_ae (ae_of_all _ fun a1 ↦
    integral_congr_ae (ae_of_all _ (hinner a1)))]
  -- and the first triangle does too
  have hfirst : (∫ a1, ∫ a2,
      ((W a0 a1 * W a0 a2 * W a1 a2) *
        (rootDegree W 4 a1 * rootDegree W 4 a2)) * pairTri W a0 ∂μ ∂μ) =
      pairTri W a0 * pairTri W a0 := by
    have h2 : ∀ a1 : Ω,
        (∫ a2, ((W a0 a1 * W a0 a2 * W a1 a2) *
            (rootDegree W 4 a1 * rootDegree W 4 a2)) * pairTri W a0 ∂μ) =
          pairTri W a0 * ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 *
            rootDegree W 4 a1 * rootDegree W 4 a2 ∂μ := by
      intro a1
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun a2 ↦ by ring)
    rw [integral_congr_ae (ae_of_all _ h2), integral_const_mul, ← pairTri]
  rw [hfirst, sq]

/-- **The outer symmetrisation.** -/
theorem integral_outer_le :
    (∫ y, (rootDegree W 4 (y 1) * rootDegree W 4 (y 2) * rootDegree W 4 (y 3) *
        rootDegree W 4 (y 4)) * graphWeight bowtie W y
        ∂assignmentMeasure (Fin 5) μ) ≤
      ∫ y, graphWeight bowtie W y * degree W (y 1)
        ∂assignmentMeasure (Fin 5) μ := by
  set ν := assignmentMeasure (Fin 5) μ with hν
  have hdeg : ∀ v : Fin 5, Integrable
      (fun y : Fin 5 → Ω ↦ graphWeight bowtie W y * degree W (y v)) ν := by
    intro v
    refine integrable_of_bounded (C := 1)
      ((measurable_graphWeight bowtie W).mul
        ((measurable_degree W).comp (measurable_pi_apply v))) fun y ↦ ?_
    rw [abs_of_nonneg (mul_nonneg (graphWeight_nonneg _ W y) (degree_nonneg W _))]
    exact mul_le_one₀ (graphWeight_le_one _ W y) (degree_nonneg W _)
      (degree_le_one W _)
  have hleft : Integrable (fun y : Fin 5 → Ω ↦
      (rootDegree W 4 (y 1) * rootDegree W 4 (y 2) * rootDegree W 4 (y 3) *
        rootDegree W 4 (y 4)) * graphWeight bowtie W y) ν := by
    refine integrable_of_bounded (C := 1) ?_ fun y ↦ ?_
    · exact ((((measurable_rootDegree W).comp (measurable_pi_apply 1)).mul
        ((measurable_rootDegree W).comp (measurable_pi_apply 2))).mul
        ((measurable_rootDegree W).comp (measurable_pi_apply 3))).mul
        ((measurable_rootDegree W).comp (measurable_pi_apply 4)) |>.mul
        (measurable_graphWeight bowtie W)
    · have hr0 : 0 ≤ rootDegree W 4 (y 1) * rootDegree W 4 (y 2) *
          rootDegree W 4 (y 3) * rootDegree W 4 (y 4) := by
        refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_ <;>
          exact rootDegree_nonneg W _
      have hr1 : rootDegree W 4 (y 1) * rootDegree W 4 (y 2) *
          rootDegree W 4 (y 3) * rootDegree W 4 (y 4) ≤ 1 :=
        mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (rootDegree_le_one W _)
          (rootDegree_nonneg W _) (rootDegree_le_one W _)) (rootDegree_nonneg W _)
          (rootDegree_le_one W _)) (rootDegree_nonneg W _) (rootDegree_le_one W _)
      rw [abs_of_nonneg (mul_nonneg hr0 (graphWeight_nonneg _ W y))]
      exact mul_le_one₀ hr1 (graphWeight_nonneg _ W y) (graphWeight_le_one _ W y)
  have hright : Integrable (fun y : Fin 5 → Ω ↦
      ((4 : ℝ))⁻¹ * (graphWeight bowtie W y * degree W (y 1)) +
      ((4 : ℝ))⁻¹ * (graphWeight bowtie W y * degree W (y 2)) +
      ((4 : ℝ))⁻¹ * (graphWeight bowtie W y * degree W (y 3)) +
      ((4 : ℝ))⁻¹ * (graphWeight bowtie W y * degree W (y 4))) ν :=
    ((((hdeg 1).const_mul _).add ((hdeg 2).const_mul _)).add
      ((hdeg 3).const_mul _)).add ((hdeg 4).const_mul _)
  have hstep : (∫ y, (rootDegree W 4 (y 1) * rootDegree W 4 (y 2) *
      rootDegree W 4 (y 3) * rootDegree W 4 (y 4)) * graphWeight bowtie W y ∂ν) ≤
      ∫ y, (((4 : ℝ))⁻¹ * (graphWeight bowtie W y * degree W (y 1)) +
        ((4 : ℝ))⁻¹ * (graphWeight bowtie W y * degree W (y 2)) +
        ((4 : ℝ))⁻¹ * (graphWeight bowtie W y * degree W (y 3)) +
        ((4 : ℝ))⁻¹ * (graphWeight bowtie W y * degree W (y 4))) ∂ν := by
    refine integral_mono hleft hright fun y ↦ ?_
    have hpt := prod_outer_rootDegree W (y 1) (y 2) (y 3) (y 4)
    have hmul := mul_le_mul_of_nonneg_right hpt (graphWeight_nonneg bowtie W y)
    calc (rootDegree W 4 (y 1) * rootDegree W 4 (y 2) * rootDegree W 4 (y 3) *
          rootDegree W 4 (y 4)) * graphWeight bowtie W y
        ≤ (((4 : ℝ))⁻¹ * degree W (y 1) + ((4 : ℝ))⁻¹ * degree W (y 2) +
            ((4 : ℝ))⁻¹ * degree W (y 3) + ((4 : ℝ))⁻¹ * degree W (y 4)) *
            graphWeight bowtie W y := hmul
      _ = _ := by ring
  refine le_trans hstep (le_of_eq ?_)
  have j1 : Integrable (fun y : Fin 5 → Ω ↦
      ((4 : ℝ))⁻¹ * (graphWeight bowtie W y * degree W (y 1))) ν :=
    (hdeg 1).const_mul _
  have j2 : Integrable (fun y : Fin 5 → Ω ↦
      ((4 : ℝ))⁻¹ * (graphWeight bowtie W y * degree W (y 2))) ν :=
    (hdeg 2).const_mul _
  have j3 : Integrable (fun y : Fin 5 → Ω ↦
      ((4 : ℝ))⁻¹ * (graphWeight bowtie W y * degree W (y 3))) ν :=
    (hdeg 3).const_mul _
  have j4 : Integrable (fun y : Fin 5 → Ω ↦
      ((4 : ℝ))⁻¹ * (graphWeight bowtie W y * degree W (y 4))) ν :=
    (hdeg 4).const_mul _
  have e1 := integral_add ((j1.add j2).add j3) j4
  have e2 := integral_add (j1.add j2) j3
  have e3 := integral_add j1 j2
  simp only [Pi.add_apply] at e1 e2 e3
  rw [e1, e2, e3, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, ← integral_outer2 W, ← integral_outer3 W,
    ← integral_outer4 W]
  ring

end Factor

/-! ### The bound -/

/-- **Atlas 119 dominates its target.** -/
theorem bowtieLeaf_bound (W : Graphon Ω μ)
    (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 3 * (2 * cliqueDensity 2 W - 1) ^ 2 ≤
      homDensity bowtieLeaf W := by
  set p := cliqueDensity 2 W with hpdef
  have hp0 : (0 : ℝ) < p := by linarith
  have hM : 0 < rootMean W 6 := rootMean_pos W (by norm_num) hp0
  haveI : IsProbabilityMeasure (rootMeasure W 6) :=
    isProbabilityMeasure_rootMeasure W hM
  set s := cliqueDensity 2 (rootGraphon W 6) with hsdef
  set K := rootMean W 6 ^ 6 with hKdef
  have hK0 : 0 < K := by positivity
  have hKp : K ≤ p := pow_rootMean_le W (by norm_num)
  have hs0 : 0 ≤ s := cliqueDensity_nonneg 2 _
  have hKs : p ^ 8 ≤ K ^ 2 * s ^ 6 := by
    have h := pow_eight_le_pow_rootEdge W
    rw [rootEdge_eq W hM] at h
    calc p ^ 8 ≤ (rootMean W 6 ^ 2 * s) ^ 6 := h
      _ = K ^ 2 * s ^ 6 := by rw [hKdef]; ring
  have hps : p ≤ s := le_biased hp hs0 hK0 hKp hKs
  have hA3 : 0 ≤ s * (2 * s - 1) := by nlinarith [hps, hp]
  -- Goodman on the biased space, transported through the bias
  have hgood : s * (2 * s - 1) ≤ homDensity (⊤ : SimpleGraph (Fin 3))
      (rootGraphon W 6) := K4Tail.goodman (rootGraphon W 6)
  have hbias := integral_rootDegree_prod 3 6 (⊤ : SimpleGraph (Fin 3)) W hM
  have hmid : rootMean W 6 ^ 3 * (s * (2 * s - 1)) ≤ ∫ x, pairTri W x ∂μ := by
    refine le_trans ?_ (integral_prod_rootDegree_le W)
    rw [hbias]
    exact mul_le_mul_of_nonneg_left hgood (by positivity)
  -- square, then undo the factorisation
  have hsq : K * (s * (2 * s - 1)) ^ 2 ≤ ∫ x, pairTri W x ^ 2 ∂μ := by
    calc K * (s * (2 * s - 1)) ^ 2
        = (rootMean W 6 ^ 3 * (s * (2 * s - 1))) ^ 2 := by rw [hKdef]; ring
      _ ≤ (∫ x, pairTri W x ∂μ) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (by positivity) hA3) hmid 2
      _ ≤ ∫ x, pairTri W x ^ 2 ∂μ := sq_integral_pairTri_le W
  have hchain : K * (s * (2 * s - 1)) ^ 2 ≤ homDensity bowtieLeaf W := by
    rw [homDensity_bowtieLeaf W]
    exact le_trans hsq
      (le_trans (le_of_eq (integral_outer_factor W).symm) (integral_outer_le W))
  have hscalar := transfer (p := p) (s := s) (K := K) hp hs0 hK0 hKp hKs
  have hval : p * (p * (2 * p - 1)) ^ 2 = p ^ 3 * (2 * p - 1) ^ 2 := by ring
  linarith [hscalar, hchain, hval]

/-! ### Chromatic data and the catalogue proposition -/

lemma affineProd_119 (z : ℝ) :
    affineProd [0, 1, 1, 1, 2, 2] z = z ^ 3 * (2 * z - 1) ^ 2 := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_cons, affineProd_nil]
  ring

/-- `K₃`, then `3` on the centre `0`, then `4` on the edge `{3,0}`, then the
leaf `5` on the outer vertex `1`. -/
def iso119 :
    attachVertex (attachVertex
      (attachVertex (⊤ : SimpleGraph (Fin 3)) {0}) {none, some 0})
      {some (some 1)} ≃g bowtieLeaf where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom119 : IsChromaticPolynomial bowtieLeaf
    ((([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := bowtieLeaf) iso119
    (isClique_singleton _ (some (some 1)))
    (isChromaticPolynomial_attachVertex (isClique_attach_new {0} (by decide))
      (isChromaticPolynomial_attachVertex (isCliqueTop _)
        (isChromaticPolynomial_top 3)))
  rw [show (({0} : Finset (Fin 3)).card) = 1 from by decide,
    show (({none, some 0} : Finset (Option (Fin 3))).card) = 2 from by decide,
    Finset.card_singleton] at h
  have hpoly :
      ((([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) * ((X - C ((2 : ℕ) : ℝ)) *
        ((X - C ((1 : ℕ) : ℝ)) * ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ)))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count119 (k : ℕ) :
    properAssignmentCount bowtieLeaf k =
      (k - 1) * ((k - 2) * ((k - 1) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := bowtieLeaf) iso119
      (isClique_singleton _ (some (some 1))) k,
    properAssignmentCount_attachVertex (isClique_attach_new {0} (by decide)),
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0} : Finset (Fin 3)).card) = 1 from by decide,
    show (({none, some 0} : Finset (Option (Fin 3))).card) = 2 from by decide,
    Finset.card_singleton]

theorem num119 : IsChromaticNumber bowtieLeaf 3 where
  positive := by rw [count119]; decide
  zero_below k hk := by
    rw [count119]
    interval_cases k <;> decide

/-- **Atlas 119 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_119 : Taeyoung.SatisfiesLowerBound bowtieLeaf := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P =
      (([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := bowtieLeaf) hP chrom119
  have hreq : r = 3 := IsChromaticNumber.unique (H := bowtieLeaf) hr num119
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := bowtieLeaf_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 1, 2, 2] (by norm_num) hone,
      affineProd_119]
    exact hkey

end Taeyoung.Methods.BowtieLeaf
