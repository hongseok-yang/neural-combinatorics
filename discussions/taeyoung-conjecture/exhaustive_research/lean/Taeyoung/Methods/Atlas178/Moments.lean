import Taeyoung.Methods.Atlas178.Link

/-!
# Atlas 178: the two half-degree moments

`notes/atlas178_half_degree_weighted_k4.tex` Lemmas 2.3 and 2.5.  Both
supporting planes of `Atlas178/Scalar.lean` are integrated against `μ`; the
`d - p` and `a - d²` corrections have mean zero, so what survives is a pair of
inequalities between

```
I  = ∫ √d · τ,     I₄ = ∫ √d · κ₄,     T = t(K₃,W).
```

The two conclusions are

```
2I ≥ √p (T + p(2p-1)),     hence   I² ≥ p²(2p-1)T,
I₄ ≥ (3p-2) I.
```

The second plane carries a division by `√d`.  Lean's `x / 0 = 0` is exactly the
note's convention at `d = 0`, where feasibility forces `τ = 0` anyway, so the
degenerate set needs no separate treatment; `halfRatio_le` and
`halfRatio_ge` both hold verbatim there.
-/

open MeasureTheory

namespace Taeyoung.Methods.Atlas178

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link Taeyoung.Methods.K4Tail
  Taeyoung.Methods.CliqueLeaf Taeyoung.Methods.PureChordal
  Taeyoung.Methods.BookTail Taeyoung.Methods.TriangleDensity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The half degree -/

/-- `√d(x)`. -/
noncomputable def sqrtDeg (W : Graphon Ω μ) (x : Ω) : ℝ :=
  Real.sqrt (degree W x)

omit [IsProbabilityMeasure μ] in
lemma sqrtDeg_nonneg (W : Graphon Ω μ) (x : Ω) : 0 ≤ sqrtDeg W x :=
  Real.sqrt_nonneg _

lemma sqrtDeg_sq (W : Graphon Ω μ) (x : Ω) : sqrtDeg W x ^ 2 = degree W x :=
  Real.sq_sqrt (degree_nonneg W x)

lemma sqrtDeg_le_one (W : Graphon Ω μ) (x : Ω) : sqrtDeg W x ≤ 1 := by
  have h := Real.sqrt_le_sqrt (degree_le_one W x)
  rwa [Real.sqrt_one] at h

lemma measurable_sqrtDeg (W : Graphon Ω μ) : Measurable (sqrtDeg W) :=
  Real.continuous_sqrt.measurable.comp (measurable_degree W)

/-- `d ≤ √d` on `[0,1]`, which is what bounds the divided quotients. -/
lemma degree_le_sqrtDeg (W : Graphon Ω μ) (x : Ω) : degree W x ≤ sqrtDeg W x := by
  have h : Real.sqrt (degree W x ^ 2) ≤ Real.sqrt (degree W x) :=
    Real.sqrt_le_sqrt (by nlinarith [degree_nonneg W x, degree_le_one W x])
  rwa [Real.sqrt_sq (degree_nonneg W x)] at h

/-! ### The two half-degree moments -/

/-- `I = ∫ √d · τ`. -/
noncomputable def halfTri (W : Graphon Ω μ) : ℝ :=
  ∫ x, sqrtDeg W x * rootedTriangle W x ∂μ

/-- `I₄ = ∫ √d · κ₄`. -/
noncomputable def halfK4 (W : Graphon Ω μ) : ℝ :=
  ∫ x, sqrtDeg W x * rootedK4 W x ∂μ

lemma integrable_sqrtDeg_mul_rootedTriangle (W : Graphon Ω μ) :
    Integrable (fun x ↦ sqrtDeg W x * rootedTriangle W x) μ :=
  integrable_of_bdd ((measurable_sqrtDeg W).mul (measurable_rootedTriangle W))
    (C := 1) fun x ↦ by
      rw [abs_of_nonneg (mul_nonneg (sqrtDeg_nonneg W x)
        (rootedTriangle_nonneg W x))]
      exact mul_le_one₀ (sqrtDeg_le_one W x) (rootedTriangle_nonneg W x)
        (rootedTriangle_le_one W x)

lemma integrable_sqrtDeg_mul_rootedK4 (W : Graphon Ω μ) :
    Integrable (fun x ↦ sqrtDeg W x * rootedK4 W x) μ :=
  integrable_of_bdd ((measurable_sqrtDeg W).mul (measurable_rootedK4 W))
    (C := 1) fun x ↦ by
      rw [abs_of_nonneg (mul_nonneg (sqrtDeg_nonneg W x) (rootedK4_nonneg W x))]
      exact mul_le_one₀ (sqrtDeg_le_one W x) (rootedK4_nonneg W x)
        (rootedK4_le_one W x)

lemma halfTri_nonneg (W : Graphon Ω μ) : 0 ≤ halfTri W :=
  integral_nonneg fun x ↦
    mul_nonneg (sqrtDeg_nonneg W x) (rootedTriangle_nonneg W x)

/-! ### The first plane, integrated -/

/-- The first supporting plane at a point, with `D = √d` and `r = √p`
substituted. -/
theorem plane_one_pointwise (W : Graphon Ω μ)
    (hp : (2:ℝ)/3 ≤ cliqueDensity 2 W) (x : Ω) :
    2 * Real.sqrt (cliqueDensity 2 W) * rootedTriangle W x
        + 2 * Real.sqrt (cliqueDensity 2 W) * (cliqueDensity 2 W *
          (2 * cliqueDensity 2 W - 1))
        + 3 * Real.sqrt (cliqueDensity 2 W) * (4 * cliqueDensity 2 W - 1) *
          (degree W x - cliqueDensity 2 W)
        + 3 * Real.sqrt (cliqueDensity 2 W) *
          (pathOp W x - degree W x ^ 2) ≤
      4 * (sqrtDeg W x * rootedTriangle W x) := by
  set p := cliqueDensity 2 W with hpdef
  set r := Real.sqrt p with hrdef
  set D := sqrtDeg W x with hDdef
  have hp0 : (0:ℝ) ≤ p := by linarith
  have hr : r ^ 2 = p := Real.sq_sqrt hp0
  have hD : D ^ 2 = degree W x := sqrtDeg_sq W x
  have hD0 : (0:ℝ) ≤ D := sqrtDeg_nonneg W x
  have hD1 : D ≤ 1 := sqrtDeg_le_one W x
  have hr45 : (4:ℝ)/5 ≤ r :=
    four_fifths_le (Real.sqrt_nonneg _) (by rw [hr]; linarith)
  have hg₅ : 0 ≤ rootedTriangle W x - 2 * pathOp W x + r ^ 2 := by
    rw [hr]; linarith [rootedTriangle_ge W x]
  have hg₆ : 0 ≤ rootedTriangle W x - pathOp W x + D ^ 2 - D ^ 4 := by
    have h4 : D ^ 4 = degree W x ^ 2 := by rw [← hD]; ring
    rw [hD, h4]
    linarith [pathOp_sub_le_rootedTriangle W x]
  have hg₈ : 0 ≤ D ^ 4 - rootedTriangle W x := by
    have h4 : D ^ 4 = degree W x ^ 2 := by rw [← hD]; ring
    rw [h4]
    linarith [rootedTriangle_le_sq_degree W x]
  have hres := res₁_nonneg hD0 hD1 hr45 hg₅ hg₆ hg₈
  rw [res₁] at hres
  rw [← hr, ← hD]
  nlinarith [hres, hr, hD]

/-- **The integrated first plane.**  `2I ≥ √p (T + p(2p-1))`. -/
theorem sqrt_mul_le_two_mul_halfTri (W : Graphon Ω μ)
    (hp : (2:ℝ)/3 ≤ cliqueDensity 2 W) :
    Real.sqrt (cliqueDensity 2 W) *
        (cliqueDensity 3 W + cliqueDensity 2 W * (2 * cliqueDensity 2 W - 1)) ≤
      2 * halfTri W := by
  set p := cliqueDensity 2 W with hpdef
  set r := Real.sqrt p with hrdef
  have hd := integrable_degree W
  have hA := integrable_pathOp W
  have hd2 := integrable_degree_pow W 2
  have hτ : Integrable (rootedTriangle W) μ :=
    integrable_of_bdd (measurable_rootedTriangle W) (C := 1) fun x ↦ by
      rw [abs_of_nonneg (rootedTriangle_nonneg W x)]
      exact rootedTriangle_le_one W x
  have i0 : Integrable (fun _ : Ω ↦ 2 * r * (p * (2 * p - 1))
      - 3 * r * (4 * p - 1) * p) μ := integrable_const _
  have i1 : Integrable (fun x : Ω ↦ 2 * r * rootedTriangle W x) μ :=
    hτ.const_mul _
  have i2 : Integrable (fun x : Ω ↦ 3 * r * (4 * p - 1) * degree W x) μ :=
    hd.const_mul _
  have i3 : Integrable (fun x : Ω ↦ 3 * r * pathOp W x) μ := hA.const_mul _
  have i4 : Integrable (fun x : Ω ↦ 3 * r * degree W x ^ 2) μ := hd2.const_mul _
  set F : Ω → ℝ := fun x ↦
    2 * r * rootedTriangle W x + 2 * r * (p * (2 * p - 1))
      + 3 * r * (4 * p - 1) * (degree W x - p)
      + 3 * r * (pathOp W x - degree W x ^ 2) with hFdef
  have hFsplit : ∀ x : Ω, F x =
      (2 * r * (p * (2 * p - 1)) - 3 * r * (4 * p - 1) * p)
        + 2 * r * rootedTriangle W x + 3 * r * (4 * p - 1) * degree W x
        + 3 * r * pathOp W x - 3 * r * degree W x ^ 2 := by
    intro x; simp only [hFdef]; ring
  have hFint : Integrable F μ := by
    refine Integrable.congr ?_ (ae_of_all _ fun x ↦ (hFsplit x).symm)
    exact ((((i0.add i1).add i2).add i3).sub i4)
  have hFval : (∫ x, F x ∂μ) = 2 * r * cliqueDensity 3 W
      + 2 * r * (p * (2 * p - 1)) := by
    have e1 := integral_sub (((i0.add i1).add i2).add i3) i4
    have e2 := integral_add ((i0.add i1).add i2) i3
    have e3 := integral_add (i0.add i1) i2
    have e4 := integral_add i0 i1
    simp only [Pi.add_apply] at e1 e2 e3 e4
    rw [integral_congr_ae (ae_of_all _ hFsplit), e1, e2, e3, e4, integral_const,
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_degree, integral_pathOp, moment,
      ← cliqueDensity_three_eq_integral_rootedTriangle]
    simp
    ring
  have hmono : (∫ x, F x ∂μ) ≤ ∫ x, 4 * (sqrtDeg W x * rootedTriangle W x) ∂μ :=
    integral_mono hFint ((integrable_sqrtDeg_mul_rootedTriangle W).const_mul _)
      fun x ↦ plane_one_pointwise W hp x
  rw [hFval, integral_const_mul] at hmono
  rw [halfTri]
  linarith [hmono]

/-- **The half-degree triangle moment.**  `I² ≥ p²(2p-1)T`. -/
theorem sq_halfTri_ge (W : Graphon Ω μ) (hp : (2:ℝ)/3 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 2 * (2 * cliqueDensity 2 W - 1) * cliqueDensity 3 W ≤
      halfTri W ^ 2 := by
  set p := cliqueDensity 2 W with hpdef
  set T := cliqueDensity 3 W with hTdef
  have hp0 : (0:ℝ) ≤ p := by linarith
  have hr : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0
  have hgood : p * (2 * p - 1) ≤ T := by
    rw [hpdef, hTdef]; exact goodman_triangle_bound W (by rw [← hpdef]; linarith)
  have hkey := sqrt_mul_le_two_mul_halfTri W hp
  rw [← hpdef, ← hTdef] at hkey
  have hI0 : 0 ≤ halfTri W := halfTri_nonneg W
  have hpos : (0:ℝ) ≤ T + p * (2 * p - 1) := by nlinarith [hgood]
  -- squaring the integrated plane
  have hsq : (Real.sqrt p * (T + p * (2 * p - 1))) ^ 2 ≤ (2 * halfTri W) ^ 2 := by
    apply pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) hpos) hkey
  have hexp : (Real.sqrt p * (T + p * (2 * p - 1))) ^ 2 =
      p * (T + p * (2 * p - 1)) ^ 2 := by
    rw [mul_pow, hr]
  rw [hexp] at hsq
  nlinarith [hsq, hgood, hp0, sq_nonneg (T - p * (2 * p - 1))]

/-! ### The second plane, integrated

The second plane is stated in the note with a quotient by `√d`.  Lean's
`x / 0 = 0` reproduces the note's convention at `d = 0`, where `τ ≤ d²` forces
`τ = 0`, so both sides vanish there and no separate case is needed in the
statement. -/

/-- `G(x) = τ(2τ - d²)/√d`, the divided form of Goodman inside the link. -/
noncomputable def halfGoodman (W : Graphon Ω μ) (x : Ω) : ℝ :=
  rootedTriangle W x * (2 * rootedTriangle W x - degree W x ^ 2) / sqrtDeg W x

lemma measurable_halfGoodman (W : Graphon Ω μ) : Measurable (halfGoodman W) :=
  ((measurable_rootedTriangle W).mul
    ((measurable_const.mul (measurable_rootedTriangle W)).sub
      ((measurable_degree W).pow_const 2))).div (measurable_sqrtDeg W)

/-- The numerator is dominated by `√d`, so `|G| ≤ 1`. -/
lemma abs_halfGoodman_le_one (W : Graphon Ω μ) (x : Ω) :
    |halfGoodman W x| ≤ 1 := by
  have hd0 := degree_nonneg W x
  have hd1 := degree_le_one W x
  have hτ0 := rootedTriangle_nonneg W x
  have hτ2 := rootedTriangle_le_sq_degree W x
  have hnum : |rootedTriangle W x * (2 * rootedTriangle W x - degree W x ^ 2)| ≤
      sqrtDeg W x := by
    have hd4 : degree W x ^ 4 ≤ degree W x := by
      have := pow_le_pow_of_le_one hd0 hd1 (by norm_num : 1 ≤ 4)
      simpa using this
    have hconv : rootedTriangle W x * rootedTriangle W x ≤
        degree W x ^ 2 * degree W x ^ 2 :=
      mul_le_mul hτ2 hτ2 hτ0 (by positivity)
    have hcross : rootedTriangle W x * degree W x ^ 2 ≤
        degree W x ^ 2 * degree W x ^ 2 :=
      mul_le_mul_of_nonneg_right hτ2 (by positivity)
    have hprod : 0 ≤ rootedTriangle W x * (degree W x ^ 2 - rootedTriangle W x) :=
      mul_nonneg hτ0 (by linarith)
    have h4 : |rootedTriangle W x * (2 * rootedTriangle W x - degree W x ^ 2)| ≤
        degree W x := by
      rw [abs_le]
      constructor <;> nlinarith [hd4, hconv, hcross, hprod, hτ0, hτ2]
    exact h4.trans (degree_le_sqrtDeg W x)
  rcases eq_or_lt_of_le (sqrtDeg_nonneg W x) with hs0 | hspos
  · rw [halfGoodman, ← hs0, div_zero, abs_zero]; norm_num
  · rw [halfGoodman, abs_div, abs_of_pos hspos, div_le_one hspos]
    exact hnum

lemma integrable_halfGoodman (W : Graphon Ω μ) :
    Integrable (halfGoodman W) μ :=
  integrable_of_bdd (measurable_halfGoodman W) (abs_halfGoodman_le_one W)

/-- **Goodman inside the link, divided.**  `G(x) ≤ √d(x)·κ₄(x)`. -/
theorem halfGoodman_le (W : Graphon Ω μ) (x : Ω) :
    halfGoodman W x ≤ sqrtDeg W x * rootedK4 W x := by
  rcases eq_or_lt_of_le (sqrtDeg_nonneg W x) with hs0 | hspos
  · have hτ : rootedTriangle W x = 0 := by
      have hd : degree W x = 0 := by
        have := sqrtDeg_sq W x
        rw [← hs0] at this; simpa using this.symm
      refine le_antisymm ?_ (rootedTriangle_nonneg W x)
      have := rootedTriangle_le_sq_degree W x
      rw [hd] at this; simpa using this
    rw [halfGoodman, ← hs0, div_zero]
    simp
  · rw [halfGoodman, div_le_iff₀ hspos]
    have hsq : sqrtDeg W x * rootedK4 W x * sqrtDeg W x =
        degree W x * rootedK4 W x := by
      calc sqrtDeg W x * rootedK4 W x * sqrtDeg W x
          = sqrtDeg W x ^ 2 * rootedK4 W x := by ring
        _ = degree W x * rootedK4 W x := by rw [sqrtDeg_sq W x]
    rw [hsq]
    exact rootedTriangle_mul_le_degree_mul_rootedK4 W x

/-- The second supporting plane at a point, in divided form. -/
theorem plane_two_pointwise (W : Graphon Ω μ)
    (hp : (2:ℝ)/3 ≤ cliqueDensity 2 W) (x : Ω) :
    3 * cliqueDensity 2 W * Real.sqrt (cliqueDensity 2 W) *
          (2 * cliqueDensity 2 W - 1) * (degree W x - cliqueDensity 2 W)
        + 2 * Real.sqrt (cliqueDensity 2 W) * (2 * cliqueDensity 2 W - 1) *
          (pathOp W x - degree W x ^ 2) ≤
      halfGoodman W x
        - (3 * cliqueDensity 2 W - 2) * (sqrtDeg W x * rootedTriangle W x) := by
  set p := cliqueDensity 2 W with hpdef
  set r := Real.sqrt p with hrdef
  set D := sqrtDeg W x with hDdef
  have hp0 : (0:ℝ) ≤ p := by linarith
  have hr : r ^ 2 = p := Real.sq_sqrt hp0
  have hr0 : (0:ℝ) ≤ r := Real.sqrt_nonneg _
  have hD : D ^ 2 = degree W x := sqrtDeg_sq W x
  have hD4 : D ^ 4 = degree W x ^ 2 := by rw [← hD]; ring
  have hD0 : (0:ℝ) ≤ D := sqrtDeg_nonneg W x
  have hD1 : D ≤ 1 := sqrtDeg_le_one W x
  have hr45 : (4:ℝ)/5 ≤ r :=
    four_fifths_le (Real.sqrt_nonneg _) (by rw [hr]; linarith)
  have hr1 : r ≤ 1 := by
    nlinarith [hr, cliqueDensity_le_one 2 W, hr0, hp0]
  have hrp : (2:ℝ)/3 ≤ r ^ 2 := by rw [hr]; linarith
  have hg₆ : 0 ≤ rootedTriangle W x - pathOp W x + D ^ 2 - D ^ 4 := by
    rw [hD, hD4]; linarith [pathOp_sub_le_rootedTriangle W x]
  have hres := res₂_nonneg hD0 hD1 hr45 hr1 hrp hg₆
  rw [res₂] at hres
  rcases eq_or_lt_of_le hD0 with hs0 | hspos
  · -- the degenerate set: `d = 0` forces `a = τ = 0`
    have hd : degree W x = 0 := by rw [← hD, ← hs0]; ring
    have hτ : rootedTriangle W x = 0 := by
      refine le_antisymm ?_ (rootedTriangle_nonneg W x)
      have := rootedTriangle_le_sq_degree W x
      rw [hd] at this; simpa using this
    have hA : pathOp W x = 0 :=
      le_antisymm (by rw [← hd]; exact pathOp_le_degree W x) (pathOp_nonneg W x)
    have hc3 : (0:ℝ) ≤ 2 * p - 1 := by linarith
    rw [halfGoodman, ← hDdef, ← hs0, div_zero, hd, hτ, hA]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hp0 hr0) hc3) hp0]
  · -- `d > 0`: divide the plane by `√d`
    have hne : D ≠ 0 := ne_of_gt hspos
    have hdD : degree W x = D ^ 2 := (sqrtDeg_sq W x).symm
    have hsplit : halfGoodman W x - (3 * p - 2) * (D * rootedTriangle W x)
        = rootedTriangle W x *
          (2 * rootedTriangle W x - D ^ 4 - (3 * p - 2) * D ^ 2) / D := by
      rw [halfGoodman, ← hDdef, hdD]
      field_simp
      -- `field_simp` closes it
    rw [hdD, hsplit, le_div_iff₀ hspos, ← hr]
    nlinarith [hres]

/-- **The half-degree adjacent-clique ratio.**  `I₄ ≥ (3p-2)·I`. -/
theorem halfK4_ge (W : Graphon Ω μ) (hp : (2:ℝ)/3 ≤ cliqueDensity 2 W) :
    (3 * cliqueDensity 2 W - 2) * halfTri W ≤ halfK4 W := by
  set p := cliqueDensity 2 W with hpdef
  set r := Real.sqrt p with hrdef
  have hd := integrable_degree W
  have hA := integrable_pathOp W
  have hd2 := integrable_degree_pow W 2
  have i0 : Integrable (fun _ : Ω ↦
      -(3 * p * r * (2 * p - 1) * p)) μ := integrable_const _
  have i1 : Integrable (fun x : Ω ↦
      3 * p * r * (2 * p - 1) * degree W x) μ := hd.const_mul _
  have i2 : Integrable (fun x : Ω ↦
      2 * r * (2 * p - 1) * pathOp W x) μ := hA.const_mul _
  have i3 : Integrable (fun x : Ω ↦
      2 * r * (2 * p - 1) * degree W x ^ 2) μ := hd2.const_mul _
  set G : Ω → ℝ := fun x ↦
    3 * p * r * (2 * p - 1) * (degree W x - p)
      + 2 * r * (2 * p - 1) * (pathOp W x - degree W x ^ 2) with hGdef
  have hGsplit : ∀ x : Ω, G x =
      -(3 * p * r * (2 * p - 1) * p) + 3 * p * r * (2 * p - 1) * degree W x
        + 2 * r * (2 * p - 1) * pathOp W x
        - 2 * r * (2 * p - 1) * degree W x ^ 2 := by
    intro x; simp only [hGdef]; ring
  have hGint : Integrable G μ := by
    refine Integrable.congr ?_ (ae_of_all _ fun x ↦ (hGsplit x).symm)
    exact (((i0.add i1).add i2).sub i3)
  have hGval : (∫ x, G x ∂μ) = 0 := by
    have e1 := integral_sub ((i0.add i1).add i2) i3
    have e2 := integral_add (i0.add i1) i2
    have e3 := integral_add i0 i1
    simp only [Pi.add_apply] at e1 e2 e3
    rw [integral_congr_ae (ae_of_all _ hGsplit), e1, e2, e3, integral_const,
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_degree, integral_pathOp, moment]
    simp
    ring
  have hRint : Integrable (fun x ↦ halfGoodman W x
      - (3 * p - 2) * (sqrtDeg W x * rootedTriangle W x)) μ :=
    (integrable_halfGoodman W).sub
      ((integrable_sqrtDeg_mul_rootedTriangle W).const_mul _)
  have hmono : (∫ x, G x ∂μ) ≤ ∫ x, halfGoodman W x
      - (3 * p - 2) * (sqrtDeg W x * rootedTriangle W x) ∂μ :=
    integral_mono hGint hRint fun x ↦ plane_two_pointwise W hp x
  rw [hGval, integral_sub (integrable_halfGoodman W)
    ((integrable_sqrtDeg_mul_rootedTriangle W).const_mul _),
    integral_const_mul] at hmono
  have hle : (∫ x, halfGoodman W x ∂μ) ≤ halfK4 W := by
    rw [halfK4]
    exact integral_mono (integrable_halfGoodman W)
      (integrable_sqrtDeg_mul_rootedK4 W) fun x ↦ halfGoodman_le W x
  rw [halfTri]
  linarith [hmono, hle]

end Taeyoung.Methods.Atlas178
