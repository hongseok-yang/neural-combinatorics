import Taeyoung.Methods.Link.PageOp

/-!
# Atlas 148: the geometric mean of the two spine degrees

The high-density argument of
`notes/atlas148_paw_bias_hilbert_projection.tex` runs on the kernel

```
Z(x,y) = √(d(x)d(y)),
```

for three reasons: `Z² = d(x)d(y)` makes the `L`-term exact, `Z ≤ (d(x)+d(y))/2`
makes the `G`-term an arithmetic--geometric mean step, and `S ≤ Z` is
Cauchy--Schwarz.  Keeping `d(x)` and `d(y)` separate instead does **not** work:
the note's supporting line is violated at `p = 3/5`, `d(x) = 0.28`, `d(y) = 1`.

The one substantial fact is the edge geometric mean

```
∫∫ W(x,y)·Z(x,y) dμ² ≥ p²,
```

sharp at every constant graphon.  The note proves it by two Cauchy--Schwarz
steps through `∫∫ W/Z ≤ 1`, defining the quotient to be zero on zero-degree
fibres.  That quotient is unbounded, so a direct transcription would owe an
integrability argument.  Instead the proof below shifts the degree by `ε > 0`,

```
g_ε(x) = (√(d(x)+ε))⁻¹  ≤  (√ε)⁻¹,
```

which is bounded, needs no case split on zero degrees, and turns both steps
into the project's weighted Cauchy--Schwarz.  The shift is removed by
`√((a+ε)(b+ε)) ≤ √(ab) + √(3ε)` and `le_of_forall_pos_le_add`, the same device
that closes `Methods/OddWalk/Limit.lean`.
-/

open MeasureTheory

namespace Taeyoung.Methods.Atlas148

open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Two elementary square-root facts -/

lemma sqrt_add_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.sqrt (u + v) ≤ Real.sqrt u + Real.sqrt v := by
  have h : u + v ≤ (Real.sqrt u + Real.sqrt v) ^ 2 := by
    have h1 : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu
    have h2 : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv
    nlinarith [Real.sqrt_nonneg u, Real.sqrt_nonneg v]
  calc Real.sqrt (u + v) ≤ Real.sqrt ((Real.sqrt u + Real.sqrt v) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = Real.sqrt u + Real.sqrt v := Real.sqrt_sq (by positivity)

/-! ### Pairing the edge against a function of one endpoint -/

lemma integral_edge_left (W : Graphon Ω μ) {h : Ω → ℝ} (hm : Measurable h)
    {C : ℝ} (hb : ∀ x, |h x| ≤ C) :
    (∫ q, W q.1 q.2 * h q.1 ∂(μ.prod μ)) = ∫ x, h x * degree W x ∂μ := by
  have hbdd : ∀ q : Ω × Ω, |W q.1 q.2 * h q.1| ≤ C := by
    intro q
    rw [abs_mul, abs_of_nonneg (W.nonneg q.1 q.2)]
    calc W q.1 q.2 * |h q.1| ≤ 1 * |h q.1| :=
          mul_le_mul_of_nonneg_right (W.le_one _ _) (abs_nonneg _)
      _ = |h q.1| := one_mul _
      _ ≤ C := hb q.1
  have hi : Integrable (Function.uncurry fun x y ↦ W x y * h x) (μ.prod μ) :=
    integrable_prod_of_bdd (W.measurable.mul (hm.comp measurable_fst)) hbdd
  rw [← integral_integral hi]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  show (∫ y, W x y * h x ∂μ) = h x * degree W x
  rw [integral_mul_const, integral_edge_right]
  ring

lemma integral_edge_snd (W : Graphon Ω μ) {h : Ω → ℝ} (hm : Measurable h)
    {C : ℝ} (hb : ∀ x, |h x| ≤ C) :
    (∫ q, W q.1 q.2 * h q.2 ∂(μ.prod μ)) = ∫ y, h y * degree W y ∂μ := by
  have hbdd : ∀ q : Ω × Ω, |W q.1 q.2 * h q.2| ≤ C := by
    intro q
    rw [abs_mul, abs_of_nonneg (W.nonneg q.1 q.2)]
    calc W q.1 q.2 * |h q.2| ≤ 1 * |h q.2| :=
          mul_le_mul_of_nonneg_right (W.le_one _ _) (abs_nonneg _)
      _ = |h q.2| := one_mul _
      _ ≤ C := hb q.2
  have hi : Integrable (Function.uncurry fun x y ↦ W x y * h y) (μ.prod μ) :=
    integrable_prod_of_bdd (W.measurable.mul (hm.comp measurable_snd)) hbdd
  rw [← integral_integral hi, integral_integral_swap hi]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  show (∫ x, W x y * h y ∂μ) = h y * degree W y
  rw [integral_mul_const]
  have hsymm : (∫ x, W x y ∂μ) = degree W y := by
    rw [← integral_edge_right W y]
    exact integral_congr_ae (ae_of_all _ fun x ↦ W.symm x y)
  rw [hsymm]
  ring

/-! ### The kernel `Z` -/

/-- `Z(x,y) = √(d(x)d(y))`. -/
noncomputable def geoDeg (W : Graphon Ω μ) (x y : Ω) : ℝ :=
  Real.sqrt (degree W x * degree W y)

lemma geoDeg_nonneg (W : Graphon Ω μ) (x y : Ω) : 0 ≤ geoDeg W x y :=
  Real.sqrt_nonneg _

lemma geoDeg_le_one (W : Graphon Ω μ) (x y : Ω) : geoDeg W x y ≤ 1 := by
  rw [geoDeg, Real.sqrt_le_one]
  exact mul_le_one₀ (degree_le_one W x) (degree_nonneg W y) (degree_le_one W y)

lemma measurable_geoDeg (W : Graphon Ω μ) :
    Measurable fun q : Ω × Ω ↦ geoDeg W q.1 q.2 :=
  Real.continuous_sqrt.measurable.comp
    (((measurable_degree W).comp measurable_fst).mul
      ((measurable_degree W).comp measurable_snd))

/-- **Arithmetic--geometric mean on the spine.**  `2Z ≤ d(x) + d(y)`. -/
lemma two_geoDeg_le (W : Graphon Ω μ) (x y : Ω) :
    2 * geoDeg W x y ≤ degree W x + degree W y := by
  have hx := degree_nonneg W x
  have hy := degree_nonneg W y
  have hmul : geoDeg W x y = Real.sqrt (degree W x) * Real.sqrt (degree W y) := by
    rw [geoDeg, Real.sqrt_mul hx]
  have e1 : Real.sqrt (degree W x) ^ 2 = degree W x := Real.sq_sqrt hx
  have e2 : Real.sqrt (degree W y) ^ 2 = degree W y := Real.sq_sqrt hy
  rw [hmul]
  nlinarith [sq_nonneg (Real.sqrt (degree W x) - Real.sqrt (degree W y)), e1, e2]

/-- **The codegree is at most the geometric mean.**  `S ≤ Z`, from `S² ≤ d(x)d(y)`:
weighted Cauchy--Schwarz with weight `W(x,·)` and `η = W(y,·)`, then
`W(x,z)W(y,z)² ≤ W(y,z)`. -/
lemma pageOp_zero_le_geoDeg (W : Graphon Ω μ) (x y : Ω) :
    pageOp W 0 x y ≤ geoDeg W x y := by
  have hrowx : Measurable fun z ↦ W x z := measurable_row W.measurable x
  have hrowy : Measurable fun z ↦ W y z := measurable_row W.measurable y
  have hAx : Integrable (fun z ↦ W x z) μ :=
    integrable_of_bdd hrowx (C := 1) fun z ↦ by
      rw [abs_of_nonneg (W.nonneg x z)]; exact W.le_one x z
  have hAy : Integrable (fun z ↦ W y z) μ :=
    integrable_of_bdd hrowy (C := 1) fun z ↦ by
      rw [abs_of_nonneg (W.nonneg y z)]; exact W.le_one y z
  have hAη : Integrable (fun z ↦ W x z * W y z) μ :=
    integrable_of_bdd (hrowx.mul hrowy) (C := 1) fun z ↦ by
      rw [abs_of_nonneg (mul_nonneg (W.nonneg x z) (W.nonneg y z))]
      exact mul_le_one₀ (W.le_one x z) (W.nonneg y z) (W.le_one y z)
  have hAη2 : Integrable (fun z ↦ W x z * W y z ^ 2) μ :=
    integrable_of_bdd (hrowx.mul (hrowy.pow_const 2)) (C := 1) fun z ↦ by
      have h0 : 0 ≤ W x z * W y z ^ 2 := mul_nonneg (W.nonneg x z) (sq_nonneg _)
      rw [abs_of_nonneg h0]
      exact mul_le_one₀ (W.le_one x z) (sq_nonneg _)
        (pow_le_one₀ (W.nonneg y z) (W.le_one y z))
  have hcs := integral_mul_sq_le_integral_mul_integral_mul_sq
    (A := fun z ↦ W x z) (η := fun z ↦ W y z) hAx hAη hAη2 fun z ↦ W.nonneg x z
  have hbound : (∫ z, W x z * W y z ^ 2 ∂μ) ≤ degree W y := by
    refine le_trans (integral_mono hAη2 hAy fun z ↦ ?_) (le_of_eq rfl)
    nlinarith [W.nonneg x z, W.le_one x z, W.nonneg y z, W.le_one y z]
  have hsq : pageOp W 0 x y ^ 2 ≤ degree W x * degree W y := by
    rw [pageOp_zero_eq]
    calc (∫ z, W x z * W y z ∂μ) ^ 2
        ≤ (∫ z, W x z ∂μ) * ∫ z, W x z * W y z ^ 2 ∂μ := hcs
      _ ≤ degree W x * degree W y :=
          mul_le_mul_of_nonneg_left hbound (degree_nonneg W x)
  calc pageOp W 0 x y = Real.sqrt (pageOp W 0 x y ^ 2) :=
        (Real.sqrt_sq (pageOp_nonneg W le_rfl x y)).symm
    _ ≤ Real.sqrt (degree W x * degree W y) := Real.sqrt_le_sqrt hsq

/-! ### The shifted inverse root -/

section Shift

variable (W : Graphon Ω μ) {ε : ℝ}

/-- `g_ε(x) = (√(d(x)+ε))⁻¹`, bounded by `(√ε)⁻¹`. -/
noncomputable def shiftInv (W : Graphon Ω μ) (ε : ℝ) (x : Ω) : ℝ :=
  (Real.sqrt (degree W x + ε))⁻¹

lemma sqrt_shift_pos (hε : 0 < ε) (x : Ω) : 0 < Real.sqrt (degree W x + ε) :=
  Real.sqrt_pos.mpr (by linarith [degree_nonneg W x])

lemma shiftInv_pos (hε : 0 < ε) (x : Ω) : 0 < shiftInv W ε x :=
  inv_pos.mpr (sqrt_shift_pos W hε x)

lemma shiftInv_le (hε : 0 < ε) (x : Ω) : shiftInv W ε x ≤ (Real.sqrt ε)⁻¹ := by
  refine inv_anti₀ (Real.sqrt_pos.mpr hε) (Real.sqrt_le_sqrt ?_)
  linarith [degree_nonneg W x]

lemma measurable_shiftInv : Measurable (shiftInv W ε) :=
  (Real.continuous_sqrt.measurable.comp
    ((measurable_degree W).add measurable_const)).inv

lemma shiftInv_mul_sqrt (hε : 0 < ε) (x : Ω) :
    shiftInv W ε x * Real.sqrt (degree W x + ε) = 1 :=
  inv_mul_cancel₀ (ne_of_gt (sqrt_shift_pos W hε x))

lemma sq_shiftInv_mul (hε : 0 < ε) (x : Ω) :
    shiftInv W ε x ^ 2 * (degree W x + ε) = 1 := by
  have h := shiftInv_mul_sqrt W hε x
  have hs : Real.sqrt (degree W x + ε) ^ 2 = degree W x + ε :=
    Real.sq_sqrt (by linarith [degree_nonneg W x])
  calc shiftInv W ε x ^ 2 * (degree W x + ε)
      = (shiftInv W ε x * Real.sqrt (degree W x + ε)) ^ 2 := by rw [mul_pow, hs]
    _ = 1 := by rw [h, one_pow]

lemma sq_shiftInv_mul_degree_le (hε : 0 < ε) (x : Ω) :
    shiftInv W ε x ^ 2 * degree W x ≤ 1 := by
  have h := sq_shiftInv_mul W hε x
  nlinarith [sq_nonneg (shiftInv W ε x), le_of_lt hε,
    mul_nonneg (sq_nonneg (shiftInv W ε x)) (le_of_lt hε)]

/-! ### The two shifted integrals -/

/-- `∫∫ W·g_ε(x)g_ε(y) ≤ 1`, by arithmetic--geometric mean and Fubini. -/
lemma integral_edge_shiftInv_le (hε : 0 < ε) :
    (∫ q, W q.1 q.2 * (shiftInv W ε q.1 * shiftInv W ε q.2) ∂(μ.prod μ)) ≤ 1 := by
  set c := (Real.sqrt ε)⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  have hgb : ∀ x, |shiftInv W ε x| ≤ c := fun x ↦ by
    rw [abs_of_nonneg (shiftInv_pos W hε x).le]; exact shiftInv_le W hε x
  have hg2b : ∀ x, |shiftInv W ε x ^ 2| ≤ c ^ 2 := fun x ↦ by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (shiftInv_pos W hε x).le (shiftInv_le W hε x) 2
  have hm := measurable_shiftInv W (ε := ε)
  -- the three integrands
  have hiP : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * (shiftInv W ε q.1 * shiftInv W ε q.2)) (μ.prod μ) := by
    refine integrable_prod_of_bdd (W.measurable.mul
      ((hm.comp measurable_fst).mul (hm.comp measurable_snd))) (C := c ^ 2) fun q ↦ ?_
    have h0 : 0 ≤ W q.1 q.2 * (shiftInv W ε q.1 * shiftInv W ε q.2) :=
      mul_nonneg (W.nonneg _ _)
        (mul_nonneg (shiftInv_pos W hε _).le (shiftInv_pos W hε _).le)
    rw [abs_of_nonneg h0]
    calc W q.1 q.2 * (shiftInv W ε q.1 * shiftInv W ε q.2)
        ≤ 1 * (c * c) := by
          refine mul_le_mul (W.le_one _ _) (mul_le_mul (shiftInv_le W hε _)
            (shiftInv_le W hε _) (shiftInv_pos W hε _).le hc0)
            (mul_nonneg (shiftInv_pos W hε _).le (shiftInv_pos W hε _).le) zero_le_one
      _ = c ^ 2 := by ring
  have hiL : Integrable (fun q : Ω × Ω ↦ W q.1 q.2 * shiftInv W ε q.1 ^ 2)
      (μ.prod μ) := by
    refine integrable_prod_of_bdd (W.measurable.mul
      ((hm.comp measurable_fst).pow_const 2)) (C := c ^ 2) fun q ↦ ?_
    have h0 : 0 ≤ W q.1 q.2 * shiftInv W ε q.1 ^ 2 :=
      mul_nonneg (W.nonneg _ _) (sq_nonneg _)
    rw [abs_of_nonneg h0]
    calc W q.1 q.2 * shiftInv W ε q.1 ^ 2 ≤ 1 * c ^ 2 :=
          mul_le_mul (W.le_one _ _)
            (pow_le_pow_left₀ (shiftInv_pos W hε _).le (shiftInv_le W hε _) 2)
            (sq_nonneg _) zero_le_one
      _ = c ^ 2 := one_mul _
  have hiR : Integrable (fun q : Ω × Ω ↦ W q.1 q.2 * shiftInv W ε q.2 ^ 2)
      (μ.prod μ) := by
    refine integrable_prod_of_bdd (W.measurable.mul
      ((hm.comp measurable_snd).pow_const 2)) (C := c ^ 2) fun q ↦ ?_
    have h0 : 0 ≤ W q.1 q.2 * shiftInv W ε q.2 ^ 2 :=
      mul_nonneg (W.nonneg _ _) (sq_nonneg _)
    rw [abs_of_nonneg h0]
    calc W q.1 q.2 * shiftInv W ε q.2 ^ 2 ≤ 1 * c ^ 2 :=
          mul_le_mul (W.le_one _ _)
            (pow_le_pow_left₀ (shiftInv_pos W hε _).le (shiftInv_le W hε _) 2)
            (sq_nonneg _) zero_le_one
      _ = c ^ 2 := one_mul _
  -- arithmetic--geometric mean, pointwise
  have hamgm : (∫ q, W q.1 q.2 * (shiftInv W ε q.1 * shiftInv W ε q.2) ∂(μ.prod μ))
      ≤ ∫ q, (W q.1 q.2 * shiftInv W ε q.1 ^ 2 +
          W q.1 q.2 * shiftInv W ε q.2 ^ 2) / 2 ∂(μ.prod μ) := by
    refine integral_mono hiP (((hiL.add hiR).div_const 2).congr
      (ae_of_all _ fun q ↦ rfl)) fun q ↦ ?_
    have hW := W.nonneg q.1 q.2
    nlinarith [sq_nonneg (shiftInv W ε q.1 - shiftInv W ε q.2), hW]
  -- Fubini on each half
  have hL : (∫ q, W q.1 q.2 * shiftInv W ε q.1 ^ 2 ∂(μ.prod μ))
      = ∫ x, shiftInv W ε x ^ 2 * degree W x ∂μ :=
    integral_edge_left W (hm.pow_const 2) hg2b
  have hR : (∫ q, W q.1 q.2 * shiftInv W ε q.2 ^ 2 ∂(μ.prod μ))
      = ∫ y, shiftInv W ε y ^ 2 * degree W y ∂μ :=
    integral_edge_snd W (hm.pow_const 2) hg2b
  have hone : (∫ x, shiftInv W ε x ^ 2 * degree W x ∂μ) ≤ 1 := by
    have hint : Integrable (fun x ↦ shiftInv W ε x ^ 2 * degree W x) μ :=
      integrable_of_bdd ((hm.pow_const 2).mul (measurable_degree W)) (C := 1)
        fun x ↦ by
          have h0 : 0 ≤ shiftInv W ε x ^ 2 * degree W x :=
            mul_nonneg (sq_nonneg _) (degree_nonneg W x)
          rw [abs_of_nonneg h0]
          exact sq_shiftInv_mul_degree_le W hε x
    calc (∫ x, shiftInv W ε x ^ 2 * degree W x ∂μ)
        ≤ ∫ _x : Ω, (1 : ℝ) ∂μ :=
          integral_mono hint (integrable_const 1) fun x ↦
            sq_shiftInv_mul_degree_le W hε x
      _ = 1 := by simp
  have hsplit : (∫ q, (W q.1 q.2 * shiftInv W ε q.1 ^ 2 +
      W q.1 q.2 * shiftInv W ε q.2 ^ 2) / 2 ∂(μ.prod μ))
      = ((∫ q, W q.1 q.2 * shiftInv W ε q.1 ^ 2 ∂(μ.prod μ)) +
          ∫ q, W q.1 q.2 * shiftInv W ε q.2 ^ 2 ∂(μ.prod μ)) / 2 := by
    rw [integral_div]
    congr 1
    exact integral_add hiL hiR
  rw [hsplit, hL, hR] at hamgm
  linarith

/-- The shifted Cauchy--Schwarz: `p² ≤ ∫∫ W·√((d(x)+ε)(d(y)+ε))`. -/
lemma sq_le_integral_edge_sqrt_shift (hε : 0 < ε) :
    cliqueDensity 2 W ^ 2 ≤
      ∫ q, W q.1 q.2 *
        (Real.sqrt (degree W q.1 + ε) * Real.sqrt (degree W q.2 + ε))
        ∂(μ.prod μ) := by
  set c := (Real.sqrt ε)⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  have hm := measurable_shiftInv W (ε := ε)
  have hms : Measurable fun x ↦ Real.sqrt (degree W x + ε) :=
    Real.continuous_sqrt.measurable.comp ((measurable_degree W).add measurable_const)
  have hsb : ∀ x : Ω, Real.sqrt (degree W x + ε) ≤ Real.sqrt (1 + ε) := fun x ↦
    Real.sqrt_le_sqrt (by linarith [degree_le_one W x])
  have hs0 : ∀ x : Ω, 0 ≤ Real.sqrt (degree W x + ε) := fun x ↦ Real.sqrt_nonneg _
  set K := Real.sqrt (1 + ε) with hK
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  -- the weight and the multiplier
  have hA0 : ∀ q : Ω × Ω,
      0 ≤ W q.1 q.2 * (shiftInv W ε q.1 * shiftInv W ε q.2) := fun q ↦
    mul_nonneg (W.nonneg _ _)
      (mul_nonneg (shiftInv_pos W hε _).le (shiftInv_pos W hε _).le)
  have hiA : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * (shiftInv W ε q.1 * shiftInv W ε q.2)) (μ.prod μ) := by
    refine integrable_prod_of_bdd (W.measurable.mul
      ((hm.comp measurable_fst).mul (hm.comp measurable_snd))) (C := c ^ 2) fun q ↦ ?_
    rw [abs_of_nonneg (hA0 q)]
    calc W q.1 q.2 * (shiftInv W ε q.1 * shiftInv W ε q.2)
        ≤ 1 * (c * c) :=
          mul_le_mul (W.le_one _ _) (mul_le_mul (shiftInv_le W hε _)
            (shiftInv_le W hε _) (shiftInv_pos W hε _).le hc0)
            (mul_nonneg (shiftInv_pos W hε _).le (shiftInv_pos W hε _).le) zero_le_one
      _ = c ^ 2 := by ring
  -- `A·η = W` and `A·η² = W·√((d+ε)(d+ε))`
  have hAη : ∀ q : Ω × Ω, W q.1 q.2 * (shiftInv W ε q.1 * shiftInv W ε q.2) *
      (Real.sqrt (degree W q.1 + ε) * Real.sqrt (degree W q.2 + ε)) = W q.1 q.2 := by
    intro q
    have h1 := shiftInv_mul_sqrt W hε q.1
    have h2 := shiftInv_mul_sqrt W hε q.2
    calc W q.1 q.2 * (shiftInv W ε q.1 * shiftInv W ε q.2) *
          (Real.sqrt (degree W q.1 + ε) * Real.sqrt (degree W q.2 + ε))
        = W q.1 q.2 * ((shiftInv W ε q.1 * Real.sqrt (degree W q.1 + ε)) *
            (shiftInv W ε q.2 * Real.sqrt (degree W q.2 + ε))) := by ring
      _ = W q.1 q.2 := by rw [h1, h2, one_mul, mul_one]
  have hAη2 : ∀ q : Ω × Ω, W q.1 q.2 * (shiftInv W ε q.1 * shiftInv W ε q.2) *
      (Real.sqrt (degree W q.1 + ε) * Real.sqrt (degree W q.2 + ε)) ^ 2 =
      W q.1 q.2 * (Real.sqrt (degree W q.1 + ε) * Real.sqrt (degree W q.2 + ε)) := by
    intro q
    calc W q.1 q.2 * (shiftInv W ε q.1 * shiftInv W ε q.2) *
          (Real.sqrt (degree W q.1 + ε) * Real.sqrt (degree W q.2 + ε)) ^ 2
        = (W q.1 q.2 * (shiftInv W ε q.1 * shiftInv W ε q.2) *
            (Real.sqrt (degree W q.1 + ε) * Real.sqrt (degree W q.2 + ε))) *
            (Real.sqrt (degree W q.1 + ε) * Real.sqrt (degree W q.2 + ε)) := by ring
      _ = _ := by rw [hAη q]
  have hiW : Integrable (fun q : Ω × Ω ↦ W q.1 q.2) (μ.prod μ) :=
    integrable_prod_of_bdd W.measurable (C := 1) fun q ↦ by
      show |W q.1 q.2| ≤ 1
      rw [abs_of_nonneg (W.nonneg q.1 q.2)]; exact W.le_one q.1 q.2
  have hiS : Integrable (fun q : Ω × Ω ↦ W q.1 q.2 *
      (Real.sqrt (degree W q.1 + ε) * Real.sqrt (degree W q.2 + ε))) (μ.prod μ) := by
    refine integrable_prod_of_bdd (W.measurable.mul
      ((hms.comp measurable_fst).mul (hms.comp measurable_snd))) (C := K ^ 2) fun q ↦ ?_
    have h0 : 0 ≤ W q.1 q.2 *
        (Real.sqrt (degree W q.1 + ε) * Real.sqrt (degree W q.2 + ε)) :=
      mul_nonneg (W.nonneg _ _) (mul_nonneg (hs0 _) (hs0 _))
    rw [abs_of_nonneg h0]
    calc W q.1 q.2 * (Real.sqrt (degree W q.1 + ε) * Real.sqrt (degree W q.2 + ε))
        ≤ 1 * (K * K) :=
          mul_le_mul (W.le_one _ _) (mul_le_mul (hsb _) (hsb _) (hs0 _) hK0)
            (mul_nonneg (hs0 _) (hs0 _)) zero_le_one
      _ = K ^ 2 := by ring
  have hcs := integral_mul_sq_le_integral_mul_integral_mul_sq
    (μ := μ.prod μ)
    (A := fun q : Ω × Ω ↦ W q.1 q.2 * (shiftInv W ε q.1 * shiftInv W ε q.2))
    (η := fun q : Ω × Ω ↦ Real.sqrt (degree W q.1 + ε) * Real.sqrt (degree W q.2 + ε))
    hiA (hiW.congr (ae_of_all _ fun q ↦ (hAη q).symm))
    (hiS.congr (ae_of_all _ fun q ↦ (hAη2 q).symm)) hA0
  rw [integral_congr_ae (ae_of_all _ hAη), integral_congr_ae (ae_of_all _ hAη2),
    integral_prod_edge] at hcs
  have hle := integral_edge_shiftInv_le W hε
  have hSn : 0 ≤ ∫ q, W q.1 q.2 *
      (Real.sqrt (degree W q.1 + ε) * Real.sqrt (degree W q.2 + ε)) ∂(μ.prod μ) :=
    integral_nonneg fun q ↦ mul_nonneg (W.nonneg _ _) (mul_nonneg (hs0 _) (hs0 _))
  nlinarith [hcs, hle, hSn]

end Shift

/-! ### The edge geometric mean -/

/-- **The edge geometric mean.**  `∫∫ W·√(d(x)d(y)) ≥ p²`, with equality at
every constant graphon. -/
theorem sq_le_integral_edge_geoDeg (W : Graphon Ω μ) :
    cliqueDensity 2 W ^ 2 ≤ ∫ q, W q.1 q.2 * geoDeg W q.1 q.2 ∂(μ.prod μ) := by
  have hiG : Integrable (fun q : Ω × Ω ↦ W q.1 q.2 * geoDeg W q.1 q.2) (μ.prod μ) := by
    refine integrable_prod_of_bdd (W.measurable.mul (measurable_geoDeg W))
      (C := 1) fun q ↦ ?_
    have h0 : 0 ≤ W q.1 q.2 * geoDeg W q.1 q.2 :=
      mul_nonneg (W.nonneg _ _) (geoDeg_nonneg W _ _)
    rw [abs_of_nonneg h0]
    exact mul_le_one₀ (W.le_one _ _) (geoDeg_nonneg W _ _) (geoDeg_le_one W _ _)
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  -- pick the shift
  set ε := min 1 (δ ^ 2 / 3) with hεdef
  have hε : 0 < ε := lt_min zero_lt_one (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε3 : 3 * ε ≤ δ ^ 2 := by
    have := min_le_right (1 : ℝ) (δ ^ 2 / 3)
    linarith [this]
  -- the pointwise comparison
  have hpt : ∀ q : Ω × Ω,
      W q.1 q.2 * (Real.sqrt (degree W q.1 + ε) * Real.sqrt (degree W q.2 + ε))
        ≤ W q.1 q.2 * geoDeg W q.1 q.2 + W q.1 q.2 * δ := by
    intro q
    have hx0 := degree_nonneg W q.1
    have hy0 := degree_nonneg W q.2
    have hx1 := degree_le_one W q.1
    have hy1 := degree_le_one W q.2
    have hprod : Real.sqrt (degree W q.1 + ε) * Real.sqrt (degree W q.2 + ε)
        = Real.sqrt ((degree W q.1 + ε) * (degree W q.2 + ε)) :=
      (Real.sqrt_mul (by linarith) _).symm
    have hexp : (degree W q.1 + ε) * (degree W q.2 + ε)
        ≤ degree W q.1 * degree W q.2 + 3 * ε := by nlinarith
    have hstep : Real.sqrt ((degree W q.1 + ε) * (degree W q.2 + ε))
        ≤ geoDeg W q.1 q.2 + δ := by
      calc Real.sqrt ((degree W q.1 + ε) * (degree W q.2 + ε))
          ≤ Real.sqrt (degree W q.1 * degree W q.2 + 3 * ε) :=
            Real.sqrt_le_sqrt hexp
        _ ≤ Real.sqrt (degree W q.1 * degree W q.2) + Real.sqrt (3 * ε) :=
            sqrt_add_le (mul_nonneg hx0 hy0) (by linarith)
        _ ≤ geoDeg W q.1 q.2 + δ := by
            have : Real.sqrt (3 * ε) ≤ δ := by
              rw [show δ = Real.sqrt (δ ^ 2) from (Real.sqrt_sq hδ.le).symm]
              exact Real.sqrt_le_sqrt hε3
            rw [geoDeg]
            linarith
    rw [hprod]
    calc W q.1 q.2 * Real.sqrt ((degree W q.1 + ε) * (degree W q.2 + ε))
        ≤ W q.1 q.2 * (geoDeg W q.1 q.2 + δ) :=
          mul_le_mul_of_nonneg_left hstep (W.nonneg _ _)
      _ = W q.1 q.2 * geoDeg W q.1 q.2 + W q.1 q.2 * δ := by ring
  -- integrate it
  have hiW : Integrable (fun q : Ω × Ω ↦ W q.1 q.2) (μ.prod μ) :=
    integrable_prod_of_bdd W.measurable (C := 1) fun q ↦ by
      show |W q.1 q.2| ≤ 1
      rw [abs_of_nonneg (W.nonneg q.1 q.2)]; exact W.le_one q.1 q.2
  have hms : Measurable fun x ↦ Real.sqrt (degree W x + ε) :=
    Real.continuous_sqrt.measurable.comp ((measurable_degree W).add measurable_const)
  have hiS : Integrable (fun q : Ω × Ω ↦ W q.1 q.2 *
      (Real.sqrt (degree W q.1 + ε) * Real.sqrt (degree W q.2 + ε))) (μ.prod μ) := by
    set K := Real.sqrt (1 + ε) with hK
    refine integrable_prod_of_bdd (W.measurable.mul
      ((hms.comp measurable_fst).mul (hms.comp measurable_snd))) (C := K ^ 2) fun q ↦ ?_
    have hs0 : ∀ x : Ω, 0 ≤ Real.sqrt (degree W x + ε) := fun x ↦ Real.sqrt_nonneg _
    have hsb : ∀ x : Ω, Real.sqrt (degree W x + ε) ≤ K := fun x ↦
      Real.sqrt_le_sqrt (by linarith [degree_le_one W x])
    have h0 : 0 ≤ W q.1 q.2 *
        (Real.sqrt (degree W q.1 + ε) * Real.sqrt (degree W q.2 + ε)) :=
      mul_nonneg (W.nonneg _ _) (mul_nonneg (hs0 _) (hs0 _))
    rw [abs_of_nonneg h0]
    calc W q.1 q.2 * (Real.sqrt (degree W q.1 + ε) * Real.sqrt (degree W q.2 + ε))
        ≤ 1 * (K * K) :=
          mul_le_mul (W.le_one _ _) (mul_le_mul (hsb _) (hsb _) (hs0 _)
            (Real.sqrt_nonneg _)) (mul_nonneg (hs0 _) (hs0 _)) zero_le_one
      _ = K ^ 2 := by ring
  have hiSum : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * geoDeg W q.1 q.2 + W q.1 q.2 * δ) (μ.prod μ) :=
    (hiG.add (hiW.mul_const δ)).congr (ae_of_all _ fun q ↦ rfl)
  have hmono := integral_mono hiS hiSum hpt
  rw [integral_add hiG (hiW.mul_const δ), integral_mul_const, integral_prod_edge] at hmono
  have hshift := sq_le_integral_edge_sqrt_shift W hε
  have hp1 : cliqueDensity 2 W ≤ 1 := cliqueDensity_le_one 2 W
  nlinarith [hshift, hmono, hδ.le, hp1, cliqueDensity_nonneg 2 W]

end Taeyoung.Methods.Atlas148
