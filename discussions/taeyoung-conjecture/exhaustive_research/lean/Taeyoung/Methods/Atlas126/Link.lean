import Taeyoung.Methods.Link.WeightedGoodman
import Taeyoung.Methods.PureChordal.WeightedCauchySchwarz
import Taeyoung.Methods.Peeling

/-!
# Atlas 126: the rooted `C₄` and its two-piece projection

`notes/atlas126_triangle_c4_vertex_supporting_plane.tex` §2.  Rooting the
triangle--`C₄` amalgam at its cut vertex factors the density into a rooted
triangle times a rooted `C₄`.  The rooted `C₄` is a second moment of the
two-step kernel

```
b_x(z) = ∫ W(x,y) W(y,z) dμ(y),      r₄(x) = ∫ b_x(z)² dμ(z),
```

whose first two moments against `1` and `W(x,·)` are the rooted path density
`a(x)` and the rooted triangle density `τ(x)`.  Splitting the `z`-integral with
the weights `W(x,·)` and `1 - W(x,·)` and applying Cauchy--Schwarz on each part
gives the note's projection `r₄ ≥ τ²/d + (a-τ)²/(1-d)`.

It is stated here in the cleared form

```
(1 - d)·τ² + d·(a - τ)² ≤ d(1 - d)·r₄,
```

which needs no hypothesis on `d` at all: the two degenerate fibres `d = 0` and
`d = 1` are already contained in it, so no convention is required anywhere.
-/

open MeasureTheory

namespace Taeyoung.Methods.Atlas126

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The two-step kernel -/

/-- `b_x(z) = ∫ W(x,y) W(y,z) dμ(y)`, the two-step kernel rooted at `x`. -/
noncomputable def pairOp (W : Graphon Ω μ) (x z : Ω) : ℝ :=
  ∫ y, W x y * W y z ∂μ

section Kernel

variable (W : Graphon Ω μ)

lemma measurable_pairOp_uncurry :
    Measurable (Function.uncurry fun x z ↦ pairOp W x z) := by
  have h : StronglyMeasurable (Function.uncurry fun q : Ω × Ω ↦
      fun y ↦ W q.1 y * W y q.2) := by
    refine Measurable.stronglyMeasurable ?_
    have h1 : Measurable fun r : (Ω × Ω) × Ω ↦ W r.1.1 r.2 :=
      W.measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have h2 : Measurable fun r : (Ω × Ω) × Ω ↦ W r.2 r.1.2 :=
      W.measurable.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    exact h1.mul h2
  exact (h.integral_prod_right' (ν := μ)).measurable

lemma measurable_pairOp (x : Ω) : Measurable (pairOp W x) :=
  (measurable_pairOp_uncurry W).comp (measurable_const.prodMk measurable_id)

omit [IsProbabilityMeasure μ] in
lemma pairOp_nonneg (x z : Ω) : 0 ≤ pairOp W x z :=
  integral_nonneg fun _y ↦ mul_nonneg (W.nonneg _ _) (W.nonneg _ _)

lemma integrable_pairIntegrand (x z : Ω) :
    Integrable (fun y ↦ W x y * W y z) μ :=
  integrable_of_bdd ((measurable_row W.measurable x).mul
    (W.measurable.comp (measurable_id.prodMk measurable_const))) (C := 1)
    fun y ↦ by
      rw [abs_of_nonneg (mul_nonneg (W.nonneg x y) (W.nonneg y z))]
      exact mul_le_one₀ (W.le_one x y) (W.nonneg y z) (W.le_one y z)

lemma pairOp_le_one (x z : Ω) : pairOp W x z ≤ 1 := by
  calc pairOp W x z ≤ ∫ _y : Ω, (1 : ℝ) ∂μ :=
        integral_mono (integrable_pairIntegrand W x z) (integrable_const _)
          fun y ↦ mul_le_one₀ (W.le_one x y) (W.nonneg y z) (W.le_one y z)
    _ = 1 := by simp

lemma integrable_pairOp (x : Ω) : Integrable (pairOp W x) μ :=
  integrable_of_bdd (measurable_pairOp W x) (C := 1) fun z ↦ by
    rw [abs_of_nonneg (pairOp_nonneg W x z)]; exact pairOp_le_one W x z

omit [IsProbabilityMeasure μ] in
/-- `b_x(z) = b_z(x)`: the two-step kernel is symmetric. -/
lemma pairOp_symm (x z : Ω) : pairOp W x z = pairOp W z x := by
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only []
  rw [W.symm x y, W.symm y z]
  ring

/-! ### The first two moments of `b_x` -/

/-- `∫ b_x = a(x)`: one Fubini swap. -/
theorem integral_pairOp (x : Ω) : (∫ z, pairOp W x z ∂μ) = pathOp W x := by
  have hint : Integrable (Function.uncurry fun z y ↦ W x y * W y z) (μ.prod μ) := by
    refine integrable_prod_of_bdd ?_ (C := 1) fun q ↦ ?_
    · exact (W.measurable.comp (measurable_const.prodMk measurable_snd)).mul
        (W.measurable.comp (measurable_snd.prodMk measurable_fst))
    · show |W x q.2 * W q.2 q.1| ≤ 1
      rw [abs_of_nonneg (mul_nonneg (W.nonneg _ _) (W.nonneg _ _))]
      exact mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _)
  calc (∫ z, pairOp W x z ∂μ) = ∫ z, ∫ y, W x y * W y z ∂μ ∂μ := rfl
    _ = ∫ y, ∫ z, W x y * W y z ∂μ ∂μ := integral_integral_swap hint
    _ = pathOp W x := by
        refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
        simp only []
        rw [integral_const_mul]
        rfl

/-- `∫ W(x,·) b_x = τ(x)`: one Fubini swap. -/
theorem integral_row_mul_pairOp (x : Ω) :
    (∫ z, W x z * pairOp W x z ∂μ) = rootedTriangle W x := by
  have hint : Integrable
      (Function.uncurry fun z y ↦ W x z * (W x y * W y z)) (μ.prod μ) := by
    refine integrable_prod_of_bdd ?_ (C := 1) fun q ↦ ?_
    · refine (W.measurable.comp (measurable_const.prodMk measurable_fst)).mul ?_
      exact (W.measurable.comp (measurable_const.prodMk measurable_snd)).mul
        (W.measurable.comp (measurable_snd.prodMk measurable_fst))
    · show |W x q.1 * (W x q.2 * W q.2 q.1)| ≤ 1
      rw [abs_of_nonneg (mul_nonneg (W.nonneg _ _)
        (mul_nonneg (W.nonneg _ _) (W.nonneg _ _)))]
      exact mul_le_one₀ (W.le_one _ _)
        (mul_nonneg (W.nonneg _ _) (W.nonneg _ _))
        (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
  have hstep : (∫ z, W x z * pairOp W x z ∂μ)
      = ∫ z, ∫ y, W x z * (W x y * W y z) ∂μ ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    simp only [pairOp]
    rw [integral_const_mul]
  rw [hstep, integral_integral_swap hint, rootedTriangle]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  ring

/-! ### The rooted `C₄` density -/

/-- `r₄(x) = ∫ b_x(z)² dμ(z)`, the `C₄` density rooted at `x`. -/
noncomputable def rootedC4 (W : Graphon Ω μ) (x : Ω) : ℝ :=
  ∫ z, pairOp W x z ^ 2 ∂μ

omit [IsProbabilityMeasure μ] in
lemma rootedC4_nonneg (x : Ω) : 0 ≤ rootedC4 W x :=
  integral_nonneg fun _z ↦ sq_nonneg _

lemma measurable_rootedC4 : Measurable (rootedC4 W) := by
  have h : StronglyMeasurable (Function.uncurry fun x z ↦ pairOp W x z ^ 2) :=
    ((measurable_pairOp_uncurry W).pow_const 2).stronglyMeasurable
  exact (h.integral_prod_right' (ν := μ)).measurable

lemma integrable_pairOp_sq (x : Ω) : Integrable (fun z ↦ pairOp W x z ^ 2) μ :=
  integrable_of_bdd ((measurable_pairOp W x).pow_const 2) (C := 1) fun z ↦ by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (pairOp_nonneg W x z) (pairOp_le_one W x z)

lemma rootedC4_le_one (x : Ω) : rootedC4 W x ≤ 1 := by
  calc rootedC4 W x ≤ ∫ _z : Ω, (1 : ℝ) ∂μ :=
        integral_mono (integrable_pairOp_sq W x) (integrable_const _) fun z ↦
          pow_le_one₀ (pairOp_nonneg W x z) (pairOp_le_one W x z)
    _ = 1 := by simp

/-- `τ(x) ≤ a(x)`: drop the factor `W(x,z)` from the rooted triangle. -/
theorem rootedTriangle_le_pathOp (x : Ω) : rootedTriangle W x ≤ pathOp W x := by
  rw [← integral_row_mul_pairOp W x, ← integral_pairOp W x]
  refine integral_mono ?_ (integrable_pairOp W x) fun z ↦ ?_
  · exact integrable_of_bdd ((measurable_row W.measurable x).mul
      (measurable_pairOp W x)) (C := 1) fun z ↦ by
        rw [abs_of_nonneg (mul_nonneg (W.nonneg x z) (pairOp_nonneg W x z))]
        exact mul_le_one₀ (W.le_one x z) (pairOp_nonneg W x z) (pairOp_le_one W x z)
  · exact mul_le_of_le_one_left (pairOp_nonneg W x z) (W.le_one x z)

/-- `a(x)² ≤ r₄(x)`: Cauchy--Schwarz against the constant `1`. -/
theorem sq_pathOp_le_rootedC4 (x : Ω) : pathOp W x ^ 2 ≤ rootedC4 W x := by
  have h := integral_mul_sq_le_integral_mul_integral_mul_sq (μ := μ)
    (A := fun _ : Ω ↦ (1 : ℝ)) (η := pairOp W x)
    (integrable_const _)
    ((integrable_pairOp W x).congr (ae_of_all _ fun z ↦ (one_mul _).symm))
    ((integrable_pairOp_sq W x).congr (ae_of_all _ fun z ↦ (one_mul _).symm))
    (fun _ ↦ zero_le_one)
  simp only [one_mul] at h
  rw [integral_const] at h
  simpa [integral_pairOp W x, rootedC4] using h

end Kernel

/-! ### The two-piece projection -/

/-- **The note's projection, cleared of denominators.**  Two weighted
Cauchy--Schwarz inequalities, one against `W(x,·)` and one against
`1 - W(x,·)`.  No hypothesis on `d(x)` is needed. -/
theorem projection (W : Graphon Ω μ) (x : Ω) :
    (1 - degree W x) * rootedTriangle W x ^ 2
        + degree W x * (pathOp W x - rootedTriangle W x) ^ 2 ≤
      degree W x * (1 - degree W x) * rootedC4 W x := by
  set b : Ω → ℝ := pairOp W x with hb
  set A : Ω → ℝ := fun z ↦ W x z with hA
  set B : Ω → ℝ := fun z ↦ 1 - W x z with hB
  have hA0 : ∀ z, 0 ≤ A z := fun z ↦ W.nonneg x z
  have hB0 : ∀ z, 0 ≤ B z := fun z ↦ by
    have := W.le_one x z; simp only [hB]; linarith
  have hAm : Measurable A := measurable_row W.measurable x
  have hBm : Measurable B := measurable_const.sub hAm
  have hbm : Measurable b := measurable_pairOp W x
  have hb0 : ∀ z, 0 ≤ b z := fun z ↦ pairOp_nonneg W x z
  have hb1 : ∀ z, b z ≤ 1 := fun z ↦ pairOp_le_one W x z
  have hAi : Integrable A μ :=
    integrable_of_bdd hAm (C := 1) fun z ↦ by
      rw [abs_of_nonneg (hA0 z)]; exact W.le_one x z
  have hBi : Integrable B μ :=
    integrable_of_bdd hBm (C := 1) fun z ↦ by
      rw [abs_of_nonneg (hB0 z)]; simp only [hB]; linarith [W.nonneg x z]
  have hAb : Integrable (fun z ↦ A z * b z) μ :=
    integrable_of_bdd (hAm.mul hbm) (C := 1) fun z ↦ by
      rw [abs_of_nonneg (mul_nonneg (hA0 z) (hb0 z))]
      exact mul_le_one₀ (W.le_one x z) (hb0 z) (hb1 z)
  have hBb : Integrable (fun z ↦ B z * b z) μ :=
    integrable_of_bdd (hBm.mul hbm) (C := 1) fun z ↦ by
      rw [abs_of_nonneg (mul_nonneg (hB0 z) (hb0 z))]
      refine mul_le_one₀ ?_ (hb0 z) (hb1 z)
      simp only [hB]; linarith [W.nonneg x z]
  have hAb2 : Integrable (fun z ↦ A z * b z ^ 2) μ :=
    integrable_of_bdd (hAm.mul (hbm.pow_const 2)) (C := 1) fun z ↦ by
      rw [abs_of_nonneg (mul_nonneg (hA0 z) (sq_nonneg _))]
      exact mul_le_one₀ (W.le_one x z) (sq_nonneg _)
        (pow_le_one₀ (hb0 z) (hb1 z))
  have hBb2 : Integrable (fun z ↦ B z * b z ^ 2) μ :=
    integrable_of_bdd (hBm.mul (hbm.pow_const 2)) (C := 1) fun z ↦ by
      rw [abs_of_nonneg (mul_nonneg (hB0 z) (sq_nonneg _))]
      refine mul_le_one₀ ?_ (sq_nonneg _) (pow_le_one₀ (hb0 z) (hb1 z))
      simp only [hB]; linarith [W.nonneg x z]
  have hcsA := integral_mul_sq_le_integral_mul_integral_mul_sq
    (μ := μ) (A := A) (η := b) hAi hAb hAb2 hA0
  have hcsB := integral_mul_sq_le_integral_mul_integral_mul_sq
    (μ := μ) (A := B) (η := b) hBi hBb hBb2 hB0
  -- identify the four moments
  have eA : (∫ z, A z ∂μ) = degree W x := rfl
  have eB : (∫ z, B z ∂μ) = 1 - degree W x := by
    rw [integral_sub (integrable_const _) hAi]; simp [eA]
  have eAb : (∫ z, A z * b z ∂μ) = rootedTriangle W x :=
    integral_row_mul_pairOp W x
  have eBb : (∫ z, B z * b z ∂μ) = pathOp W x - rootedTriangle W x := by
    have hcong : ∀ z, B z * b z = b z - A z * b z := fun z ↦ by
      simp only [hA, hB]; ring
    rw [integral_congr_ae (ae_of_all _ hcong),
      integral_sub (integrable_pairOp W x) hAb, integral_pairOp W x,
      eAb]
  have esplit : (∫ z, A z * b z ^ 2 ∂μ) + ∫ z, B z * b z ^ 2 ∂μ
      = rootedC4 W x := by
    rw [← integral_add hAb2 hBb2, rootedC4]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    simp only [hA, hB]; ring
  rw [eA, eAb] at hcsA
  rw [eB, eBb] at hcsB
  have hd0 : 0 ≤ degree W x := degree_nonneg W x
  have hd1 : degree W x ≤ 1 := degree_le_one W x
  have hIA : 0 ≤ ∫ z, A z * b z ^ 2 ∂μ :=
    integral_nonneg fun z ↦ mul_nonneg (hA0 z) (sq_nonneg _)
  have hIB : 0 ≤ ∫ z, B z * b z ^ 2 ∂μ :=
    integral_nonneg fun z ↦ mul_nonneg (hB0 z) (sq_nonneg _)
  have h1 : (1 - degree W x) * rootedTriangle W x ^ 2
      ≤ (1 - degree W x) * (degree W x * ∫ z, A z * b z ^ 2 ∂μ) :=
    mul_le_mul_of_nonneg_left hcsA (by linarith)
  have h2 : degree W x * (pathOp W x - rootedTriangle W x) ^ 2
      ≤ degree W x * ((1 - degree W x) * ∫ z, B z * b z ^ 2 ∂μ) :=
    mul_le_mul_of_nonneg_left hcsB hd0
  rw [← esplit]
  nlinarith [h1, h2, hIA, hIB, hd0, hd1]

end Taeyoung.Methods.Atlas126
