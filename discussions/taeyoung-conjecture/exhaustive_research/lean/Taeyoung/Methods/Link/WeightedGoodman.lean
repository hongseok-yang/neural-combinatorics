import Taeyoung.Foundation.Link

/-!
# The weighted rooted-triangle inequality

For every graphon `W` of edge density `p` and every `h ≥ 0`,

```
p · ∫ dʰ τ  ≥  (2p - 1) · ∫ dʰ⁺²
```

where `d` is the degree function and `τ` the rooted triangle density
(`weighted_rootedTriangle`).  This is the single analytic input shared by the
cone and leaf methodologies; it is written out verbatim in five of the notes,
and is proved here once.

The statement is kept cross-multiplied rather than in the notes' `(2p-1)/p`
form, so nothing has to be assumed about `p` — in particular the threshold case
`p = 0` needs no separate treatment.

The proof has three steps:

1. `rootedTriangle_ge` — a pointwise Goodman bound `τ(x) ≥ 2·(T_W d)(x) - p`,
   from `ab ≥ a + b - 1` on `[0,1]²` weighted by `W(y,z)`.  The linearised
   double integral is evaluated on the product measure, where linearity is
   single-level, and Fubini plus symmetry of `W` turn both cross terms back
   into `T_W d`.
2. `correlation_bound` — `∫ dʰ · T_U u ≥ ∫ dʰ u²` for `U = 1 - W`, `u = 1 - d`.
   Symmetrising over `Prod.swap` turns the difference into
   `∫∫ U(x,y)·(d x - d y)·(d xʰ - d yʰ)`, which is pointwise nonnegative
   because `t ↦ tʰ` is monotone on `[0,∞)`.
3. `weighted_rootedTriangle` — completing the square: after substituting
   `corrTerm_eq`, the residual is `∫ dʰ (d - p)² ≥ 0`.
-/

open MeasureTheory

namespace Taeyoung.Methods.Link

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Bounded measurable functions are integrable -/

lemma integrable_of_bdd {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hbdd : ∀ x, |f x| ≤ C) : Integrable f μ :=
  (integrable_const (μ := μ) C).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hbdd x)

lemma integrable_prod_of_bdd {f : Ω × Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hbdd : ∀ p, |f p| ≤ C) : Integrable f (μ.prod μ) :=
  (integrable_const (μ := μ.prod μ) C).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun p ↦ by rw [Real.norm_eq_abs]; exact hbdd p)

/-- The integral of a bounded measurable function obeys the same bound. -/
lemma abs_integral_le_of_bdd {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hbdd : ∀ z, |f z| ≤ C) : |∫ z, f z ∂μ| ≤ C := by
  have hint : Integrable f μ := integrable_of_bdd hf hbdd
  calc |∫ z, f z ∂μ| ≤ ∫ z, |f z| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _z : Ω, C ∂μ :=
        integral_mono hint.abs (integrable_const (μ := μ) C) hbdd
    _ = C := by simp

/-- Rows of a jointly measurable kernel are measurable. -/
lemma measurable_row {f : Ω → Ω → ℝ} (hf : Measurable (Function.uncurry f))
    (y : Ω) : Measurable fun z ↦ f y z :=
  hf.comp (measurable_const.prodMk measurable_id)

/-- Partial integrals of a jointly measurable kernel are measurable. -/
lemma measurable_integral_right {f : Ω → Ω → ℝ}
    (hf : Measurable (Function.uncurry f)) :
    Measurable fun y ↦ ∫ z, f y z ∂μ :=
  (hf.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

/-- Partial integrals of a bounded measurable kernel are integrable. -/
lemma integrable_integral_right {f : Ω → Ω → ℝ}
    (hf : Measurable (Function.uncurry f)) {C : ℝ}
    (hbdd : ∀ y z, |f y z| ≤ C) :
    Integrable (fun y ↦ ∫ z, f y z ∂μ) μ :=
  integrable_of_bdd (measurable_integral_right hf) fun y ↦
    abs_integral_le_of_bdd (measurable_row hf y) (hbdd y)

/-- A bounded measurable kernel is product-integrable. -/
lemma integrable_uncurry_of_bdd {f : Ω → Ω → ℝ}
    (hf : Measurable (Function.uncurry f)) {C : ℝ}
    (hbdd : ∀ y z, |f y z| ≤ C) :
    Integrable (Function.uncurry f) (μ.prod μ) :=
  integrable_prod_of_bdd hf fun q ↦ hbdd q.1 q.2

/-! ### The operator applied to the degree function -/

/-- `(T_W d)(x) = ∫ W(x,y) d(y) dμ(y)`, the rooted two-edge path density. -/
noncomputable def pathOp (W : Graphon Ω μ) (x : Ω) : ℝ :=
  ∫ y, W x y * degree W y ∂μ

lemma measurable_pathOp (W : Graphon Ω μ) : Measurable (pathOp W) := by
  have h : StronglyMeasurable
      (Function.uncurry fun x y ↦ W x y * degree W y) := by
    refine (W.measurable.mul ?_).stronglyMeasurable
    exact (measurable_degree W).comp measurable_snd
  exact (h.integral_prod_right' (ν := μ)).measurable

lemma pathOp_nonneg (W : Graphon Ω μ) (x : Ω) : 0 ≤ pathOp W x :=
  integral_nonneg fun y ↦ mul_nonneg (W.nonneg x y) (degree_nonneg W y)

lemma pathOp_le_one (W : Graphon Ω μ) (x : Ω) : pathOp W x ≤ 1 := by
  have hint : Integrable (fun y ↦ W x y * degree W y) μ := by
    refine integrable_of_bdd ?_ (C := 1) fun y ↦ ?_
    · exact (W.measurable.comp (measurable_const.prodMk measurable_id)).mul
        (measurable_degree W)
    · rw [abs_of_nonneg (mul_nonneg (W.nonneg x y) (degree_nonneg W y))]
      exact mul_le_one₀ (W.le_one x y) (degree_nonneg W y) (degree_le_one W y)
  calc pathOp W x ≤ ∫ _y : Ω, (1 : ℝ) ∂μ :=
        integral_mono hint (integrable_const _) fun y ↦
          mul_le_one₀ (W.le_one x y) (degree_nonneg W y) (degree_le_one W y)
    _ = 1 := by simp

/-- Integrating `W(y,z)` in `z` gives the degree of `y`. -/
lemma integral_edge_right (W : Graphon Ω μ) (y : Ω) :
    ∫ z, W y z ∂μ = degree W y := rfl

/-! ### Step 1: the pointwise Goodman bound -/

section Goodman

variable (W : Graphon Ω μ) (x : Ω)

private lemma hW : Measurable (Function.uncurry W.toFun) := W.measurable

private lemma meas_fst : Measurable fun q : Ω × Ω ↦ W x q.1 :=
  W.measurable.comp (measurable_const.prodMk measurable_fst)

private lemma meas_snd : Measurable fun q : Ω × Ω ↦ W x q.2 :=
  W.measurable.comp (measurable_const.prodMk measurable_snd)

private lemma bdd_mul_edge (a : Ω) (y z : Ω) : |W a y * W y z| ≤ 1 := by
  rw [abs_of_nonneg (mul_nonneg (W.nonneg a y) (W.nonneg y z))]
  exact mul_le_one₀ (W.le_one a y) (W.nonneg y z) (W.le_one y z)

/-- **Pointwise Goodman bound.**  From `ab ≥ a + b - 1` on `[0,1]²`, applied to
`W(x,y)` and `W(x,z)` and weighted by `W(y,z)`. -/
theorem rootedTriangle_ge :
    2 * pathOp W x - cliqueDensity 2 W ≤ rootedTriangle W x := by
  have hWm : Measurable (Function.uncurry W.toFun) := W.measurable
  -- the triangle integrand and its linearisation
  have hgm : Measurable (Function.uncurry fun y z ↦ W x y * W x z * W y z) :=
    ((meas_fst W x).mul (meas_snd W x)).mul hWm
  have hlm : Measurable
      (Function.uncurry fun y z ↦ (W x y + W x z - 1) * W y z) :=
    (((meas_fst W x).add (meas_snd W x)).sub measurable_const).mul hWm
  have hgb : ∀ y z, |W x y * W x z * W y z| ≤ 1 := by
    intro y z
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (W.nonneg x y) (W.nonneg x z))
      (W.nonneg y z))]
    exact mul_le_one₀ (mul_le_one₀ (W.le_one x y) (W.nonneg x z)
      (W.le_one x z)) (W.nonneg y z) (W.le_one y z)
  have hlb : ∀ y z, |(W x y + W x z - 1) * W y z| ≤ 1 := by
    intro y z
    have h1 := W.nonneg x y; have h2 := W.le_one x y
    have h3 := W.nonneg x z; have h4 := W.le_one x z
    have h5 := W.nonneg y z; have h6 := W.le_one y z
    rw [abs_le]
    constructor <;> nlinarith
  have hpt : ∀ y z, (W x y + W x z - 1) * W y z ≤ W x y * W x z * W y z := by
    intro y z
    have hab : W x y + W x z - 1 ≤ W x y * W x z := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (W.le_one x y))
        (sub_nonneg.mpr (W.le_one x z))]
    exact mul_le_mul_of_nonneg_right hab (W.nonneg y z)
  -- the linearised double integral is `2 (T_W d)(x) - p`
  have hlin : (∫ y, ∫ z, (W x y + W x z - 1) * W y z ∂μ ∂μ) =
      2 * pathOp W x - cliqueDensity 2 W := by
    have hlint : Integrable (Function.uncurry fun y z ↦
        (W x y + W x z - 1) * W y z) (μ.prod μ) :=
      integrable_uncurry_of_bdd hlm hlb
    have ha : Integrable (fun q : Ω × Ω ↦ W x q.1 * W q.1 q.2) (μ.prod μ) :=
      integrable_uncurry_of_bdd ((meas_fst W x).mul hWm) (bdd_mul_edge W x)
    have hb : Integrable (fun q : Ω × Ω ↦ W x q.2 * W q.1 q.2) (μ.prod μ) := by
      refine integrable_prod_of_bdd ((meas_snd W x).mul hWm) (C := 1) fun q ↦ ?_
      rw [abs_of_nonneg (mul_nonneg (W.nonneg x q.2) (W.nonneg q.1 q.2))]
      exact mul_le_one₀ (W.le_one x q.2) (W.nonneg q.1 q.2) (W.le_one q.1 q.2)
    have hc : Integrable (fun q : Ω × Ω ↦ W q.1 q.2) (μ.prod μ) := by
      refine integrable_prod_of_bdd hWm (C := 1) fun q ↦ ?_
      rw [abs_of_nonneg (W.nonneg q.1 q.2)]
      exact W.le_one q.1 q.2
    rw [integral_integral hlint]
    have hcongr : ∀ q : Ω × Ω,
        (W x q.1 + W x q.2 - 1) * W q.1 q.2 =
          W x q.1 * W q.1 q.2 + W x q.2 * W q.1 q.2 - W q.1 q.2 := by
      intro q; ring
    rw [integral_congr_ae (ae_of_all _ hcongr)]
    have e1 := integral_sub (ha.add hb) hc
    have e2 := integral_add ha hb
    simp only [Pi.add_apply] at e1 e2
    rw [e1, e2]
    -- identify the three product integrals
    have hA : (∫ q : Ω × Ω, W x q.1 * W q.1 q.2 ∂(μ.prod μ)) = pathOp W x := by
      have ha' : Integrable (Function.uncurry fun y z ↦ W x y * W y z)
          (μ.prod μ) := ha
      rw [← integral_integral ha']
      refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      simp only []
      rw [integral_const_mul]
      rfl
    have hB : (∫ q : Ω × Ω, W x q.2 * W q.1 q.2 ∂(μ.prod μ)) = pathOp W x := by
      have hb' : Integrable (Function.uncurry fun y z ↦ W x z * W y z)
          (μ.prod μ) := hb
      rw [← integral_integral hb', integral_integral_swap hb']
      refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
      simp only []
      rw [integral_const_mul]
      congr 1
      exact integral_congr_ae (ae_of_all _ fun y ↦ W.symm y z)
    have hC : (∫ q : Ω × Ω, W q.1 q.2 ∂(μ.prod μ)) = cliqueDensity 2 W := by
      have hc' : Integrable (Function.uncurry fun y z ↦ W y z) (μ.prod μ) := hc
      rw [← integral_integral hc', ← integral_degree]
      rfl
    rw [hA, hB, hC]
    ring
  rw [← hlin, rootedTriangle]
  refine integral_mono (integrable_integral_right hlm hlb)
    (integrable_integral_right hgm hgb) fun y ↦ ?_
  exact integral_mono (integrable_of_bdd (measurable_row hlm y) (hlb y))
    (integrable_of_bdd (measurable_row hgm y) (hgb y)) (hpt y)

end Goodman

/-! ### Step 2: the correlation bound -/

/-- `a ↦ aʰ` is monotone on `[0,∞)`, so `a - b` and `aʰ - bʰ` agree in sign. -/
lemma sub_mul_pow_sub_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : ℕ) :
    0 ≤ (a - b) * (a ^ h - b ^ h) := by
  rcases le_total b a with hab | hab
  · exact mul_nonneg (by linarith) (by simpa using pow_le_pow_left₀ hb hab h)
  · have hp : a ^ h ≤ b ^ h := pow_le_pow_left₀ ha hab h
    nlinarith

/-- The complement pairing `(T_U u)(x) = ∫ (1 - W x y)(1 - d y) dμ(y)`. -/
noncomputable def corrTerm (W : Graphon Ω μ) (x : Ω) : ℝ :=
  ∫ y, (1 - W x y) * (1 - degree W y) ∂μ

section Correlation

variable (W : Graphon Ω μ) (h : ℕ)

private lemma meas_compl :
    Measurable fun q : Ω × Ω ↦ 1 - W q.1 q.2 :=
  measurable_const.sub W.measurable

private lemma meas_deg_fst :
    Measurable fun q : Ω × Ω ↦ degree W q.1 :=
  (measurable_degree W).comp measurable_fst

private lemma meas_deg_snd :
    Measurable fun q : Ω × Ω ↦ degree W q.2 :=
  (measurable_degree W).comp measurable_snd

private lemma bdd_pow (x : Ω) : |degree W x ^ h| ≤ 1 := by
  rw [abs_of_nonneg (pow_nonneg (degree_nonneg W x) h)]
  exact pow_le_one₀ (degree_nonneg W x) (degree_le_one W x)

/-- **Correlation bound.**  `u = 1 - d` and `dʰ` are oppositely ordered, so
pairing `dʰ` against `T_U u` beats pairing it against `u²`. -/
theorem correlation_bound :
    (∫ x, degree W x ^ h * (1 - degree W x) ^ 2 ∂μ) ≤
      ∫ x, degree W x ^ h * corrTerm W x ∂μ := by
  set F : Ω × Ω → ℝ :=
    fun q ↦ (1 - W q.1 q.2) * (degree W q.1 ^ h * (1 - degree W q.2)) with hF
  set G : Ω × Ω → ℝ :=
    fun q ↦ (1 - W q.1 q.2) * (degree W q.1 ^ h * (1 - degree W q.1)) with hG
  have hFm : Measurable F :=
    (meas_compl W).mul (((meas_deg_fst W).pow_const h).mul
      (measurable_const.sub (meas_deg_snd W)))
  have hGm : Measurable G :=
    (meas_compl W).mul (((meas_deg_fst W).pow_const h).mul
      (measurable_const.sub (meas_deg_fst W)))
  have hbd : ∀ (a b c : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → 0 ≤ c → c ≤ 1 →
      |(1 - a) * (b * (1 - c))| ≤ 1 := by
    intro a b c h1 h2 h3 h4 h5 h6
    have ha' : 0 ≤ 1 - a := by linarith
    have ha1 : 1 - a ≤ 1 := by linarith
    have hc' : 0 ≤ 1 - c := by linarith
    have hc1 : 1 - c ≤ 1 := by linarith
    have hnn : 0 ≤ (1 - a) * (b * (1 - c)) :=
      mul_nonneg ha' (mul_nonneg h3 hc')
    rw [abs_of_nonneg hnn]
    exact mul_le_one₀ ha1 (mul_nonneg h3 hc') (mul_le_one₀ h4 hc' hc1)
  have hFb : ∀ q, |F q| ≤ 1 := fun q ↦ hbd _ _ _ (W.nonneg _ _) (W.le_one _ _)
    (pow_nonneg (degree_nonneg W _) h)
    (pow_le_one₀ (degree_nonneg W _) (degree_le_one W _))
    (degree_nonneg W _) (degree_le_one W _)
  have hGb : ∀ q, |G q| ≤ 1 := fun q ↦ hbd _ _ _ (W.nonneg _ _) (W.le_one _ _)
    (pow_nonneg (degree_nonneg W _) h)
    (pow_le_one₀ (degree_nonneg W _) (degree_le_one W _))
    (degree_nonneg W _) (degree_le_one W _)
  have hFi : Integrable F (μ.prod μ) := integrable_prod_of_bdd hFm hFb
  have hGi : Integrable G (μ.prod μ) := integrable_prod_of_bdd hGm hGb
  -- the two product integrals are the two sides
  have hFval : (∫ q, F q ∂(μ.prod μ)) = ∫ x, degree W x ^ h * corrTerm W x ∂μ := by
    have hFi' : Integrable (Function.uncurry fun a b ↦
        (1 - W a b) * (degree W a ^ h * (1 - degree W b))) (μ.prod μ) := hFi
    rw [← integral_integral hFi']
    refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
    simp only []
    rw [corrTerm, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun b ↦ by ring)
  have hGval : (∫ q, G q ∂(μ.prod μ)) =
      ∫ x, degree W x ^ h * (1 - degree W x) ^ 2 ∂μ := by
    have hGi' : Integrable (Function.uncurry fun a b ↦
        (1 - W a b) * (degree W a ^ h * (1 - degree W a))) (μ.prod μ) := hGi
    rw [← integral_integral hGi']
    refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
    simp only []
    have hconst : (∫ b, (1 - W a b) * (degree W a ^ h * (1 - degree W a)) ∂μ) =
        (degree W a ^ h * (1 - degree W a)) * ∫ b, (1 - W a b) ∂μ := by
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun b ↦ by ring)
    have hone : (∫ b, (1 - W a b) ∂μ) = 1 - degree W a := by
      have hint : Integrable (fun b ↦ W a b) μ :=
        integrable_of_bdd (measurable_row W.measurable a) (C := 1) fun b ↦ by
          rw [abs_of_nonneg (W.nonneg a b)]; exact W.le_one a b
      rw [integral_sub (integrable_const _) hint]
      simp [degree]
    rw [hconst, hone]
    ring
  -- the difference is nonnegative, by symmetrising
  have hswap : (∫ q, (F q - G q) ∂(μ.prod μ)) =
      ∫ q, (F q.swap - G q.swap) ∂(μ.prod μ) :=
    (integral_prod_swap (fun q ↦ F q - G q)).symm
  have hsum : 0 ≤ ∫ q, ((F q - G q) + (F q.swap - G q.swap)) ∂(μ.prod μ) := by
    refine integral_nonneg fun q ↦ ?_
    have hkey : (F q - G q) + (F q.swap - G q.swap) =
        (1 - W q.1 q.2) *
          ((degree W q.1 - degree W q.2) *
            (degree W q.1 ^ h - degree W q.2 ^ h)) := by
      simp only [hF, hG, Prod.fst_swap, Prod.snd_swap]
      rw [W.symm q.2 q.1]
      ring
    rw [hkey]
    exact mul_nonneg (by linarith [W.le_one q.1 q.2])
      (sub_mul_pow_sub_nonneg (degree_nonneg W q.1) (degree_nonneg W q.2) h)
  have hdiff : 0 ≤ ∫ q, (F q - G q) ∂(μ.prod μ) := by
    have hswapi : Integrable (fun q : Ω × Ω ↦ F q.swap - G q.swap)
        (μ.prod μ) := by
      refine integrable_prod_of_bdd ((hFm.comp measurable_swap).sub
        (hGm.comp measurable_swap)) (C := 2) fun q ↦ ?_
      have h1 := hFb q.swap
      have h2 := hGb q.swap
      rw [abs_le] at h1 h2 ⊢
      exact ⟨by linarith [h1.1, h1.2, h2.1, h2.2],
        by linarith [h1.1, h1.2, h2.1, h2.2]⟩
    have hadd := integral_add (hFi.sub hGi) hswapi
    simp only [Pi.add_apply, Pi.sub_apply] at hadd
    rw [hadd, ← hswap] at hsum
    linarith
  rw [← hFval, ← hGval]
  have hsub : (∫ q, (F q - G q) ∂(μ.prod μ)) =
      (∫ q, F q ∂(μ.prod μ)) - ∫ q, G q ∂(μ.prod μ) := integral_sub hFi hGi
  linarith [hdiff, hsub]

end Correlation

/-! ### Step 3: assembling the weighted inequality -/

/-- The degree moments `M j = int d^j`. -/
noncomputable def moment (W : Graphon Ω μ) (j : ℕ) : ℝ :=
  ∫ x, degree W x ^ j ∂μ

section Assembly

variable (W : Graphon Ω μ)

lemma integrable_degree_pow (j : ℕ) :
    Integrable (fun x ↦ degree W x ^ j) μ :=
  integrable_of_bdd ((measurable_degree W).pow_const j) fun x ↦ by
    rw [abs_of_nonneg (pow_nonneg (degree_nonneg W x) j)]
    exact pow_le_one₀ (degree_nonneg W x) (degree_le_one W x)

/-- Three-term linearity in the degree moments. -/
lemma integral_moment_combo (a b c : ℝ) (i j k : ℕ) :
    (∫ x, (a * degree W x ^ i + b * degree W x ^ j + c * degree W x ^ k) ∂μ) =
      a * moment W i + b * moment W j + c * moment W k := by
  have h1 := (integrable_degree_pow W i).const_mul a
  have h2 := (integrable_degree_pow W j).const_mul b
  have h3 := (integrable_degree_pow W k).const_mul c
  have e1 := integral_add (h1.add h2) h3
  have e2 := integral_add h1 h2
  simp only [Pi.add_apply] at e1 e2
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul]
  rfl

/-- Adding a moment combination to an integrable function. -/
lemma integral_add_moment_combo {f : Ω → ℝ} (hf : Integrable f μ)
    (a b c : ℝ) (i j k : ℕ) :
    (∫ x, (f x +
        (a * degree W x ^ i + b * degree W x ^ j + c * degree W x ^ k)) ∂μ) =
      (∫ x, f x ∂μ) + (a * moment W i + b * moment W j + c * moment W k) := by
  have h1 := (integrable_degree_pow W i).const_mul a
  have h2 := (integrable_degree_pow W j).const_mul b
  have h3 := (integrable_degree_pow W k).const_mul c
  have e := integral_add hf ((h1.add h2).add h3)
  simp only [Pi.add_apply] at e
  rw [e, integral_moment_combo]

/-- The complement pairing, expanded. -/
lemma corrTerm_eq (x : Ω) :
    corrTerm W x = 1 - degree W x - cliqueDensity 2 W + pathOp W x := by
  have hone : Integrable (fun _ : Ω ↦ (1 : ℝ)) μ := integrable_const _
  have hW : Integrable (fun y ↦ W x y) μ :=
    integrable_of_bdd (measurable_row W.measurable x) (C := 1) fun y ↦ by
      rw [abs_of_nonneg (W.nonneg x y)]; exact W.le_one x y
  have hd : Integrable (degree W) μ := integrable_degree W
  have hWd : Integrable (fun y ↦ W x y * degree W y) μ :=
    integrable_of_bdd ((measurable_row W.measurable x).mul (measurable_degree W))
      (C := 1) fun y ↦ by
        rw [abs_of_nonneg (mul_nonneg (W.nonneg x y) (degree_nonneg W y))]
        exact mul_le_one₀ (W.le_one x y) (degree_nonneg W y) (degree_le_one W y)
  have hexp : (fun y ↦ (1 - W x y) * (1 - degree W y)) =
      fun y ↦ 1 - W x y - degree W y + W x y * degree W y := by
    funext y; ring
  rw [corrTerm, hexp]
  have s1 := integral_add ((hone.sub hW).sub hd) hWd
  have s2 := integral_sub (hone.sub hW) hd
  have s3 := integral_sub hone hW
  simp only [Pi.add_apply, Pi.sub_apply] at s1 s2 s3
  rw [s1, s2, s3, integral_degree]
  simp [degree, pathOp]

lemma measurable_rootedTriangle : Measurable (rootedTriangle W) := by
  have hg : StronglyMeasurable (fun q : (Ω × Ω) × Ω ↦
      W q.1.1 q.1.2 * W q.1.1 q.2 * W q.1.2 q.2) := by
    refine (?_ : Measurable _).stronglyMeasurable
    exact ((W.measurable.comp measurable_fst).mul
      (W.measurable.comp ((measurable_fst.comp measurable_fst).prodMk
        measurable_snd))).mul
      (W.measurable.comp ((measurable_snd.comp measurable_fst).prodMk
        measurable_snd))
  have hinner : Measurable
      (Function.uncurry fun x y ↦ ∫ z, W x y * W x z * W y z ∂μ) :=
    (hg.integral_prod_right' (ν := μ)).measurable
  exact (hinner.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

lemma rootedTriangle_le_one (x : Ω) : rootedTriangle W x ≤ 1 := by
  have hrowx : Measurable fun b ↦ W x b := measurable_row W.measurable x
  have hb : ∀ y, |∫ z, W x y * W x z * W y z ∂μ| ≤ 1 := by
    intro y
    refine abs_integral_le_of_bdd
      ((measurable_const.mul hrowx).mul (measurable_row W.measurable y))
      fun z ↦ ?_
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (W.nonneg x y) (W.nonneg x z))
      (W.nonneg y z))]
    exact mul_le_one₀ (mul_le_one₀ (W.le_one x y) (W.nonneg x z)
      (W.le_one x z)) (W.nonneg y z) (W.le_one y z)
  have hker : Measurable (Function.uncurry fun y z ↦ W x y * W x z * W y z) :=
    ((W.measurable.comp (measurable_const.prodMk measurable_fst)).mul
      (W.measurable.comp (measurable_const.prodMk measurable_snd))).mul
      W.measurable
  have hfin := abs_integral_le_of_bdd (μ := μ)
    (measurable_integral_right hker) hb
  rw [abs_le] at hfin
  exact hfin.2

/-- **The weighted rooted-triangle inequality.**  Cross-multiplied, so no
hypothesis on `p` is needed; in particular the threshold `p = 0` is covered. -/
theorem weighted_rootedTriangle (h : ℕ) :
    (2 * cliqueDensity 2 W - 1) * moment W (h + 2) ≤
      cliqueDensity 2 W * ∫ x, degree W x ^ h * rootedTriangle W x ∂μ := by
  have hp0 : 0 ≤ cliqueDensity 2 W := cliqueDensity_nonneg 2 W
  set p := cliqueDensity 2 W with hpdef
  -- integrability of the weighted integrands
  have hiP : Integrable (fun x ↦ degree W x ^ h * pathOp W x) μ :=
    integrable_of_bdd
      (((measurable_degree W).pow_const h).mul (measurable_pathOp W))
      (C := 1) fun x ↦ by
        rw [abs_of_nonneg (mul_nonneg (pow_nonneg (degree_nonneg W x) h)
          (pathOp_nonneg W x))]
        exact mul_le_one₀ (pow_le_one₀ (degree_nonneg W x) (degree_le_one W x))
          (pathOp_nonneg W x) (pathOp_le_one W x)
  have hitau : Integrable (fun x ↦ degree W x ^ h * rootedTriangle W x) μ :=
    integrable_of_bdd
      (((measurable_degree W).pow_const h).mul (measurable_rootedTriangle W))
      (C := 1) fun x ↦ by
        rw [abs_of_nonneg (mul_nonneg (pow_nonneg (degree_nonneg W x) h)
          (rootedTriangle_nonneg W x))]
        exact mul_le_one₀ (pow_le_one₀ (degree_nonneg W x) (degree_le_one W x))
          (rootedTriangle_nonneg W x) (rootedTriangle_le_one W x)
  -- (1)  Step 1, integrated
  have hre1 : (fun x ↦ degree W x ^ h * (2 * pathOp W x - p)) =
      fun x ↦ 2 * (degree W x ^ h * pathOp W x) +
        ((-p) * degree W x ^ h + 0 * degree W x ^ (h + 1) +
          0 * degree W x ^ 0) := by
    funext x; ring
  have hiC : Integrable (fun x ↦ degree W x ^ h * (2 * pathOp W x - p)) μ := by
    rw [hre1]
    exact (hiP.const_mul 2).add
      ((((integrable_degree_pow W h).const_mul (-p)).add
        ((integrable_degree_pow W (h + 1)).const_mul 0)).add
        ((integrable_degree_pow W 0).const_mul 0))
  have h1 : 2 * (∫ x, degree W x ^ h * pathOp W x ∂μ) - p * moment W h ≤
      ∫ x, degree W x ^ h * rootedTriangle W x ∂μ := by
    have hmono : (∫ x, degree W x ^ h * (2 * pathOp W x - p) ∂μ) ≤
        ∫ x, degree W x ^ h * rootedTriangle W x ∂μ :=
      integral_mono hiC hitau fun x ↦
        mul_le_mul_of_nonneg_left (rootedTriangle_ge W x)
          (pow_nonneg (degree_nonneg W x) h)
    have hval : (∫ x, degree W x ^ h * (2 * pathOp W x - p) ∂μ) =
        2 * (∫ x, degree W x ^ h * pathOp W x ∂μ) - p * moment W h := by
      rw [hre1, integral_add_moment_combo W (hiP.const_mul 2), integral_const_mul]
      ring
    linarith [hval ▸ hmono]
  -- (2)  the complement pairing in terms of the path integral
  have hre2 : (fun x ↦ degree W x ^ h * corrTerm W x) =
      fun x ↦ degree W x ^ h * pathOp W x +
        ((1 - p) * degree W x ^ h + (-1) * degree W x ^ (h + 1) +
          0 * degree W x ^ 0) := by
    funext x
    rw [corrTerm_eq W x]
    ring
  have h2 : (∫ x, degree W x ^ h * corrTerm W x ∂μ) =
      (∫ x, degree W x ^ h * pathOp W x ∂μ) +
        ((1 - p) * moment W h + (-1) * moment W (h + 1) + 0 * moment W 0) := by
    rw [hre2, integral_add_moment_combo W hiP]
  -- (3)  Step 2, with both sides expanded
  have hre3 : (fun x ↦ degree W x ^ h * (1 - degree W x) ^ 2) =
      fun x ↦ 1 * degree W x ^ h + (-2) * degree W x ^ (h + 1) +
        1 * degree W x ^ (h + 2) := by
    funext x; ring
  have h3 : moment W h - 2 * moment W (h + 1) + moment W (h + 2) ≤
      ∫ x, degree W x ^ h * corrTerm W x ∂μ := by
    have hcb := correlation_bound W h
    rw [hre3, integral_moment_combo] at hcb
    linarith
  -- (4)  the completed square
  have hre4 : (fun x ↦ degree W x ^ h * (degree W x - p) ^ 2) =
      fun x ↦ 1 * degree W x ^ (h + 2) + (-(2 * p)) * degree W x ^ (h + 1) +
        p ^ 2 * degree W x ^ h := by
    funext x; ring
  have h4 : 0 ≤ moment W (h + 2) - 2 * p * moment W (h + 1) +
      p ^ 2 * moment W h := by
    have hnn : 0 ≤ ∫ x, degree W x ^ h * (degree W x - p) ^ 2 ∂μ :=
      integral_nonneg fun x ↦
        mul_nonneg (pow_nonneg (degree_nonneg W x) h) (sq_nonneg _)
    rw [hre4, integral_moment_combo] at hnn
    linarith
  -- combine
  have h5 : 2 * moment W (h + 2) - 2 * moment W (h + 1) + p * moment W h ≤
      ∫ x, degree W x ^ h * rootedTriangle W x ∂μ := by linarith
  have h6 : p * (2 * moment W (h + 2) - 2 * moment W (h + 1) +
      p * moment W h) ≤ p * ∫ x, degree W x ^ h * rootedTriangle W x ∂μ :=
    mul_le_mul_of_nonneg_left h5 hp0
  nlinarith [h4, h6]

end Assembly

end Taeyoung.Methods.Link
