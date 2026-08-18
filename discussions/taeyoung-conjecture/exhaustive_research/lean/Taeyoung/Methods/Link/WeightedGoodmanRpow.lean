import Taeyoung.Methods.Link.WeightedGoodman
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Integral

/-!
# The weighted rooted-triangle inequality at a real exponent

`notes/page_rooted_triangle_book_leaves.tex` compresses `m` page moments to a
single one at the *average* exponent `α = (k₁ + ⋯ + k_m)/m`, which is not an
integer.  Its Lemma 2.2 therefore states the weighted rooted-triangle
inequality for every real `h ≥ 0`, and remarks that the proof of the integer
case never used integrality — only that `s ↦ sʰ` is nondecreasing on `[0,1]`.

This file is that port.  It *adds* `weighted_rootedTriangle_rpow` alongside the
`ℕ`-indexed `weighted_rootedTriangle`, which the clique common-leaf and cone
families consume unchanged.

Two conventions matter.  `Real.rpow` sets `0 ^ (0 : ℝ) = 1`, which is exactly
the note's convention `d⁰ = 1` including where the degree vanishes.  And the
splitting `d^(s+2) = d^s·d²` is `Real.rpow_add'`, whose side condition is
`s + 2 ≠ 0` rather than `0 < d`; that is what keeps the degenerate set harmless.
-/

open MeasureTheory

namespace Taeyoung.Methods.Link

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The degree at a real power -/

lemma measurable_degree_rpow (W : Graphon Ω μ) {s : ℝ} (hs : 0 ≤ s) :
    Measurable fun x ↦ degree W x ^ s :=
  (Real.continuous_rpow_const hs).measurable.comp (measurable_degree W)

lemma degree_rpow_nonneg (W : Graphon Ω μ) (s : ℝ) (x : Ω) :
    0 ≤ degree W x ^ s :=
  Real.rpow_nonneg (degree_nonneg W x) s

lemma degree_rpow_le_one (W : Graphon Ω μ) {s : ℝ} (hs : 0 ≤ s) (x : Ω) :
    degree W x ^ s ≤ 1 :=
  Real.rpow_le_one (degree_nonneg W x) (degree_le_one W x) hs

lemma integrable_degree_rpow (W : Graphon Ω μ) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun x ↦ degree W x ^ s) μ :=
  integrable_of_bdd (measurable_degree_rpow W hs) fun x ↦ by
    rw [abs_of_nonneg (degree_rpow_nonneg W s x)]
    exact degree_rpow_le_one W hs x

/-- `d^(s+1) = d^s·d`, valid at `d = 0` because `s + 1 ≠ 0`. -/
lemma degree_rpow_succ (W : Graphon Ω μ) {s : ℝ} (hs : 0 ≤ s) (x : Ω) :
    degree W x ^ (s + 1) = degree W x ^ s * degree W x := by
  rw [Real.rpow_add' (degree_nonneg W x) (by linarith), Real.rpow_one]

/-- `d^(s+2) = d^s·d²`, valid at `d = 0` because `s + 2 ≠ 0`. -/
lemma degree_rpow_add_two (W : Graphon Ω μ) {s : ℝ} (hs : 0 ≤ s) (x : Ω) :
    degree W x ^ (s + 2) = degree W x ^ s * degree W x ^ 2 := by
  rw [Real.rpow_add' (degree_nonneg W x) (by linarith), Real.rpow_two]

/-! ### The moments -/

/-- `M_s = ∫ dˢ` at a real exponent. -/
noncomputable def momentR (W : Graphon Ω μ) (s : ℝ) : ℝ :=
  ∫ x, degree W x ^ s ∂μ

lemma momentR_natCast (W : Graphon Ω μ) (j : ℕ) :
    momentR W (j : ℝ) = moment W j := by
  rw [momentR, moment]
  exact integral_congr_ae (ae_of_all _ fun x ↦ Real.rpow_natCast _ j)

/-- **Jensen at a real exponent.**  `M_s ≥ pˢ` for `s ≥ 1`. -/
theorem rpow_le_momentR (W : Graphon Ω μ) {s : ℝ} (hs : 1 ≤ s) :
    cliqueDensity 2 W ^ s ≤ momentR W s := by
  have hj := ConvexOn.map_integral_le (μ := μ) (s := Set.Ici 0)
    (g := fun t : ℝ ↦ t ^ s) (f := degree W) (convexOn_rpow hs)
    ((Real.continuous_rpow_const (by linarith)).continuousOn) isClosed_Ici
    (ae_of_all _ fun x ↦ degree_nonneg W x)
    (integrable_degree W) (integrable_degree_rpow W (by linarith))
  rwa [integral_degree] at hj

/-- Three-term linearity in the real-exponent moments. -/
lemma integral_rpow_combo (W : Graphon Ω μ) {s : ℝ} (hs : 0 ≤ s) (a b c : ℝ) :
    (∫ x, (a * degree W x ^ s + b * degree W x ^ (s + 1) +
        c * degree W x ^ (s + 2)) ∂μ) =
      a * momentR W s + b * momentR W (s + 1) + c * momentR W (s + 2) := by
  have h1 := (integrable_degree_rpow W hs).const_mul a
  have h2 := (integrable_degree_rpow W (by linarith : (0:ℝ) ≤ s + 1)).const_mul b
  have h3 := (integrable_degree_rpow W (by linarith : (0:ℝ) ≤ s + 2)).const_mul c
  have e1 := integral_add (h1.add h2) h3
  have e2 := integral_add h1 h2
  simp only [Pi.add_apply] at e1 e2
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul]
  rfl

lemma integral_add_rpow_combo (W : Graphon Ω μ) {s : ℝ} (hs : 0 ≤ s)
    {f : Ω → ℝ} (hf : Integrable f μ) (a b c : ℝ) :
    (∫ x, (f x + (a * degree W x ^ s + b * degree W x ^ (s + 1) +
        c * degree W x ^ (s + 2))) ∂μ) =
      (∫ x, f x ∂μ) +
        (a * momentR W s + b * momentR W (s + 1) + c * momentR W (s + 2)) := by
  have h1 := (integrable_degree_rpow W hs).const_mul a
  have h2 := (integrable_degree_rpow W (by linarith : (0:ℝ) ≤ s + 1)).const_mul b
  have h3 := (integrable_degree_rpow W (by linarith : (0:ℝ) ≤ s + 2)).const_mul c
  have e := integral_add hf ((h1.add h2).add h3)
  simp only [Pi.add_apply] at e
  rw [e, integral_rpow_combo W hs]

/-! ### The correlation bound at a real exponent -/

/-- `a ↦ aˢ` is nondecreasing on `[0,∞)`, so `a - b` and `aˢ - bˢ` agree in
sign.  This is the only place integrality of the exponent was ever used. -/
lemma sub_mul_rpow_sub_nonneg {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : 0 ≤ s) : 0 ≤ (a - b) * (a ^ s - b ^ s) := by
  rcases le_total b a with hab | hab
  · exact mul_nonneg (by linarith) (by linarith [Real.rpow_le_rpow hb hab hs])
  · nlinarith [Real.rpow_le_rpow ha hab hs]

theorem correlation_bound_rpow (W : Graphon Ω μ) {s : ℝ} (hs : 0 ≤ s) :
    (∫ x, degree W x ^ s * (1 - degree W x) ^ 2 ∂μ) ≤
      ∫ x, degree W x ^ s * corrTerm W x ∂μ := by
  set F : Ω × Ω → ℝ :=
    fun q ↦ (1 - W q.1 q.2) * (degree W q.1 ^ s * (1 - degree W q.2)) with hF
  set G : Ω × Ω → ℝ :=
    fun q ↦ (1 - W q.1 q.2) * (degree W q.1 ^ s * (1 - degree W q.1)) with hG
  have hdeg1 : Measurable fun q : Ω × Ω ↦ degree W q.1 ^ s :=
    (measurable_degree_rpow W hs).comp measurable_fst
  have hcompl : Measurable fun q : Ω × Ω ↦ 1 - W q.1 q.2 :=
    measurable_const.sub W.measurable
  have hFm : Measurable F :=
    hcompl.mul (hdeg1.mul (measurable_const.sub
      ((measurable_degree W).comp measurable_snd)))
  have hGm : Measurable G :=
    hcompl.mul (hdeg1.mul (measurable_const.sub
      ((measurable_degree W).comp measurable_fst)))
  have hbd : ∀ (a b c : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → 0 ≤ c → c ≤ 1 →
      |(1 - a) * (b * (1 - c))| ≤ 1 := by
    intro a b c h1 h2 h3 h4 h5 h6
    have hnn : 0 ≤ (1 - a) * (b * (1 - c)) :=
      mul_nonneg (by linarith) (mul_nonneg h3 (by linarith))
    rw [abs_of_nonneg hnn]
    exact mul_le_one₀ (by linarith) (mul_nonneg h3 (by linarith))
      (mul_le_one₀ h4 (by linarith) (by linarith))
  have hFb : ∀ q, |F q| ≤ 1 := fun q ↦ hbd _ _ _ (W.nonneg _ _) (W.le_one _ _)
    (degree_rpow_nonneg W s _) (degree_rpow_le_one W hs _)
    (degree_nonneg W _) (degree_le_one W _)
  have hGb : ∀ q, |G q| ≤ 1 := fun q ↦ hbd _ _ _ (W.nonneg _ _) (W.le_one _ _)
    (degree_rpow_nonneg W s _) (degree_rpow_le_one W hs _)
    (degree_nonneg W _) (degree_le_one W _)
  have hFi : Integrable F (μ.prod μ) := integrable_prod_of_bdd hFm hFb
  have hGi : Integrable G (μ.prod μ) := integrable_prod_of_bdd hGm hGb
  have hFval : (∫ q, F q ∂(μ.prod μ)) =
      ∫ x, degree W x ^ s * corrTerm W x ∂μ := by
    have hFi' : Integrable (Function.uncurry fun a b ↦
        (1 - W a b) * (degree W a ^ s * (1 - degree W b))) (μ.prod μ) := hFi
    rw [← integral_integral hFi']
    refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
    simp only []
    rw [corrTerm, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun b ↦ by ring)
  have hGval : (∫ q, G q ∂(μ.prod μ)) =
      ∫ x, degree W x ^ s * (1 - degree W x) ^ 2 ∂μ := by
    have hGi' : Integrable (Function.uncurry fun a b ↦
        (1 - W a b) * (degree W a ^ s * (1 - degree W a))) (μ.prod μ) := hGi
    rw [← integral_integral hGi']
    refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
    simp only []
    have hconst : (∫ b, (1 - W a b) * (degree W a ^ s * (1 - degree W a)) ∂μ) =
        (degree W a ^ s * (1 - degree W a)) * ∫ b, (1 - W a b) ∂μ := by
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
  have hswap : (∫ q, (F q - G q) ∂(μ.prod μ)) =
      ∫ q, (F q.swap - G q.swap) ∂(μ.prod μ) :=
    (integral_prod_swap (fun q ↦ F q - G q)).symm
  have hsum : 0 ≤ ∫ q, ((F q - G q) + (F q.swap - G q.swap)) ∂(μ.prod μ) := by
    refine integral_nonneg fun q ↦ ?_
    have hkey : (F q - G q) + (F q.swap - G q.swap) =
        (1 - W q.1 q.2) *
          ((degree W q.1 - degree W q.2) *
            (degree W q.1 ^ s - degree W q.2 ^ s)) := by
      simp only [hF, hG, Prod.fst_swap, Prod.snd_swap]
      rw [W.symm q.2 q.1]
      ring
    rw [hkey]
    exact mul_nonneg (by linarith [W.le_one q.1 q.2])
      (sub_mul_rpow_sub_nonneg (degree_nonneg W q.1) (degree_nonneg W q.2) hs)
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

/-! ### The inequality -/

/-- **The weighted rooted-triangle inequality at a real exponent.**  Stated
cross-multiplied, as in the `ℕ` case, so that `p = 0` needs no separate
treatment. -/
theorem weighted_rootedTriangle_rpow (W : Graphon Ω μ) {s : ℝ} (hs : 0 ≤ s) :
    (2 * cliqueDensity 2 W - 1) * momentR W (s + 2) ≤
      cliqueDensity 2 W * ∫ x, degree W x ^ s * rootedTriangle W x ∂μ := by
  have hp0 : 0 ≤ cliqueDensity 2 W := cliqueDensity_nonneg 2 W
  set p := cliqueDensity 2 W with hpdef
  have hiP : Integrable (fun x ↦ degree W x ^ s * pathOp W x) μ :=
    integrable_of_bdd ((measurable_degree_rpow W hs).mul (measurable_pathOp W))
      (C := 1) fun x ↦ by
        rw [abs_of_nonneg (mul_nonneg (degree_rpow_nonneg W s x)
          (pathOp_nonneg W x))]
        exact mul_le_one₀ (degree_rpow_le_one W hs x) (pathOp_nonneg W x)
          (pathOp_le_one W x)
  have hitau : Integrable (fun x ↦ degree W x ^ s * rootedTriangle W x) μ :=
    integrable_of_bdd
      ((measurable_degree_rpow W hs).mul (measurable_rootedTriangle W))
      (C := 1) fun x ↦ by
        rw [abs_of_nonneg (mul_nonneg (degree_rpow_nonneg W s x)
          (rootedTriangle_nonneg W x))]
        exact mul_le_one₀ (degree_rpow_le_one W hs x) (rootedTriangle_nonneg W x)
          (rootedTriangle_le_one W x)
  -- (1) the pointwise Goodman bound, integrated
  have hre1 : (fun x ↦ degree W x ^ s * (2 * pathOp W x - p)) =
      fun x ↦ 2 * (degree W x ^ s * pathOp W x) +
        ((-p) * degree W x ^ s + 0 * degree W x ^ (s + 1) +
          0 * degree W x ^ (s + 2)) := by
    funext x; ring
  have hiC : Integrable (fun x ↦ degree W x ^ s * (2 * pathOp W x - p)) μ := by
    rw [hre1]
    exact (hiP.const_mul 2).add
      ((((integrable_degree_rpow W hs).const_mul (-p)).add
        ((integrable_degree_rpow W (by linarith : (0:ℝ) ≤ s + 1)).const_mul 0)).add
        ((integrable_degree_rpow W (by linarith : (0:ℝ) ≤ s + 2)).const_mul 0))
  have h1 : 2 * (∫ x, degree W x ^ s * pathOp W x ∂μ) - p * momentR W s ≤
      ∫ x, degree W x ^ s * rootedTriangle W x ∂μ := by
    have hmono : (∫ x, degree W x ^ s * (2 * pathOp W x - p) ∂μ) ≤
        ∫ x, degree W x ^ s * rootedTriangle W x ∂μ :=
      integral_mono hiC hitau fun x ↦
        mul_le_mul_of_nonneg_left (rootedTriangle_ge W x) (degree_rpow_nonneg W s x)
    have hval : (∫ x, degree W x ^ s * (2 * pathOp W x - p) ∂μ) =
        2 * (∫ x, degree W x ^ s * pathOp W x ∂μ) - p * momentR W s := by
      rw [hre1, integral_add_rpow_combo W hs (hiP.const_mul 2), integral_const_mul]
      ring
    linarith [hval ▸ hmono]
  -- (2) the complement pairing
  have hre2 : (fun x ↦ degree W x ^ s * corrTerm W x) =
      fun x ↦ degree W x ^ s * pathOp W x +
        ((1 - p) * degree W x ^ s + (-1) * degree W x ^ (s + 1) +
          0 * degree W x ^ (s + 2)) := by
    funext x
    rw [corrTerm_eq W x, degree_rpow_succ W hs x]
    ring
  have h2 : (∫ x, degree W x ^ s * corrTerm W x ∂μ) =
      (∫ x, degree W x ^ s * pathOp W x ∂μ) +
        ((1 - p) * momentR W s + (-1) * momentR W (s + 1) +
          0 * momentR W (s + 2)) := by
    rw [hre2, integral_add_rpow_combo W hs hiP]
  -- (3) the correlation bound, expanded
  have hre3 : (fun x ↦ degree W x ^ s * (1 - degree W x) ^ 2) =
      fun x ↦ 1 * degree W x ^ s + (-2) * degree W x ^ (s + 1) +
        1 * degree W x ^ (s + 2) := by
    funext x
    rw [degree_rpow_succ W hs x, degree_rpow_add_two W hs x]
    ring
  have h3 : momentR W s - 2 * momentR W (s + 1) + momentR W (s + 2) ≤
      ∫ x, degree W x ^ s * corrTerm W x ∂μ := by
    have hcb := correlation_bound_rpow W hs
    rw [hre3, integral_rpow_combo W hs] at hcb
    linarith
  -- (4) the completed square
  have hre4 : (fun x ↦ degree W x ^ s * (degree W x - p) ^ 2) =
      fun x ↦ p ^ 2 * degree W x ^ s + (-(2 * p)) * degree W x ^ (s + 1) +
        1 * degree W x ^ (s + 2) := by
    funext x
    rw [degree_rpow_succ W hs x, degree_rpow_add_two W hs x]
    ring
  have h4 : 0 ≤ momentR W (s + 2) - 2 * p * momentR W (s + 1) +
      p ^ 2 * momentR W s := by
    have hnn : 0 ≤ ∫ x, degree W x ^ s * (degree W x - p) ^ 2 ∂μ :=
      integral_nonneg fun x ↦
        mul_nonneg (degree_rpow_nonneg W s x) (sq_nonneg _)
    rw [hre4, integral_rpow_combo W hs] at hnn
    linarith
  have h5 : 2 * momentR W (s + 2) - 2 * momentR W (s + 1) + p * momentR W s ≤
      ∫ x, degree W x ^ s * rootedTriangle W x ∂μ := by linarith
  have h6 : p * (2 * momentR W (s + 2) - 2 * momentR W (s + 1) +
      p * momentR W s) ≤ p * ∫ x, degree W x ^ s * rootedTriangle W x ∂μ :=
    mul_le_mul_of_nonneg_left h5 hp0
  nlinarith [h4, h6]

end Taeyoung.Methods.Link
