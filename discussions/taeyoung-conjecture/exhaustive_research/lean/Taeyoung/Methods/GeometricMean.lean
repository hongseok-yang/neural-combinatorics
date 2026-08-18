import Taeyoung.Methods.PathSidorenko

/-!
# The normalized-edge geometric-mean estimate

`notes/two_root_triangle_leaf_cones.tex` Lemma 2.1: with
`Z(x,y) = √(d(x)d(y))`,

```
∫∫ W(x,y)·Z(x,y) dμdμ ≥ p²,      i.e.   E_ρ[Z] ≥ p
```

under the edge-biased probability measure `dρ = (W/p)dμdμ`.  It is the new
analytic ingredient of the two-root book-edge leaf family.

The proof is two Cauchy–Schwarz steps, both of them
`ENNReal.lintegral_prod_norm_pow_le` over `Fin 2` at exponents `(½,½)`:

```
∫∫ W/Z = ∫∫ (W/d(x))^{1/2}(W/d(y))^{1/2} ≤ (∫∫W/d(x))^{1/2}(∫∫W/d(y))^{1/2} ≤ 1,
p = ∫∫ W = ∫∫ (WZ)^{1/2}(W/Z)^{1/2} ≤ (∫∫WZ)^{1/2}(∫∫W/Z)^{1/2} ≤ (∫∫WZ)^{1/2}.
```

Everything is in `ℝ≥0∞`, and the divisions by the degree are the *same* ones
path Sidorenko already had to handle: `Methods/PathSidorenko.lean` supplies
`edgeE`, `degE`, the two bounds `∫⁻ W/d ≤ 1`, and the a.e. statement that a
vertex of degree zero has a vanishing row — which is exactly what makes the
pointwise factorizations below hold almost everywhere.
-/

open MeasureTheory

open scoped ENNReal

namespace Taeyoung.Methods.GeometricMean

open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.PathSidorenko

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### `Z` in `ℝ≥0∞` -/

/-- `Z(x,y) = √(d(x)d(y))`. -/
noncomputable def geoE (W : Graphon Ω μ) (q : Ω × Ω) : ℝ≥0∞ :=
  (degE W q.1 * degE W q.2) ^ (1 / 2 : ℝ)

lemma measurable_geoE (W : Graphon Ω μ) : Measurable (geoE W) := by
  have hd : Measurable fun q : Ω × Ω ↦ degE W q.1 * degE W q.2 :=
    ((measurable_degE W).comp measurable_fst).mul
      ((measurable_degE W).comp measurable_snd)
  exact hd.pow_const _

private lemma mul_self_rpow_half (a : ℝ≥0∞) : (a * a) ^ (1 / 2 : ℝ) = a := by
  rw [← pow_two, ← ENNReal.rpow_natCast a 2, ← ENNReal.rpow_mul]
  norm_num

private lemma degE_ne_top (W : Graphon Ω μ) (x : Ω) : degE W x ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- On the support of `W`, both endpoint degrees are nonzero — the only place
the null set matters. -/
lemma ae_both (W : Graphon Ω μ) :
    ∀ᵐ q ∂(μ.prod μ), edgeE W q ≠ 0 → degE W q.1 ≠ 0 ∧ degE W q.2 ≠ 0 := by
  filter_upwards [ae_degE_ne_zero W, ae_degE_ne_zero_snd W] with q h1 h2 he
  exact ⟨h1 he, h2 he⟩

/-! ### The Hölder step, packaged

Both Cauchy–Schwarz applications below have the same shape: a pointwise a.e.
factorization of the integrand into `f₀^{1/2}·f₁^{1/2}`, and a bound on each
`∫⁻ fᵢ`.  This states that once. -/

private lemma cauchy_schwarz {g f₀ f₁ : (Ω × Ω) → ℝ≥0∞}
    (h₀ : AEMeasurable f₀ (μ.prod μ)) (h₁ : AEMeasurable f₁ (μ.prod μ))
    (hfac : ∀ᵐ q ∂(μ.prod μ), f₀ q ^ (1 / 2 : ℝ) * f₁ q ^ (1 / 2 : ℝ) = g q) :
    (∫⁻ q, g q ∂(μ.prod μ)) ≤
      (∫⁻ q, f₀ q ∂(μ.prod μ)) ^ (1 / 2 : ℝ) *
        (∫⁻ q, f₁ q ∂(μ.prod μ)) ^ (1 / 2 : ℝ) := by
  set f : Fin 2 → (Ω × Ω) → ℝ≥0∞ := fun i ↦ if i = 0 then f₀ else f₁ with hfdef
  have hf0 : f 0 = f₀ := rfl
  have hf1 : f 1 = f₁ := rfl
  have hm : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      AEMeasurable (f i) (μ.prod μ) := by
    intro i _
    simp only [hfdef]
    split_ifs <;> assumption
  have hholder := ENNReal.lintegral_prod_norm_pow_le (μ := μ.prod μ)
    (Finset.univ : Finset (Fin 2)) hm (p := fun _ ↦ (1 / 2 : ℝ))
    (by norm_num) (fun i _ ↦ by norm_num)
  rw [Fin.prod_univ_two] at hholder
  rw [hf0, hf1] at hholder
  refine le_trans (le_of_eq ?_) hholder
  refine (lintegral_congr_ae ?_).symm
  filter_upwards [hfac] with q hq
  rw [Fin.prod_univ_two, hf0, hf1]
  exact hq

/-! ### The first Cauchy–Schwarz: `∫∫ W/Z ≤ 1` -/

lemma ae_split_inv (W : Graphon Ω μ) :
    ∀ᵐ q ∂(μ.prod μ),
      (edgeE W q * (degE W q.1)⁻¹) ^ (1 / 2 : ℝ) *
          (edgeE W q * (degE W q.2)⁻¹) ^ (1 / 2 : ℝ) =
        edgeE W q * (geoE W q)⁻¹ := by
  filter_upwards [ae_both W] with q hq
  rcases eq_or_ne (edgeE W q) 0 with h0 | h0
  · rw [h0]
    simp
  · obtain ⟨hb, hc⟩ := hq h0
    have hbt := degE_ne_top W q.1
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hre : edgeE W q * (degE W q.1)⁻¹ * (edgeE W q * (degE W q.2)⁻¹) =
        edgeE W q * edgeE W q * (degE W q.1 * degE W q.2)⁻¹ := by
      rw [ENNReal.mul_inv (Or.inl hb) (Or.inl hbt)]
      ring
    rw [hre, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      mul_self_rpow_half, ENNReal.inv_rpow, geoE]

theorem lintegral_edgeE_div_geo (W : Graphon Ω μ) :
    (∫⁻ q, edgeE W q * (geoE W q)⁻¹ ∂(μ.prod μ)) ≤ 1 := by
  have hcs := cauchy_schwarz (μ := μ)
    (f₀ := fun q ↦ edgeE W q * (degE W q.1)⁻¹)
    (f₁ := fun q ↦ edgeE W q * (degE W q.2)⁻¹)
    ((measurable_edgeE W).mul
      (((measurable_degE W).comp measurable_fst).inv)).aemeasurable
    ((measurable_edgeE W).mul
      (((measurable_degE W).comp measurable_snd).inv)).aemeasurable
    (ae_split_inv W)
  have e0 : (∫⁻ q, edgeE W q * (degE W q.1)⁻¹ ∂(μ.prod μ)) ≤ 1 := by
    refine le_trans (le_of_eq ?_) (lintegral_edgeE_div_fst W)
    exact lintegral_congr fun q ↦ (div_eq_mul_inv _ _).symm
  have e1 : (∫⁻ q, edgeE W q * (degE W q.2)⁻¹ ∂(μ.prod μ)) ≤ 1 := by
    refine le_trans (le_of_eq ?_) (lintegral_edgeE_div_snd W)
    exact lintegral_congr fun q ↦ (div_eq_mul_inv _ _).symm
  refine le_trans hcs ?_
  calc (∫⁻ q, edgeE W q * (degE W q.1)⁻¹ ∂(μ.prod μ)) ^ (1 / 2 : ℝ) *
        (∫⁻ q, edgeE W q * (degE W q.2)⁻¹ ∂(μ.prod μ)) ^ (1 / 2 : ℝ)
      ≤ (1 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (1 : ℝ≥0∞) ^ (1 / 2 : ℝ) :=
        mul_le_mul' (ENNReal.rpow_le_rpow e0 (by norm_num))
          (ENNReal.rpow_le_rpow e1 (by norm_num))
    _ = 1 := by rw [ENNReal.one_rpow, mul_one]

/-! ### The second Cauchy–Schwarz -/

lemma ae_split_geo (W : Graphon Ω μ) :
    ∀ᵐ q ∂(μ.prod μ),
      (edgeE W q * geoE W q) ^ (1 / 2 : ℝ) *
          (edgeE W q * (geoE W q)⁻¹) ^ (1 / 2 : ℝ) = edgeE W q := by
  filter_upwards [ae_both W] with q hq
  rcases eq_or_ne (edgeE W q) 0 with h0 | h0
  · rw [h0]
    simp
  · obtain ⟨hb, hc⟩ := hq h0
    have hprod : degE W q.1 * degE W q.2 ≠ 0 := mul_ne_zero hb hc
    have hprodt : degE W q.1 * degE W q.2 ≠ ⊤ :=
      ENNReal.mul_ne_top (degE_ne_top W q.1) (degE_ne_top W q.2)
    have hGpos : 0 < geoE W q :=
      ENNReal.rpow_pos (pos_iff_ne_zero.mpr hprod) hprodt
    have hGt : geoE W q ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) hprodt
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hre : edgeE W q * geoE W q * (edgeE W q * (geoE W q)⁻¹) =
        edgeE W q * edgeE W q := by
      rw [show edgeE W q * geoE W q * (edgeE W q * (geoE W q)⁻¹) =
          edgeE W q * edgeE W q * (geoE W q * (geoE W q)⁻¹) by ring,
        ENNReal.mul_inv_cancel hGpos.ne' hGt, mul_one]
    rw [hre, mul_self_rpow_half]

theorem sq_le_lintegral_edgeE_geo (W : Graphon Ω μ) :
    ENNReal.ofReal (cliqueDensity 2 W) ^ (2 : ℕ) ≤
      ∫⁻ q, edgeE W q * geoE W q ∂(μ.prod μ) := by
  have hcs := cauchy_schwarz (μ := μ)
    (f₀ := fun q ↦ edgeE W q * geoE W q)
    (f₁ := fun q ↦ edgeE W q * (geoE W q)⁻¹)
    ((measurable_edgeE W).mul (measurable_geoE W)).aemeasurable
    ((measurable_edgeE W).mul (measurable_geoE W).inv).aemeasurable
    (ae_split_geo W)
  rw [lintegral_edgeE W] at hcs
  -- drop the second factor, which is at most `1`
  have hstep : ENNReal.ofReal (cliqueDensity 2 W) ≤
      (∫⁻ q, edgeE W q * geoE W q ∂(μ.prod μ)) ^ (1 / 2 : ℝ) := by
    refine le_trans hcs ?_
    calc (∫⁻ q, edgeE W q * geoE W q ∂(μ.prod μ)) ^ (1 / 2 : ℝ) *
          (∫⁻ q, edgeE W q * (geoE W q)⁻¹ ∂(μ.prod μ)) ^ (1 / 2 : ℝ)
        ≤ (∫⁻ q, edgeE W q * geoE W q ∂(μ.prod μ)) ^ (1 / 2 : ℝ) *
            (1 : ℝ≥0∞) ^ (1 / 2 : ℝ) :=
          mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (lintegral_edgeE_div_geo W)
            (by norm_num))
      _ = (∫⁻ q, edgeE W q * geoE W q ∂(μ.prod μ)) ^ (1 / 2 : ℝ) := by
          rw [ENNReal.one_rpow, mul_one]
  -- square both sides
  have hsq := pow_le_pow_left' hstep 2
  refine le_trans hsq (le_of_eq ?_)
  rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

/-! ### Back to the real integral -/

/-- `Z(x,y) = √(d(x)d(y))`, as a real function. -/
noncomputable def geoMean (W : Graphon Ω μ) (q : Ω × Ω) : ℝ :=
  Real.sqrt (degree W q.1 * degree W q.2)

lemma measurable_geoMean (W : Graphon Ω μ) : Measurable (geoMean W) :=
  Real.continuous_sqrt.measurable.comp
    (((measurable_degree W).comp measurable_fst).mul
      ((measurable_degree W).comp measurable_snd))

lemma geoMean_nonneg (W : Graphon Ω μ) (q : Ω × Ω) : 0 ≤ geoMean W q :=
  Real.sqrt_nonneg _

lemma geoMean_le_one (W : Graphon Ω μ) (q : Ω × Ω) : geoMean W q ≤ 1 := by
  rw [geoMean, show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (mul_le_one₀ (degree_le_one W _)
    (degree_nonneg W _) (degree_le_one W _))

/-- `Z² = d(x)d(y)`. -/
lemma sq_geoMean (W : Graphon Ω μ) (q : Ω × Ω) :
    geoMean W q ^ 2 = degree W q.1 * degree W q.2 :=
  Real.sq_sqrt (mul_nonneg (degree_nonneg W _) (degree_nonneg W _))

/-- **AM–GM at the two endpoints**: `2Z ≤ d(x) + d(y)`. -/
lemma two_mul_geoMean_le (W : Graphon Ω μ) (q : Ω × Ω) :
    2 * geoMean W q ≤ degree W q.1 + degree W q.2 := by
  have hsq := sq_geoMean W q
  have hnn := geoMean_nonneg W q
  nlinarith [sq_nonneg (degree W q.1 - degree W q.2),
    sq_nonneg (degree W q.1 + degree W q.2 - 2 * geoMean W q),
    degree_nonneg W q.1, degree_nonneg W q.2]

/-- The integrand as a real function: `W(x,y)·√(d(x)d(y))`. -/
noncomputable def geoIntegrand (W : Graphon Ω μ) (q : Ω × Ω) : ℝ :=
  W q.1 q.2 * geoMean W q

lemma measurable_geoIntegrand (W : Graphon Ω μ) : Measurable (geoIntegrand W) :=
  W.measurable.mul (measurable_geoMean W)

lemma geoIntegrand_nonneg (W : Graphon Ω μ) (q : Ω × Ω) :
    0 ≤ geoIntegrand W q :=
  mul_nonneg (W.nonneg _ _) (geoMean_nonneg W q)

lemma geoIntegrand_le_one (W : Graphon Ω μ) (q : Ω × Ω) :
    geoIntegrand W q ≤ 1 :=
  mul_le_one₀ (W.le_one _ _) (geoMean_nonneg W q) (geoMean_le_one W q)

lemma integrable_geoIntegrand (W : Graphon Ω μ) :
    Integrable (geoIntegrand W) (μ.prod μ) :=
  integrable_prod_of_bdd (measurable_geoIntegrand W) (C := 1) fun q ↦ by
    rw [abs_of_nonneg (geoIntegrand_nonneg W q)]
    exact geoIntegrand_le_one W q

lemma lintegral_edgeE_geo (W : Graphon Ω μ) :
    (∫⁻ q, edgeE W q * geoE W q ∂(μ.prod μ)) =
      ENNReal.ofReal (∫ q, geoIntegrand W q ∂(μ.prod μ)) := by
  have hpt : ∀ q : Ω × Ω,
      edgeE W q * geoE W q = ENNReal.ofReal (geoIntegrand W q) := by
    intro q
    simp only [edgeE, degE, geoE, geoIntegrand, geoMean, Real.sqrt_eq_rpow]
    rw [← ENNReal.ofReal_mul (degree_nonneg W q.1),
      ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg (degree_nonneg W q.1) (degree_nonneg W q.2))
        (by norm_num),
      ← ENNReal.ofReal_mul (W.nonneg _ _)]
  rw [lintegral_congr hpt]
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_geoIntegrand W)
    (ae_of_all _ (geoIntegrand_nonneg W))).symm

/-- **The geometric-mean estimate.**  `∫∫ W(x,y)√(d(x)d(y)) ≥ p²`; equivalently
`E_ρ[√(d(x)d(y))] ≥ p` under the edge-biased measure. -/
theorem sq_le_integral_geoIntegrand (W : Graphon Ω μ) :
    cliqueDensity 2 W ^ 2 ≤ ∫ q, geoIntegrand W q ∂(μ.prod μ) := by
  have hkey := sq_le_lintegral_edgeE_geo W
  rw [lintegral_edgeE_geo W,
    ← ENNReal.ofReal_pow (cliqueDensity_nonneg 2 W)] at hkey
  have hnn : 0 ≤ ∫ q, geoIntegrand W q ∂(μ.prod μ) :=
    integral_nonneg (geoIntegrand_nonneg W)
  exact (ENNReal.ofReal_le_ofReal_iff hnn).mp hkey

end Taeyoung.Methods.GeometricMean
