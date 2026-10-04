import ApicesCommonness.Cycles.Equality.Functionals

/-!
# A vanishing fourth signed cycle forces `W = 1/2`

Blueprint `lem:c-zero`, by the finite-rank `L²` route of plan D9 (no dyadic cells).  With
`U = 2W − 1` and `K₂ = U ∘ U`:

1. `c = t(C₄, U) = trace (K₂ ∘ K₂) = ∫∫ K₂²` (`graphonC_eq_integral_sq`), so `c = 0` gives `K₂ = 0`
   almost everywhere;
2. for bounded measurable `φ`, `g = Tφ` has `∫ g² = ⟨φ, T²φ⟩ = ⟨φ, K₂φ⟩ = 0`, so `Tφ = 0` a.e. and
   `∫∫ U(x,y) ψ(x) φ(y) = 0` for bounded measurable `ψ` (`integral_U_mul_eq_zero`);
3. a finite-rank kernel `V = ∑ⱼ aⱼ(x) bⱼ(y)` within `L²` distance `δ` of `U` (`exists_finiteRank_sq_close`)
   has `∫ UV = 0`, hence `∫ U² = ∫ U(U − V) ≤ ½∫U² + ½∫(U − V)²`, i.e. `∫ U² ≤ ∫ (U − V)² < δ`;
   so `∫ U² = 0` and `U = 0` almost everywhere (`signedKernel_ae_zero_of_graphonC`).
-/

open MeasureTheory

set_option linter.unusedSectionVars false

namespace ApicesCommonness

open Foundation SimpleGraph Foundation.Spectral.L2Kernel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma goodK_signedKernel {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) : GoodK (signedKernel W) :=
  ⟨measurable_signedKernel hW, 1, zero_le_one, abs_signedKernel_le hW⟩

lemma signedKernel_symm {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) (x y : Ω) :
    signedKernel W x y = signedKernel W y x := by
  simp only [signedKernel, hW.symm x y]

/-- A bounded measurable function on `Ω × Ω` is integrable for `μ.prod μ`. -/
private lemma integrable_of_bdd {f : Ω × Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ p, |f p| ≤ C) : Integrable f (μ.prod μ) :=
  (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ fun p => by
    rw [Real.norm_eq_abs]; exact hC p)

/-! ### `c = ∫∫ K₂²` -/

/-- `t(C₄, U) = trace ((U ∘ U) ∘ (U ∘ U))`. -/
theorem graphonC_eq_trace {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) :
    graphonC μ W = trace μ (comp μ (comp μ (signedKernel W) (signedKernel W))
      (comp μ (signedKernel W) (signedKernel W))) := by
  set U := signedKernel W with hU
  have hUg : GoodK U := goodK_signedKernel hW
  have hcyc : graphonC μ W = cycleDensity U μ 4 := by
    rw [cycleDensity_eq_integral hUg 3, graphonC, signedDensity, homDensity_eq_integral_edgeProd]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    dsimp only
    rw [edgeProd, edgePairs_cycleGraph_four, c4Edges, Fin.prod_univ_four]
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_singleton]
    rw [show (3 : Fin 4) + 1 = 0 by decide, show (0 : Fin 4) + 1 = 1 by decide,
      show (1 : Fin 4) + 1 = 2 by decide, show (2 : Fin 4) + 1 = 3 by decide,
      show U (v 3) (v 0) = U (v 0) (v 3) from signedKernel_symm hW (v 3) (v 0)]
    ring
  rw [hcyc, cycleDensity, show 4 - 1 = 3 from rfl, compPow, compPow, compPow, compPow,
    comp_assoc hUg hUg (goodK_comp hUg hUg)]

/-- `K₂ = U ∘ U` is symmetric. -/
lemma comp_signed_symm {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) (x z : Ω) :
    comp μ (signedKernel W) (signedKernel W) z x = comp μ (signedKernel W) (signedKernel W) x z := by
  simp only [comp]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  show signedKernel W z y * signedKernel W y x = signedKernel W x y * signedKernel W y z
  rw [signedKernel_symm hW z y, signedKernel_symm hW y x]
  ring

/-- **`c = ∫∫ K₂²`.** -/
theorem graphonC_eq_integral_sq {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) :
    graphonC μ W = ∫ p, comp μ (signedKernel W) (signedKernel W) p.1 p.2 ^ 2 ∂(μ.prod μ) := by
  set K₂ := comp μ (signedKernel W) (signedKernel W) with hK₂
  have hK : GoodK K₂ := goodK_comp (goodK_signedKernel hW) (goodK_signedKernel hW)
  obtain ⟨C, _, hC⟩ := hK.bdd
  have hint : Integrable (fun p : Ω × Ω => K₂ p.1 p.2 ^ 2) (μ.prod μ) :=
    integrable_of_bdd (hK.meas.pow_const 2) (C := C ^ 2) fun p => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC p.1 p.2) 2
  rw [graphonC_eq_trace hW, integral_prod _ hint, trace]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [comp]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  show K₂ x z * K₂ z x = K₂ x z ^ 2
  rw [hK₂, comp_signed_symm hW x z, sq]

/-- `c = 0` forces `K₂ = 0` almost everywhere. -/
lemma comp_signed_ae_zero {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) (hc : graphonC μ W = 0) :
    (fun p : Ω × Ω => comp μ (signedKernel W) (signedKernel W) p.1 p.2) =ᵐ[μ.prod μ] 0 := by
  have hK : GoodK (comp μ (signedKernel W) (signedKernel W)) :=
    goodK_comp (goodK_signedKernel hW) (goodK_signedKernel hW)
  obtain ⟨C, _, hC⟩ := hK.bdd
  have hint : Integrable (fun p : Ω × Ω => comp μ (signedKernel W) (signedKernel W) p.1 p.2 ^ 2)
      (μ.prod μ) :=
    integrable_of_bdd (hK.meas.pow_const 2) (C := C ^ 2) fun p => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC p.1 p.2) 2
  rw [graphonC_eq_integral_sq hW] at hc
  have h0 := (integral_eq_zero_iff_of_nonneg (fun p => sq_nonneg _) hint).mp hc
  filter_upwards [h0] with p hp
  simpa using hp

/-! ### Bilinear forms of `U` vanish -/

/-- `T` is self-adjoint on bounded functions: `∫ (Tφ) ψ = ∫ φ (Tψ)`. -/
lemma integral_kernelOp_mul {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) {φ ψ : Ω → ℝ} (hφ : Good φ)
    (hψ : Good ψ) :
    ∫ x, kernelOp (signedKernel W) μ φ x * ψ x ∂μ
      = ∫ y, φ y * kernelOp (signedKernel W) μ ψ y ∂μ := by
  set U := signedKernel W
  obtain ⟨Cφ, hCφ0, hCφ⟩ := hφ.bdd
  obtain ⟨Cψ, hCψ0, hCψ⟩ := hψ.bdd
  have hm : Measurable (Function.uncurry fun x y => U x y * φ y * ψ x) :=
    ((measurable_signedKernel hW).mul (hφ.meas.measurable.comp measurable_snd)).mul
      (hψ.meas.measurable.comp measurable_fst)
  have hint : Integrable (Function.uncurry fun x y => U x y * φ y * ψ x) (μ.prod μ) :=
    integrable_of_bdd hm (C := Cφ * Cψ) fun p => by
      simp only [Function.uncurry, abs_mul]
      have := abs_signedKernel_le hW p.1 p.2
      have h1 := hCφ p.2
      have h2 := hCψ p.1
      calc |U p.1 p.2| * |φ p.2| * |ψ p.1| ≤ 1 * Cφ * Cψ := by gcongr
        _ = Cφ * Cψ := by ring
  have hl : ∀ x, kernelOp U μ φ x * ψ x = ∫ y, U x y * φ y * ψ x ∂μ := fun x => by
    rw [kernelOp, ← integral_mul_const]
  have hr : ∀ y, φ y * kernelOp U μ ψ y = ∫ x, U x y * φ y * ψ x ∂μ := fun y => by
    rw [kernelOp, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show φ y * (U y x * ψ x) = U x y * φ y * ψ x
    rw [show U y x = U x y from signedKernel_symm hW y x]
    ring
  simp_rw [hl, hr]
  exact integral_integral_swap hint

/-- If `K₂ = 0` a.e., then `Tφ = 0` a.e. for every bounded measurable `φ`. -/
lemma kernelOp_ae_zero {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) (hc : graphonC μ W = 0) {φ : Ω → ℝ}
    (hφ : Good φ) : kernelOp (signedKernel W) μ φ =ᵐ[μ] 0 := by
  set U := signedKernel W
  have hUg : GoodK U := goodK_signedKernel hW
  set g := kernelOp U μ φ with hg
  have hgood : Good g := good_kernelOp_goodK hUg hφ
  -- `T g = K₂ φ = 0` a.e.
  have hK₂ := comp_signed_ae_zero hW hc
  have hTg : kernelOp U μ g =ᵐ[μ] 0 := by
    have hcomp := kernelOp_comp_eq_kernelOp_kernelOp (mu := μ) hUg hUg hφ
    have hx : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, comp μ U U x y = 0 := Measure.ae_ae_of_ae_prod hK₂
    filter_upwards [hx] with x hxy
    show kernelOp U μ (kernelOp U μ φ) x = 0
    rw [← hcomp]
    show ∫ y, comp μ U U x y * φ y ∂μ = 0
    rw [integral_eq_zero_of_ae]
    filter_upwards [hxy] with y hy
    simp [hy]
  -- `∫ g² = ∫ φ (T g) = 0`
  have hsq : ∫ x, g x * g x ∂μ = 0 := by
    rw [integral_kernelOp_mul hW hφ hgood]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hTg] with y hy
    have hy' : kernelOp (signedKernel W) μ g y = 0 := hy
    simp [hy']
  obtain ⟨Cg, _, hCg⟩ := hgood.bdd
  have hint : Integrable (fun x => g x * g x) μ :=
    (integrable_const (Cg * Cg)).mono' (hgood.meas.mul hgood.meas).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hCg x) (hCg x) (abs_nonneg _) (le_trans (abs_nonneg _) (hCg x)))
  have h0 := (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (g x)) hint).mp hsq
  filter_upwards [h0] with x hx
  exact mul_self_eq_zero.mp hx

/-- **`∫∫ U(x,y) ψ(x) φ(y) = 0`** for bounded measurable `φ, ψ`, when `c = 0`. -/
theorem integral_U_mul_eq_zero {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) (hc : graphonC μ W = 0)
    {φ ψ : Ω → ℝ} (hφ : Good φ) (hψ : Good ψ) :
    ∫ p, signedKernel W p.1 p.2 * (ψ p.1 * φ p.2) ∂(μ.prod μ) = 0 := by
  set U := signedKernel W
  obtain ⟨Cφ, _, hCφ⟩ := hφ.bdd
  obtain ⟨Cψ, _, hCψ⟩ := hψ.bdd
  have hm : Measurable fun p : Ω × Ω => U p.1 p.2 * (ψ p.1 * φ p.2) :=
    (measurable_signedKernel hW).mul ((hψ.meas.measurable.comp measurable_fst).mul
      (hφ.meas.measurable.comp measurable_snd))
  have hint : Integrable (fun p : Ω × Ω => U p.1 p.2 * (ψ p.1 * φ p.2)) (μ.prod μ) :=
    integrable_of_bdd hm (C := Cψ * Cφ) fun p => by
      rw [abs_mul, abs_mul]
      have := abs_signedKernel_le hW p.1 p.2
      calc |U p.1 p.2| * (|ψ p.1| * |φ p.2|) ≤ 1 * (Cψ * Cφ) := by
            gcongr
            · exact hCψ p.1
            · exact hCφ p.2
        _ = Cψ * Cφ := one_mul _
  rw [integral_prod _ hint]
  have hT := kernelOp_ae_zero hW hc hφ
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hT] with x hx
  have : ∫ y, U x y * (ψ x * φ y) ∂μ = ψ x * kernelOp U μ φ x := by
    rw [kernelOp, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun y => by ring)
  simp only [Pi.zero_apply] at hx ⊢
  rw [this, hx, mul_zero]

/-! ### `U = 0` almost everywhere -/

/-- **`lem:c-zero`, main direction.**  If `t(C₄, U) = 0` then `U = 0` almost everywhere. -/
theorem signedKernel_ae_zero_of_graphonC {W : Ω → Ω → ℝ} (hW : IsGraphon W μ)
    (hc : graphonC μ W = 0) :
    (fun p : Ω × Ω => signedKernel W p.1 p.2) =ᵐ[μ.prod μ] 0 := by
  set U := signedKernel W
  have hUg : GoodK U := goodK_signedKernel hW
  have hUm : Measurable fun p : Ω × Ω => U p.1 p.2 := measurable_signedKernel hW
  have hint2 : Integrable (fun p : Ω × Ω => U p.1 p.2 ^ 2) (μ.prod μ) :=
    integrable_of_bdd (hUm.pow_const 2) (C := 1) fun p => by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (abs_signedKernel_le hW p.1 p.2)
  -- `∫ U² < δ` for every `δ > 0`
  have hsmall : ∀ δ > 0, ∫ p, U p.1 p.2 ^ 2 ∂(μ.prod μ) ≤ δ := by
    intro δ hδ
    obtain ⟨J, hJ, V, a, b, hVg, ha, hb, -, -, hV, hclose⟩ :=
      exists_finiteRank_sq_close (μ := μ) hUg hδ
    obtain ⟨CV, _, hCV⟩ := hVg.bdd
    have hVm : Measurable fun p : Ω × Ω => V p.1 p.2 := hVg.meas
    -- `∫ U V = 0`
    have hUV : ∫ p, U p.1 p.2 * V p.1 p.2 ∂(μ.prod μ) = 0 := by
      have hterm : ∀ j, ∫ p, U p.1 p.2 * (a j p.1 * b j p.2) ∂(μ.prod μ) = 0 := fun j =>
        integral_U_mul_eq_zero hW hc (hb j) (ha j)
      have hsum : (fun p : Ω × Ω => U p.1 p.2 * V p.1 p.2)
          = fun p => ∑ j, U p.1 p.2 * (a j p.1 * b j p.2) := by
        funext p
        rw [hV, Finset.mul_sum]
      rw [hsum, integral_finsetSum]
      · exact Finset.sum_eq_zero fun j _ => hterm j
      · intro j _
        obtain ⟨Ca, _, hCa⟩ := (ha j).bdd
        obtain ⟨Cb, _, hCb⟩ := (hb j).bdd
        refine integrable_of_bdd (hUm.mul (((ha j).meas.measurable.comp measurable_fst).mul
          ((hb j).meas.measurable.comp measurable_snd))) (C := Ca * Cb) fun p => ?_
        rw [abs_mul, abs_mul]
        have := abs_signedKernel_le hW p.1 p.2
        calc |U p.1 p.2| * (|a j p.1| * |b j p.2|) ≤ 1 * (Ca * Cb) := by
              gcongr
              · exact hCa p.1
              · exact hCb p.2
          _ = Ca * Cb := one_mul _
    -- `U² ≤ U(U − V) + ... ` pointwise: `U² = U(U − V) + UV ≤ (U² + (U − V)²)/2 + UV`
    have hint3 : Integrable (fun p : Ω × Ω => (U p.1 p.2 - V p.1 p.2) ^ 2) (μ.prod μ) :=
      integrable_of_bdd ((hUm.sub hVm).pow_const 2) (C := (1 + CV) ^ 2) fun p => by
        rw [abs_pow]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        calc |U p.1 p.2 - V p.1 p.2| ≤ |U p.1 p.2| + |V p.1 p.2| := abs_sub _ _
          _ ≤ 1 + CV := add_le_add (abs_signedKernel_le hW p.1 p.2) (hCV p.1 p.2)
    have hintUV : Integrable (fun p : Ω × Ω => U p.1 p.2 * V p.1 p.2) (μ.prod μ) :=
      integrable_of_bdd (hUm.mul hVm) (C := CV) fun p => by
        rw [abs_mul]
        calc |U p.1 p.2| * |V p.1 p.2| ≤ 1 * CV :=
              mul_le_mul (abs_signedKernel_le hW p.1 p.2) (hCV p.1 p.2) (abs_nonneg _) zero_le_one
          _ = CV := one_mul _
    have h1 : ∫ p, U p.1 p.2 ^ 2 ∂(μ.prod μ)
        = ∫ p, (U p.1 p.2 ^ 2 - U p.1 p.2 * V p.1 p.2) ∂(μ.prod μ) := by
      rw [integral_sub hint2 hintUV, hUV, sub_zero]
    have h2 : ∫ p, (U p.1 p.2 ^ 2 - U p.1 p.2 * V p.1 p.2) ∂(μ.prod μ)
        ≤ ∫ p, (U p.1 p.2 ^ 2 + (U p.1 p.2 - V p.1 p.2) ^ 2) / 2 ∂(μ.prod μ) :=
      integral_mono (hint2.sub hintUV) ((hint2.add hint3).div_const 2) fun p => by
        nlinarith [sq_nonneg (V p.1 p.2)]
    have h3 : ∫ p, (U p.1 p.2 ^ 2 + (U p.1 p.2 - V p.1 p.2) ^ 2) / 2 ∂(μ.prod μ)
        = (∫ p, U p.1 p.2 ^ 2 ∂(μ.prod μ) + ∫ p, (U p.1 p.2 - V p.1 p.2) ^ 2 ∂(μ.prod μ)) / 2 := by
      rw [integral_div, integral_add hint2 hint3]
    have hclose' : ∫ p, (U p.1 p.2 - V p.1 p.2) ^ 2 ∂(μ.prod μ) < δ := hclose
    linarith
  have hzero : ∫ p, U p.1 p.2 ^ 2 ∂(μ.prod μ) = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add fun δ hδ => ?_) (integral_nonneg fun p => sq_nonneg _)
    simpa using hsmall δ hδ
  have h0 := (integral_eq_zero_iff_of_nonneg (fun p => sq_nonneg _) hint2).mp hzero
  filter_upwards [h0] with p hp
  simpa using hp

/-- **`lem:c-zero`** (the direction used): `c = 0` gives `W = 1/2` almost everywhere. -/
theorem graphon_half_of_graphonC_zero {W : Ω → Ω → ℝ} (hW : IsGraphon W μ)
    (hc : graphonC μ W = 0) :
    (fun p : Ω × Ω => W p.1 p.2) =ᵐ[μ.prod μ] fun _ => (1 / 2 : ℝ) := by
  filter_upwards [signedKernel_ae_zero_of_graphonC hW hc] with p hp
  simp only [signedKernel, Pi.zero_apply] at hp
  linarith

end ApicesCommonness
