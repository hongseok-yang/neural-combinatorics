import OddCycleBound.PathDensity

/-!
# Kernel-composition algebra

To prove the cycle inclusion–exclusion `t(C_m, 1−U) = [polynomial in x_j and c_m]` uniformly,
we work with kernels `K : Ω → Ω → ℝ` under composition `comp K L x y = ∫ z, K x z · L z y`.
The all-ones kernel `onesKernel` is idempotent (`onesKernel ∘ onesKernel = onesKernel`) and rank-one, and the central
**cut lemma** `onesKernel ∘ M ∘ onesKernel = (∫∫ M) · onesKernel` is the arc-factorization mechanism: a `onesKernel`-flanked
run of `U`'s collapses to the scalar path density `∫∫ Uᵒˡ = x_ℓ`.

This file builds the reusable algebra (composition, boundedness/measurability closure,
bilinearity, the cut lemma).  Cyclic traces, the per-cycle expansions (C5/C7/C9), and the
connection to `pathDensity`/`c_m` are built on top.
-/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A bounded, jointly measurable kernel. -/
structure GoodK (K : Ω → Ω → ℝ) : Prop where
  meas : Measurable (Function.uncurry K)
  bdd : ∃ C, 0 ≤ C ∧ ∀ x y, |K x y| ≤ C

/-- Kernel composition `(K ∘ L)(x,y) = ∫ z, K x z · L z y`. -/
noncomputable def comp (μ : Measure Ω) (K L : Ω → Ω → ℝ) : Ω → Ω → ℝ :=
  fun x y => ∫ z, K x z * L z y ∂μ

/-- The all-ones kernel. -/
def onesKernel : Ω → Ω → ℝ := fun _ _ => 1

/-- Double mean `∫∫ M`. -/
noncomputable def doubleMean (μ : Measure Ω) (M : Ω → Ω → ℝ) : ℝ := ∫ x, ∫ y, M x y ∂μ ∂μ

lemma goodK_onesKernel : GoodK (onesKernel (Ω := Ω)) :=
  ⟨measurable_const, ⟨1, zero_le_one, fun _ _ => by simp [onesKernel]⟩⟩

lemma goodK_of_isGraphon {U : Ω → Ω → ℝ} (hU : IsGraphon U μ) : GoodK U :=
  ⟨hU.meas, ⟨1, zero_le_one, fun x y => by
    rw [abs_of_nonneg (hU.nonneg x y)]; exact hU.le_one x y⟩⟩

/-- For `Good`K kernels, the inner integrand `z ↦ K x z · L z y` is integrable. -/
lemma integrable_KL {K L : Ω → Ω → ℝ} (hK : GoodK K) (hL : GoodK L) (x y : Ω) :
    Integrable (fun z => K x z * L z y) μ := by
  obtain ⟨Ck, _, hCk⟩ := hK.bdd
  obtain ⟨Cl, hCl0, hCl⟩ := hL.bdd
  have hmK : Measurable (fun z => K x z) := hK.meas.comp (measurable_prodMk_left)
  have hmL : Measurable (fun z => L z y) := hL.meas.comp (measurable_id.prodMk measurable_const)
  refine (integrable_const (Ck * Cl)).mono' (hmK.mul hmL).aestronglyMeasurable (ae_of_all _ ?_)
  intro z
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hCk x z) (hCl z y) (abs_nonneg _) (le_trans (abs_nonneg _) (hCk x z))

lemma goodK_comp {K L : Ω → Ω → ℝ} (hK : GoodK K) (hL : GoodK L) : GoodK (comp μ K L) := by
  obtain ⟨Ck, hCk0, hCk⟩ := hK.bdd
  obtain ⟨Cl, hCl0, hCl⟩ := hL.bdd
  refine ⟨?_, ⟨Ck * Cl, mul_nonneg hCk0 hCl0, fun x y => ?_⟩⟩
  · -- measurability of `(x,y) ↦ ∫ z, K x z * L z y`
    have hSM : StronglyMeasurable (fun q : (Ω × Ω) × Ω => K q.1.1 q.2 * L q.2 q.1.2) := by
      have h1 : Measurable (fun q : (Ω × Ω) × Ω => K q.1.1 q.2) :=
        hK.meas.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      have h2 : Measurable (fun q : (Ω × Ω) × Ω => L q.2 q.1.2) :=
        hL.meas.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
      exact (h1.mul h2).stronglyMeasurable
    exact (hSM.integral_prod_right').measurable
  · -- the bound
    calc |comp μ K L x y| ≤ ∫ z, |K x z * L z y| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _z, Ck * Cl ∂μ := by
          refine integral_mono (integrable_KL hK hL x y).abs (integrable_const _) (fun z => ?_)
          rw [abs_mul]
          exact mul_le_mul (hCk x z) (hCl z y) (abs_nonneg _) hCk0
      _ = Ck * Cl := by simp

/-! ### Integrability helpers for `GoodK` kernels -/

lemma GoodK.integrable_row {K : Ω → Ω → ℝ} (hK : GoodK K) (x : Ω) :
    Integrable (fun y => K x y) μ := by
  obtain ⟨C, _, hC⟩ := hK.bdd
  have hm : Measurable (fun y => K x y) := hK.meas.comp measurable_prodMk_left
  exact (integrable_const C).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hC x y)

lemma GoodK.integrable_col {K : Ω → Ω → ℝ} (hK : GoodK K) (y : Ω) :
    Integrable (fun x => K x y) μ := by
  obtain ⟨C, _, hC⟩ := hK.bdd
  have hm : Measurable (fun x => K x y) := hK.meas.comp (measurable_id.prodMk measurable_const)
  exact (integrable_const C).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x y)

lemma GoodK.integrable_prod {K : Ω → Ω → ℝ} (hK : GoodK K) :
    Integrable (Function.uncurry K) (μ.prod μ) := by
  obtain ⟨C, _, hC⟩ := hK.bdd
  exact (integrable_const C).mono' hK.meas.aestronglyMeasurable
    (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hC p.1 p.2)

lemma GoodK.colsum_stronglyMeasurable {K : Ω → Ω → ℝ} (hK : GoodK K) :
    StronglyMeasurable (fun y => ∫ x, K x y ∂μ) :=
  (show StronglyMeasurable (Function.uncurry K) from hK.meas.stronglyMeasurable).integral_prod_left

lemma GoodK.colsum_integrable {K : Ω → Ω → ℝ} (hK : GoodK K) :
    Integrable (fun y => ∫ x, K x y ∂μ) μ := by
  obtain ⟨C, _, hC⟩ := hK.bdd
  refine (integrable_const C).mono' hK.colsum_stronglyMeasurable.aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs]
  calc |∫ x, K x y ∂μ| ≤ ∫ x, |K x y| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _x, C ∂μ := integral_mono (hK.integrable_col y).abs (integrable_const C) (fun x => hC x y)
    _ = C := by simp

/-! ### Bilinearity of composition (in each argument) -/

lemma comp_add_left {K₁ K₂ L : Ω → Ω → ℝ} (hK₁ : GoodK K₁) (hK₂ : GoodK K₂) (hL : GoodK L) :
    comp μ (fun x y => K₁ x y + K₂ x y) L = fun x y => comp μ K₁ L x y + comp μ K₂ L x y := by
  funext x y
  simp only [comp]
  rw [← integral_add (integrable_KL hK₁ hL x y) (integrable_KL hK₂ hL x y)]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

lemma comp_add_right {K L₁ L₂ : Ω → Ω → ℝ} (hK : GoodK K) (hL₁ : GoodK L₁) (hL₂ : GoodK L₂) :
    comp μ K (fun x y => L₁ x y + L₂ x y) = fun x y => comp μ K L₁ x y + comp μ K L₂ x y := by
  funext x y
  simp only [comp]
  rw [← integral_add (integrable_KL hK hL₁ x y) (integrable_KL hK hL₂ x y)]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

lemma comp_smul_left (c : ℝ) (K L : Ω → Ω → ℝ) :
    comp μ (fun x y => c * K x y) L = fun x y => c * comp μ K L x y := by
  funext x y
  simp only [comp]
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

lemma comp_smul_right (c : ℝ) (K L : Ω → Ω → ℝ) :
    comp μ K (fun x y => c * L x y) = fun x y => c * comp μ K L x y := by
  funext x y
  simp only [comp]
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

lemma comp_neg_left (K L : Ω → Ω → ℝ) :
    comp μ (fun x y => -K x y) L = fun x y => -comp μ K L x y := by
  funext x y; simp only [comp]; rw [← integral_neg]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

lemma comp_sub_left {K₁ K₂ L : Ω → Ω → ℝ} (hK₁ : GoodK K₁) (hK₂ : GoodK K₂) (hL : GoodK L) :
    comp μ (fun x y => K₁ x y - K₂ x y) L = fun x y => comp μ K₁ L x y - comp μ K₂ L x y := by
  funext x y
  simp only [comp]
  rw [← integral_sub (integrable_KL hK₁ hL x y) (integrable_KL hK₂ hL x y)]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

lemma comp_sub_right {K L₁ L₂ : Ω → Ω → ℝ} (hK : GoodK K) (hL₁ : GoodK L₁) (hL₂ : GoodK L₂) :
    comp μ K (fun x y => L₁ x y - L₂ x y) = fun x y => comp μ K L₁ x y - comp μ K L₂ x y := by
  funext x y
  simp only [comp]
  rw [← integral_sub (integrable_KL hK hL₁ x y) (integrable_KL hK hL₂ x y)]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

/-! ### The cut lemma: `onesKernel ∘ M ∘ onesKernel = (∫∫ M) · onesKernel` -/

/-- Right multiplication by `onesKernel` integrates out the second variable: `(M ∘ onesKernel)(x,y) = ∫ M x ·`. -/
lemma comp_onesKernel_right (M : Ω → Ω → ℝ) :
    comp μ M onesKernel = fun x _ => ∫ z, M x z ∂μ := by
  funext x y; simp [comp, onesKernel]

/-- Left multiplication by `onesKernel` integrates out the first variable. -/
lemma comp_onesKernel_left (M : Ω → Ω → ℝ) :
    comp μ onesKernel M = fun _ y => ∫ z, M z y ∂μ := by
  funext x y; simp [comp, onesKernel]

/-- `onesKernel` is idempotent under composition. -/
lemma comp_onesKernel_onesKernel : comp μ (onesKernel (Ω := Ω)) onesKernel = onesKernel := by
  funext x y; simp [comp, onesKernel]

/-- **The cut lemma.**  `onesKernel ∘ M ∘ onesKernel = (∫∫ M) · onesKernel`: a `onesKernel`-flanked block collapses to its
double mean times `onesKernel`.  This is the arc-factorization mechanism. -/
lemma cut (M : Ω → Ω → ℝ) :
    comp μ onesKernel (comp μ M onesKernel) = fun _ _ => doubleMean μ M := by
  rw [comp_onesKernel_right]
  funext x y
  simp only [comp, onesKernel, one_mul]
  rfl

/-! ### Associativity of composition (Fubini) -/

lemma comp_assoc {K L M : Ω → Ω → ℝ} (hK : GoodK K) (hL : GoodK L) (hM : GoodK M) :
    comp μ (comp μ K L) M = comp μ K (comp μ L M) := by
  funext x y
  obtain ⟨Ck, _, hCk⟩ := hK.bdd
  obtain ⟨Cl, _, hCl⟩ := hL.bdd
  obtain ⟨Cm, _, hCm⟩ := hM.bdd
  have hSM : StronglyMeasurable (Function.uncurry fun w z => K x z * L z w * M w y) := by
    have h1 : Measurable (fun p : Ω × Ω => K x p.2) := hK.meas.comp (measurable_const.prodMk measurable_snd)
    have h2 : Measurable (fun p : Ω × Ω => L p.2 p.1) := hL.meas.comp (measurable_snd.prodMk measurable_fst)
    have h3 : Measurable (fun p : Ω × Ω => M p.1 y) := hM.meas.comp (measurable_fst.prodMk measurable_const)
    exact ((h1.mul h2).mul h3).stronglyMeasurable
  have hInt : Integrable (Function.uncurry fun w z => K x z * L z w * M w y) (μ.prod μ) := by
    refine (integrable_const (Ck * Cl * Cm)).mono' hSM.aestronglyMeasurable (ae_of_all _ ?_)
    rintro ⟨w, z⟩
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (mul_le_mul (hCk x z) (hCl z w) (abs_nonneg _) (le_trans (abs_nonneg _) (hCk x z)))
      (hCm w y) (abs_nonneg _)
      (mul_nonneg (le_trans (abs_nonneg _) (hCk x z)) (le_trans (abs_nonneg _) (hCl z w)))
  have hL1 : ∀ w, comp μ K L x w * M w y = ∫ z, K x z * L z w * M w y ∂μ := by
    intro w; simp only [comp]; rw [← integral_mul_const]
  have hR1 : ∀ z, K x z * comp μ L M z y = ∫ w, K x z * L z w * M w y ∂μ := by
    intro z; simp only [comp]; rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun w => by ring)
  calc comp μ (comp μ K L) M x y
      = ∫ w, comp μ K L x w * M w y ∂μ := rfl
    _ = ∫ w, ∫ z, K x z * L z w * M w y ∂μ ∂μ := integral_congr_ae (ae_of_all _ hL1)
    _ = ∫ z, ∫ w, K x z * L z w * M w y ∂μ ∂μ := integral_integral_swap hInt
    _ = ∫ z, K x z * comp μ L M z y ∂μ := (integral_congr_ae (ae_of_all _ hR1)).symm
    _ = comp μ K (comp μ L M) x y := rfl

/-! ### Kernel powers and the cyclic trace -/

/-- `compPow K n` is the `(n+1)`-fold composition `K ∘ K ∘ ⋯ ∘ K` (so `compPow K 0 = K`). -/
noncomputable def compPow (μ : Measure Ω) (K : Ω → Ω → ℝ) : ℕ → (Ω → Ω → ℝ)
  | 0 => K
  | (n + 1) => comp μ K (compPow μ K n)

lemma goodK_compPow {K : Ω → Ω → ℝ} (hK : GoodK K) : ∀ n, GoodK (compPow μ K n)
  | 0 => hK
  | (n + 1) => goodK_comp hK (goodK_compPow hK n)

lemma compPow_onesKernel : ∀ n, compPow μ (onesKernel (Ω := Ω)) n = onesKernel
  | 0 => rfl
  | (n + 1) => by rw [compPow, compPow_onesKernel n, comp_onesKernel_onesKernel]

/-- The trace `trace K = ∫ x, K x x`.  The cycle density is `t(C_m, K) = trace (compPow K (m−1))`. -/
noncomputable def trace (μ : Measure Ω) (K : Ω → Ω → ℝ) : ℝ := ∫ x, K x x ∂μ

lemma trace_onesKernel : trace μ (onesKernel (Ω := Ω)) = 1 := by simp [trace, onesKernel]

/-- **Trace cyclic-invariance** (the necklace-rotation primitive): `trace (A ∘ B) = trace (B ∘ A)`. -/
lemma trace_comp_comm {A B : Ω → Ω → ℝ} (hA : GoodK A) (hB : GoodK B) :
    trace μ (comp μ A B) = trace μ (comp μ B A) := by
  obtain ⟨Ca, _, hCa⟩ := hA.bdd
  obtain ⟨Cb, _, hCb⟩ := hB.bdd
  have hint : Integrable (Function.uncurry fun x z => A x z * B z x) (μ.prod μ) := by
    have hm : Measurable (Function.uncurry fun x z => A x z * B z x) :=
      (hA.meas.comp (measurable_fst.prodMk measurable_snd)).mul
        (hB.meas.comp (measurable_snd.prodMk measurable_fst))
    refine (integrable_const (Ca * Cb)).mono' hm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hCa p.1 p.2) (hCb p.2 p.1) (abs_nonneg _) (le_trans (abs_nonneg _) (hCa p.1 p.2))
  have h1 : trace μ (comp μ A B) = ∫ x, ∫ z, A x z * B z x ∂μ ∂μ := rfl
  have h2 : trace μ (comp μ B A) = ∫ x, ∫ z, B x z * A z x ∂μ ∂μ := rfl
  rw [h1, h2, integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun x => integral_congr_ae (ae_of_all _ fun z => ?_))
  ring

/-- `trace (onesKernel ∘ M) = ∫∫ M`. -/
lemma trace_comp_onesKernel {M : Ω → Ω → ℝ} (hM : GoodK M) : trace μ (comp μ onesKernel M) = doubleMean μ M := by
  have hint : Integrable (Function.uncurry fun x z => M z x) (μ.prod μ) := by
    obtain ⟨C, _, hC⟩ := hM.bdd
    have hm : Measurable (Function.uncurry fun x z => M z x) :=
      hM.meas.comp (measurable_snd.prodMk measurable_fst)
    exact (integrable_const C).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hC p.2 p.1)
  show ∫ x, comp μ onesKernel M x x ∂μ = doubleMean μ M
  simp only [comp, onesKernel, one_mul]
  rw [integral_integral_swap hint]; rfl

/-- `trace (M ∘ onesKernel) = ∫∫ M`. -/
lemma trace_comp_onesKernel_right {M : Ω → Ω → ℝ} : trace μ (comp μ M onesKernel) = doubleMean μ M := by
  show ∫ x, comp μ M onesKernel x x ∂μ = doubleMean μ M
  simp only [comp, onesKernel, mul_one]; rfl

/-- The diagonal of a `GoodK` kernel is integrable. -/
lemma GoodK.diag_integrable {K : Ω → Ω → ℝ} (hK : GoodK K) :
    Integrable (fun x => K x x) μ := by
  obtain ⟨C, _, hC⟩ := hK.bdd
  have hm : Measurable (fun x => K x x) := hK.meas.comp (measurable_id.prodMk measurable_id)
  exact (integrable_const C).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x x)

/-- Additivity of the trace over a pointwise difference of `GoodK` kernels. -/
lemma trace_sub {A B : Ω → Ω → ℝ} (hA : GoodK A) (hB : GoodK B) :
    trace μ (fun x y => A x y - B x y) = trace μ A - trace μ B := by
  show ∫ x, (A x x - B x x) ∂μ = (∫ x, A x x ∂μ) - ∫ x, B x x ∂μ
  exact integral_sub hA.diag_integrable hB.diag_integrable

/-- The row-broadcast `(x,y) ↦ f x` of a `Good` function is a `GoodK` kernel. -/
lemma goodK_rowBroadcast {f : Ω → ℝ} (hf : Good f) : GoodK (fun _x _y => f _x) := by
  obtain ⟨C, hC0, hC⟩ := hf.bdd
  exact ⟨hf.meas.measurable.comp measurable_fst, ⟨C, hC0, fun x _ => hC x⟩⟩

end OddCycleBound
