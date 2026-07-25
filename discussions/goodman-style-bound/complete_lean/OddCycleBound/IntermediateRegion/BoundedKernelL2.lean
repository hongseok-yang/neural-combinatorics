import OddCycleBound.IntermediateRegion.CenteredKernel

/-!
# Pointwise `L²` realization for signed bounded symmetric kernels

The low-band operator library proves the arbitrary-`L²` pointwise formula
for graphons.  the intermediate region needs the same statement for the signed centered
kernel.  This file supplies the bounded-kernel version, retaining the
existing `GoodK` interface and an explicit uniform bound.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.Spectral.L2Kernel

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]

section Pointwise

variable {K : Omega → Omega → Real}

lemma integrable_kernelOp_goodK_l2
    (hK : GoodK K) {C : Real} (hC0 : 0 ≤ C)
    (hKC : ∀ x y, |K x y| ≤ C)
    (f : Lp Real 2 mu) (x : Omega) :
    Integrable (fun y => K x y * f y) mu := by
  have hf_int : Integrable (fun y : Omega => f y) mu :=
    (Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hrow_meas : StronglyMeasurable (fun y : Omega => K x y) :=
    (hK.meas.comp measurable_prodMk_left).stronglyMeasurable
  refine (hf_int.norm.const_mul C).mono'
    (hrow_meas.mul (Lp.stronglyMeasurable f)).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  simp only [Real.norm_eq_abs]
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hKC x y) (abs_nonneg (f y))

/-- A uniformly bounded measurable kernel sends an arbitrary `L²` vector to
a bounded strongly measurable pointwise representative. -/
lemma good_kernelOp_goodK_l2
    (hK : GoodK K) {C : Real} (hC0 : 0 ≤ C)
    (hKC : ∀ x y, |K x y| ≤ C)
    (f : Lp Real 2 mu) :
    Good (kernelOp K mu (fun y : Omega => f y)) := by
  let B : Real := C * ∫ y, |f y| ∂mu
  have hf_int : Integrable (fun y : Omega => f y) mu :=
    (Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hprod_sm : StronglyMeasurable
      (fun p : Omega × Omega => K p.1 p.2 * f p.2) :=
    hK.meas.stronglyMeasurable.mul
      ((Lp.stronglyMeasurable f).comp_measurable measurable_snd)
  refine ⟨hprod_sm.integral_prod_right', B, ?_, fun x => ?_⟩
  · exact mul_nonneg hC0 (integral_nonneg fun y => abs_nonneg (f y))
  · have hint := integrable_kernelOp_goodK_l2
      (mu := mu) hK hC0 hKC f x
    have hdom : Integrable (fun y : Omega => C * |f y|) mu :=
      hf_int.norm.const_mul C
    calc
      |kernelOp K mu (fun y : Omega => f y) x|
          ≤ ∫ y, |K x y * f y| ∂mu := by
            simpa [kernelOp] using
              (abs_integral_le_integral_abs
                (μ := mu) (f := fun y : Omega => K x y * f y))
      _ ≤ ∫ y, C * |f y| ∂mu := by
            exact integral_mono hint.abs hdom (fun y => by
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_right (hKC x y) (abs_nonneg (f y)))
      _ = B := by rw [integral_const_mul]

/-- The pointwise integral transform of an arbitrary `L²` input. -/
noncomputable def kernelOpGoodKL2OfL2
    (hK : GoodK K) {C : Real} (hC0 : 0 ≤ C)
    (hKC : ∀ x y, |K x y| ≤ C)
    (f : Lp Real 2 mu) : Lp Real 2 mu :=
  goodL2 (mu := mu) (good_kernelOp_goodK_l2 (mu := mu) hK hC0 hKC f)

/-- On a bounded representative, the arbitrary-`L²` transform agrees with
the original bounded-kernel transform. -/
lemma kernelOpGoodKL2OfL2_goodL2
    (hK : GoodK K) {C : Real} (hC0 : 0 ≤ C)
    (hKC : ∀ x y, |K x y| ≤ C)
    {f : Omega → Real} (hf : Good f) :
    kernelOpGoodKL2OfL2 (mu := mu) hK hC0 hKC
        (goodL2 (mu := mu) hf) =
      kernelOpL2OfGoodK (mu := mu) hK hf := by
  exact MemLp.toLp_congr
    (good_memLp_two
      (good_kernelOp_goodK_l2 (mu := mu) hK hC0 hKC
        (goodL2 (mu := mu) hf)))
    (kernelOpGoodK_memLp_two (mu := mu) hK hf)
    (ae_of_all _ fun x =>
      congrFun
        (kernelOpGoodK_congr_ae (mu := mu) (K := K)
          (goodL2_ae_eq (mu := mu) hf)) x)

lemma inner_goodL2_kernelOpGoodKL2OfL2_eq_integral
    (hK : GoodK K) {C : Real} (hC0 : 0 ≤ C)
    (hKC : ∀ x y, |K x y| ≤ C)
    (f : Lp Real 2 mu) {g : Omega → Real} (hg : Good g) :
    inner Real (goodL2 (mu := mu) hg)
        (kernelOpGoodKL2OfL2 (mu := mu) hK hC0 hKC f) =
      ∫ x, g x * kernelOp K mu (fun y : Omega => f y) x ∂mu := by
  simpa [kernelOpGoodKL2OfL2] using
    inner_goodL2_eq_integral_mul (mu := mu) hg
      (good_kernelOp_goodK_l2 (mu := mu) hK hC0 hKC f)

lemma inner_kernelOpL2OfGoodK_l2_eq_integral
    (hK : GoodK K) {g : Omega → Real} (hg : Good g)
    (f : Lp Real 2 mu) :
    inner Real (kernelOpL2OfGoodK (mu := mu) hK hg) f =
      ∫ x, kernelOp K mu g x * f x ∂mu := by
  rw [MeasureTheory.L2.inner_def]
  have hkg := kernelOpL2OfGoodK_ae_eq (mu := mu) hK hg
  refine integral_congr_ae ?_
  filter_upwards [hkg] with x hx
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]

/-- Fubini symmetry for a bounded symmetric kernel, with one arbitrary `L²`
input and one bounded test function. -/
lemma kernelOp_goodK_symm_l2_good
    (hK : GoodK K) {C : Real} (hC0 : 0 ≤ C)
    (hKC : ∀ x y, |K x y| ≤ C)
    (hsymm : ∀ x y, K x y = K y x)
    (f : Lp Real 2 mu) {g : Omega → Real} (hg : Good g) :
    (∫ x, kernelOp K mu (fun y : Omega => f y) x * g x ∂mu) =
      ∫ y, f y * kernelOp K mu g y ∂mu := by
  obtain ⟨Cg, hCg0, hCg⟩ := hg.bdd
  have hf_int : Integrable (fun y : Omega => f y) mu :=
    (Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hSM : StronglyMeasurable
      (Function.uncurry (fun x y : Omega => K x y * f y * g x)) := by
    have h1 : StronglyMeasurable
        (fun p : Omega × Omega => K p.1 p.2) := hK.meas.stronglyMeasurable
    have h2 : StronglyMeasurable (fun p : Omega × Omega => f p.2) :=
      (Lp.stronglyMeasurable f).comp_measurable measurable_snd
    have h3 : StronglyMeasurable (fun p : Omega × Omega => g p.1) :=
      hg.meas.comp_measurable measurable_fst
    exact (h1.mul h2).mul h3
  have hInt : Integrable
      (Function.uncurry (fun x y : Omega => K x y * f y * g x))
      (mu.prod mu) := by
    have hbound : Integrable
        (fun p : Omega × Omega => (C * Cg) * |f p.2|) (mu.prod mu) :=
      (hf_int.norm.const_mul (C * Cg)).comp_snd mu
    refine hbound.mono' hSM.aestronglyMeasurable (ae_of_all _ ?_)
    rintro ⟨x, y⟩
    simp only [Function.uncurry, Real.norm_eq_abs]
    rw [abs_mul, abs_mul]
    calc
      |K x y| * |f y| * |g x| ≤ (C * |f y|) * |g x| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hKC x y) (abs_nonneg (f y)))
          (abs_nonneg (g x))
      _ ≤ (C * |f y|) * Cg :=
        mul_le_mul_of_nonneg_left (hCg x)
          (mul_nonneg hC0 (abs_nonneg (f y)))
      _ = (C * Cg) * |f y| := by ring
  have hL : ∀ x,
      kernelOp K mu (fun y : Omega => f y) x * g x =
        ∫ y, K x y * f y * g x ∂mu := fun x => by
    rw [kernelOp, integral_mul_const]
  have hR : ∀ y,
      f y * kernelOp K mu g y =
        ∫ x, K x y * f y * g x ∂mu := fun y => by
    rw [kernelOp, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    change f y * (K y x * g x) = K x y * f y * g x
    rw [hsymm y x]
    ring
  calc
    (∫ x, kernelOp K mu (fun y : Omega => f y) x * g x ∂mu) =
        ∫ x, ∫ y, K x y * f y * g x ∂mu ∂mu := by simp_rw [hL]
    _ = ∫ y, ∫ x, K x y * f y * g x ∂mu ∂mu := integral_integral_swap hInt
    _ = ∫ y, f y * kernelOp K mu g y ∂mu := by simp_rw [hR]

lemma kernelOpGoodKL2OfL2_goodL2_selfadj
    (hK : GoodK K) {C : Real} (hC0 : 0 ≤ C)
    (hKC : ∀ x y, |K x y| ≤ C)
    (hsymm : ∀ x y, K x y = K y x)
    (f : Lp Real 2 mu) {g : Omega → Real} (hg : Good g) :
    inner Real (goodL2 (mu := mu) hg)
        (kernelOpGoodKL2OfL2 (mu := mu) hK hC0 hKC f) =
      inner Real (kernelOpL2OfGoodK (mu := mu) hK hg) f := by
  rw [inner_goodL2_kernelOpGoodKL2OfL2_eq_integral
    (mu := mu) hK hC0 hKC f hg]
  rw [inner_kernelOpL2OfGoodK_l2_eq_integral (mu := mu) hK hg f]
  calc
    (∫ x, g x * kernelOp K mu (fun y : Omega => f y) x ∂mu) =
        ∫ x, kernelOp K mu (fun y : Omega => f y) x * g x ∂mu := by
      refine integral_congr_ae (ae_of_all _ fun x => by ring)
    _ = ∫ y, f y * kernelOp K mu g y ∂mu :=
      kernelOp_goodK_symm_l2_good (mu := mu) hK hC0 hKC hsymm f hg
    _ = ∫ x, kernelOp K mu g x * f x ∂mu := by
      refine integral_congr_ae (ae_of_all _ fun x => by ring)

/-- The completed bounded-kernel operator is self-adjoint when its kernel is
pointwise symmetric. -/
lemma kernelOpGoodKCLM_isSymmetric
    (hK : GoodK K) {C : Real} (hC0 : 0 ≤ C)
    (hKC : ∀ x y, |K x y| ≤ C)
    (hsymm : ∀ x y, K x y = K y x) :
    (kernelOpGoodKCLM (mu := mu) hK hC0 hKC :
      Lp Real 2 mu →ₗ[Real] Lp Real 2 mu).IsSymmetric := by
  intro f g
  let e : Lp.simpleFunc Real 2 mu → Lp Real 2 mu :=
    fun s => (s : Lp Real 2 mu)
  have hdense : DenseRange e :=
    Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
      (by norm_num)
  refine hdense.induction_on₂
    (p := fun f g =>
      inner Real (kernelOpGoodKCLM (mu := mu) hK hC0 hKC f) g =
        inner Real f (kernelOpGoodKCLM (mu := mu) hK hC0 hKC g))
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_ f g
  intro s t
  dsimp [e]
  rw [kernelOpGoodKCLM_simpleFunc (mu := mu) hK hC0 hKC s,
    kernelOpGoodKCLM_simpleFunc (mu := mu) hK hC0 hKC t]
  have h := kernelOpGoodKL2OfL2_goodL2_selfadj
    (mu := mu) hK hC0 hKC hsymm
    (goodL2 (mu := mu) (simpleFunc_good (mu := mu) s))
    (simpleFunc_good (mu := mu) t)
  rw [kernelOpGoodKL2OfL2_goodL2 (mu := mu) hK hC0 hKC
    (simpleFunc_good (mu := mu) s)] at h
  simpa [kernelOpGoodKSimple, goodL2_simpleFunc_eq_coe (mu := mu),
    real_inner_comm] using h

/-- The completed operator agrees with the concrete pointwise transform on
every `L²` vector. -/
lemma kernelOpGoodKCLM_eq_kernelOpGoodKL2OfL2_apply
    (hK : GoodK K) {C : Real} (hC0 : 0 ≤ C)
    (hKC : ∀ x y, |K x y| ≤ C)
    (hsymm : ∀ x y, K x y = K y x)
    (f : Lp Real 2 mu) :
    kernelOpGoodKCLM (mu := mu) hK hC0 hKC f =
      kernelOpGoodKL2OfL2 (mu := mu) hK hC0 hKC f := by
  let z : Lp Real 2 mu :=
    kernelOpGoodKCLM (mu := mu) hK hC0 hKC f -
      kernelOpGoodKL2OfL2 (mu := mu) hK hC0 hKC f
  have hT := kernelOpGoodKCLM_isSymmetric
    (mu := mu) hK hC0 hKC hsymm
  have hinner_good : ∀ a : {g : Omega → Real // Good g},
      inner Real (goodL2 (mu := mu) a.property) z = 0 := by
    intro a
    rcases a with ⟨g, hg⟩
    have hclm :
        inner Real (goodL2 (mu := mu) hg)
            (kernelOpGoodKCLM (mu := mu) hK hC0 hKC f) =
          inner Real (kernelOpL2OfGoodK (mu := mu) hK hg) f := by
      calc
        _ = inner Real
            (kernelOpGoodKCLM (mu := mu) hK hC0 hKC
              (goodL2 (mu := mu) hg)) f := (hT.apply_clm _ _).symm
        _ = _ := by
          rw [kernelOpGoodKCLM_goodL2 (mu := mu) hK hC0 hKC hg]
    have hpoint := kernelOpGoodKL2OfL2_goodL2_selfadj
      (mu := mu) hK hC0 hKC hsymm f hg
    dsimp [z]
    rw [inner_sub_right, hclm, hpoint, sub_self]
  have hall : ∀ v : Lp Real 2 mu, inner Real v z = 0 := by
    intro v
    apply DenseRange.induction_on
      (p := fun v : Lp Real 2 mu => inner Real v z = 0)
      (denseRange_goodL2 (Omega := Omega) (mu := mu)) v
    · exact isClosed_eq (by fun_prop) continuous_const
    · exact hinner_good
  have hzz : inner Real z z = 0 := hall z
  have hz : z = 0 := by
    apply norm_eq_zero.mp
    have : ‖z‖ ^ 2 = 0 := by
      simpa [real_inner_self_eq_norm_sq] using hzz
    nlinarith [norm_nonneg z]
  exact sub_eq_zero.mp hz

/-- Finite row-coordinate square sums for arbitrary `L²` modes are
integrable for every uniformly bounded measurable kernel. -/
lemma integrable_sum_goodK_row_inner_l2_sq
    (hK : GoodK K) {C : Real} (hC0 : 0 ≤ C)
    (hKC : ∀ x y, |K x y| ≤ C)
    {ι : Type*} [DecidableEq ι]
    (mode : ι → Lp Real 2 mu) (s : Finset ι) :
    Integrable (fun x : Omega =>
      s.sum (fun i =>
        inner Real (goodL2 (mu := mu) (goodK_row hK x)) (mode i) ^ 2)) mu := by
  refine integrable_finset_sum s ?_
  intro i hi
  have hgood : Good (fun x : Omega =>
      kernelOp K mu (fun y : Omega => mode i y) x *
        kernelOp K mu (fun y : Omega => mode i y) x) :=
    (good_kernelOp_goodK_l2 (mu := mu) hK hC0 hKC (mode i)).mul
      (good_kernelOp_goodK_l2 (mu := mu) hK hC0 hKC (mode i))
  refine hgood.integrable.congr (ae_of_all _ fun x => ?_)
  change
    kernelOp K mu (fun y : Omega => mode i y) x *
        kernelOp K mu (fun y : Omega => mode i y) x =
      inner Real (goodL2 (mu := mu) (goodK_row hK x)) (mode i) ^ 2
  rw [inner_goodK_row_l2_eq_kernelOp (mu := mu) hK (mode i) x]
  ring

/-- Finite Hilbert--Schmidt row-energy identity for arbitrary `L²` modes. -/
lemma sum_norm_kernelOpGoodKCLM_sq_eq_integral_sum_row_inner_l2_sq
    (hK : GoodK K) {C : Real} (hC0 : 0 ≤ C)
    (hKC : ∀ x y, |K x y| ≤ C)
    (hsymm : ∀ x y, K x y = K y x)
    {ι : Type*} [DecidableEq ι]
    (mode : ι → Lp Real 2 mu) (s : Finset ι) :
    s.sum (fun i => ‖kernelOpGoodKCLM (mu := mu) hK hC0 hKC (mode i)‖ ^ 2) =
      ∫ x, s.sum (fun i =>
        inner Real (goodL2 (mu := mu) (goodK_row hK x)) (mode i) ^ 2) ∂mu := by
  have hterm_integrable : ∀ i ∈ s, Integrable (fun x : Omega =>
      inner Real (goodL2 (mu := mu) (goodK_row hK x)) (mode i) ^ 2) mu := by
    intro i hi
    have hgood : Good (fun x : Omega =>
        kernelOp K mu (fun y : Omega => mode i y) x *
          kernelOp K mu (fun y : Omega => mode i y) x) :=
      (good_kernelOp_goodK_l2 (mu := mu) hK hC0 hKC (mode i)).mul
        (good_kernelOp_goodK_l2 (mu := mu) hK hC0 hKC (mode i))
    refine hgood.integrable.congr (ae_of_all _ fun x => ?_)
    change
      kernelOp K mu (fun y : Omega => mode i y) x *
          kernelOp K mu (fun y : Omega => mode i y) x =
        inner Real (goodL2 (mu := mu) (goodK_row hK x)) (mode i) ^ 2
    rw [inner_goodK_row_l2_eq_kernelOp (mu := mu) hK (mode i) x]
    ring
  rw [integral_finset_sum s hterm_integrable]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [kernelOpGoodKCLM_eq_kernelOpGoodKL2OfL2_apply
    (mu := mu) hK hC0 hKC hsymm (mode i)]
  calc
    ‖kernelOpGoodKL2OfL2 (mu := mu) hK hC0 hKC (mode i)‖ ^ 2 =
        ∫ x, kernelOp K mu (fun y : Omega => mode i y) x *
          kernelOp K mu (fun y : Omega => mode i y) x ∂mu := by
      rw [kernelOpGoodKL2OfL2,
        norm_goodL2_sq_eq_integral_mul (mu := mu)]
    _ = ∫ x,
        inner Real (goodL2 (mu := mu) (goodK_row hK x)) (mode i) ^ 2 ∂mu := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      change
        kernelOp K mu (fun y : Omega => mode i y) x *
            kernelOp K mu (fun y : Omega => mode i y) x =
          inner Real (goodL2 (mu := mu) (goodK_row hK x)) (mode i) ^ 2
      rw [inner_goodK_row_l2_eq_kernelOp (mu := mu) hK (mode i) x]
      ring

end Pointwise

end OddCycleBound.IntermediateRegion
