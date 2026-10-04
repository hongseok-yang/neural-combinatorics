-- Provenance (plan D7): copied from
--   discussions/schur_decomposition/cycle_commonality/lean/CycleCommonality/Foundation/GraphonL2Operator.lean
--   at neural-combinatorics commit e2d96440.
-- Changes: import paths and the namespace prefix CycleCommonality -> ApicesCommonness; pruned in M11
-- (declarations unused by this development removed).
import ApicesCommonness.Common.Foundation.Kernel
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# L² foundations for graphon kernel operators

This file develops the concrete `L²` objects and kernel operators needed for the graphon
approximation argument.  In particular, bounded measurable kernels act on `Lp ℝ 2 μ`, and the
simple-function density results yield finite-rank kernel approximations.  The development uses
only these concrete operator identities and does not require a compact-operator spectral theorem.
-/

open MeasureTheory
open scoped InnerProductSpace
open scoped ENNReal

-- A few lemmas do not use the section variable `[IsProbabilityMeasure mu]`; keep the declarations uniform.
set_option linter.unusedSectionVars false

noncomputable section

namespace ApicesCommonness.Foundation
namespace Spectral
namespace L2Kernel

universe u

variable {Omega : Type u} [MeasurableSpace Omega] {mu : Measure Omega}
variable [IsProbabilityMeasure mu]
variable {W : Omega -> Omega -> Real}

/-- A bounded measurable kernel sends bounded strongly measurable functions to
bounded strongly measurable functions.

This is the non-graphon version needed for approximation arguments: simple
kernel approximants and kernel differences are generally `GoodK`, not
`IsGraphon`. -/
lemma good_kernelOp_goodK {K : Omega -> Omega -> Real}
    (hK : GoodK K) {f : Omega -> Real} (hf : Good f) :
    Good (kernelOp K mu f) := by
  obtain ⟨CK, hCK0, hCK⟩ := hK.bdd
  obtain ⟨Cf, hCf0, hCf⟩ := hf.bdd
  refine ⟨?_, ⟨CK * Cf, mul_nonneg hCK0 hCf0, fun x => ?_⟩⟩
  · have hSM : StronglyMeasurable
        (fun p : Omega × Omega => K p.1 p.2 * f p.2) :=
      hK.meas.stronglyMeasurable.mul
        (hf.meas.comp_measurable measurable_snd)
    exact hSM.integral_prod_right'
  · have hint : Integrable (fun y => K x y * f y) mu := by
      have hmK : Measurable (fun y => K x y) :=
        hK.meas.comp measurable_prodMk_left
      refine (integrable_const (CK * Cf)).mono'
        (hmK.stronglyMeasurable.mul hf.meas).aestronglyMeasurable
        (ae_of_all _ fun y => ?_)
      change |K x y * f y| <= CK * Cf
      rw [abs_mul]
      exact mul_le_mul (hCK x y) (hCf y) (abs_nonneg _) hCK0
    calc
      |kernelOp K mu f x|
          <= ∫ y, |K x y * f y| ∂mu := abs_integral_le_integral_abs
      _ <= ∫ _y, CK * Cf ∂mu := by
          refine integral_mono hint.abs (integrable_const (CK * Cf)) ?_
          intro y
          change |K x y * f y| <= CK * Cf
          rw [abs_mul]
          exact mul_le_mul (hCK x y) (hCf y) (abs_nonneg _) hCK0
      _ = CK * Cf := by simp

/-- Composing a kernel with the row-broadcast kernel `(z, y) ↦ f z`
is the same as applying the kernel to `f`, pointwise in the first variable. -/
lemma comp_rowBroadcast_eq_kernelOp {K : Omega -> Omega -> Real}
    (f : Omega -> Real) :
    comp mu K (fun z _y => f z) = fun x _y => kernelOp K mu f x := by
  rfl

/-- Pointwise composition law for bounded kernels acting on bounded
representatives: applying `L` and then `K` equals applying the composed
kernel `K ∘ L`.  This is a direct consequence of the already-proved
Fubini associativity of kernel composition. -/
lemma kernelOp_comp_eq_kernelOp_kernelOp {K L : Omega -> Omega -> Real}
    (hK : GoodK K) (hL : GoodK L)
    {f : Omega -> Real} (hf : Good f) :
    kernelOp (comp mu K L) mu f =
      kernelOp K mu (kernelOp L mu f) := by
  have hassoc :=
    comp_assoc (μ := mu) hK hL (goodK_rowBroadcast (Ω := Omega) hf)
  have hleft :
      comp mu (comp mu K L) (fun z _y => f z) =
        fun x _y => kernelOp (comp mu K L) mu f x := by
    exact comp_rowBroadcast_eq_kernelOp (mu := mu) f
  have hright :
      comp mu L (fun z _y => f z) =
        fun x _y => kernelOp L mu f x := by
    exact comp_rowBroadcast_eq_kernelOp (mu := mu) f
  funext x
  have hx := congrFun (congrFun hassoc x) x
  rw [hleft] at hx
  rw [hright] at hx
  simpa [comp, kernelOp] using hx

/-! ### Hilbert-Schmidt estimates for bounded kernels -/

/-- A bounded measurable kernel is an `L²` function on the product space. -/
lemma goodK_memLp_prod_two {K : Omega -> Omega -> Real}
    (hK : GoodK K) :
    MemLp (Function.uncurry K) 2 (mu.prod mu) := by
  obtain ⟨C, _hC0, hC⟩ := hK.bdd
  exact MemLp.of_bound (μ := mu.prod mu) hK.meas.aestronglyMeasurable C
    (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]
      exact hC p.1 p.2)

/-- Real-valued `L²` seminorm as the square root of the square integral. -/
lemma lpNorm_two_eq_sqrt_integral_sq
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f : α -> Real} (hf : AEStronglyMeasurable f ν) :
    lpNorm f 2 ν = Real.sqrt (∫ x, f x * f x ∂ν) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal
    (p := (2 : ENNReal)) (by norm_num) (by simp) hf]
  rw [Real.sqrt_eq_rpow]
  congr 1
  · apply integral_congr_ae
    exact ae_of_all _ fun x => by
      simp [Real.norm_eq_abs, abs_mul_abs_self, sq]
  · norm_num

/-- General `L²` simple-function approximation for bounded measurable
kernels, stated on the product space.

The next graphon-specific step is to replace each simple-function level set
by finite unions of measurable rectangles, using the rectangle semiring
approximation in `Kernel.lean`. -/
lemma exists_simpleFunc_eLpNorm_uncurry_sub_lt_of_goodK
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ S : SimpleFunc (Omega × Omega) Real,
      eLpNorm (Function.uncurry K - ⇑S) 2 (mu.prod mu) < ε ∧
        MemLp S 2 (mu.prod mu) := by
  have htop := ENNReal.ofNat_ne_top (n := 2)
  exact (goodK_memLp_prod_two (mu := mu) hK).exists_simpleFunc_eLpNorm_sub_lt
    htop hε

/-- Real-valued `L²` simple-function approximation for bounded measurable
kernels on the product space. -/
lemma exists_simpleFunc_lpNorm_uncurry_sub_lt_of_goodK
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {δ : Real} (hδ : 0 < δ) :
    ∃ S : SimpleFunc (Omega × Omega) Real,
      lpNorm (Function.uncurry K - ⇑S) 2 (mu.prod mu) < δ ∧
        MemLp S 2 (mu.prod mu) := by
  rcases exists_simpleFunc_eLpNorm_uncurry_sub_lt_of_goodK
      (mu := mu) hK (ε := ENNReal.ofReal δ)
      (ENNReal.ofReal_ne_zero_iff.mpr hδ) with ⟨S, hSlt, hSmem⟩
  refine ⟨S, ?_, hSmem⟩
  have hSM :
      AEStronglyMeasurable (Function.uncurry K - ⇑S) (mu.prod mu) :=
    (goodK_memLp_prod_two (mu := mu) hK).aestronglyMeasurable.sub
      hSmem.aestronglyMeasurable
  rw [← MeasureTheory.toReal_eLpNorm hSM]
  exact ENNReal.toReal_lt_of_lt_ofReal hSlt

end L2Kernel
end Spectral
end ApicesCommonness.Foundation
