import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Graphon representatives

The common analytic object used by every proof method. We deliberately use an
actual symmetric measurable kernel on an arbitrary probability space; there is
no finite-step, regularity, or quotient-by-weak-isomorphism assumption.
-/

open MeasureTheory

namespace Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- A symmetric measurable `[0,1]`-valued kernel on a probability space. -/
structure Graphon (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  toFun : Ω → Ω → ℝ
  measurable : Measurable (Function.uncurry toFun)
  nonneg : ∀ x y, 0 ≤ toFun x y
  le_one : ∀ x y, toFun x y ≤ 1
  symm : ∀ x y, toFun x y = toFun y x

instance : CoeFun (Graphon Ω μ) fun _ ↦ Ω → Ω → ℝ :=
  ⟨Graphon.toFun⟩

end Taeyoung
