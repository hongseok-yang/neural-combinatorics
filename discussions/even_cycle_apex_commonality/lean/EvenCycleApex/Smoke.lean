import EvenCycleApex.Foundation.FiniteBridge
import EvenCycleApex.Foundation.Spectral.EigenSystem

/-!
# M0 smoke test

One statement exercising the three pieces of the copied foundation that the plan relies on most:
`IsGraphon` (plan D1), the `L¹` step approximation `exists_stepGraphon_l1_close` (plan D3), and
the eigenvalue trace formula `EigenSystem.trace_pow_eq_sum` for the Euclidean model of a weighted
finite host (plan D2).  It carries no mathematics of its own; it only shows the copied modules are
usable from this package.
-/

open MeasureTheory

namespace EvenCycleApex

/-- Every graphon has step-graphon approximants, and on the step model the trace of `Tⁿ` is the
sum of the `n`-th powers of the eigenvalues. -/
theorem foundation_smoke {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W : Ω → Ω → ℝ} (hW : Foundation.IsGraphon W μ) :
    (∀ ε > 0, ∃ V : Ω → Ω → ℝ, Foundation.IsGraphon V μ ∧ IsStepKernel V ∧
        l1norm μ (fun x y => W x y - V x y) < ε) ∧
      ∀ {N : ℕ} (G : StepGraphon N) (hN : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N)
        (n : ℕ),
        Matrix.trace (G.mat ^ n) =
          ∑ i, ((EigenSystem.ofSymmetric G.op_isSymmetric hN).val i) ^ n := by
  refine ⟨fun ε hε => exists_stepGraphon_l1_close hW hε, fun G hN n => ?_⟩
  rw [← G.trace_op_pow n]
  exact (EigenSystem.ofSymmetric G.op_isSymmetric hN).trace_pow_eq_sum n

end EvenCycleApex
