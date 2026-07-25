/-
# Dense region (Phase D) — the unconditional endgame (paper §4, `thm:dense-region`)

This capstone discharges the single analytic hypothesis threaded through the beta/gamma route.
`GammaSmoothing.lean` and `Positivity.lean` keep the gamma moment inequality abstract (`hmoment`,
`DiagKernelPosEll`) so that they are self-contained; `GammaMomentProof.lean` proves that inequality
outright (`gamma_moment_inequality`, the hard analytic content D6, ending in `H(b_*) > 0` via
`L(t) < 0`).  Here the two meet: the abstract hypothesis is supplied by the proven inequality, so
`DiagKernelPosEll` and the dense-region odd-cycle bound hold unconditionally.
-/
import OddCycleBound.DenseRegion.Diagonal.GammaMomentProof
import OddCycleBound.DenseRegion.Diagonal.GammaSmoothing
import OddCycleBound.DenseRegion.Diagonal.Positivity

open MeasureTheory

namespace OddCycleBound.DenseRegion

/-- **The `ℓ>0` diagonal-kernel positivity, unconditionally.**  The gamma moment inequality (D6) is
now proven (`gamma_moment_inequality`), so the abstract input `DiagKernelPosEll` of the beta/gamma
route holds outright. -/
theorem diagKernelPosEll_unconditional : DiagKernelPosEll :=
  diagKernel_nonneg_pos_ell gamma_moment_inequality

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Ω → Ω → ℝ}

/-- **Dense-region odd-cycle bound** (`thm:dense-region`), unconditionally.  For every graphon `W`
with `edgeDensity ≥ 2/3` and every odd `m ≥ 3`,
`edgeDensity^m − edgeDensity·(1−edgeDensity)^{m-1} ≤ cycleDensity μ W m`. -/
theorem dense_region_cycle_bound_unconditional
    {m : ℕ} (hW : IsGraphon W μ) (hp : 2 / 3 ≤ edgeDensity W μ) (hm : Odd m) (hm3 : 3 ≤ m) :
    edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) ≤
      cycleDensity μ W m :=
  dense_region_cycle_bound diagKernelPosEll_unconditional hW hp hm hm3

end OddCycleBound.DenseRegion
