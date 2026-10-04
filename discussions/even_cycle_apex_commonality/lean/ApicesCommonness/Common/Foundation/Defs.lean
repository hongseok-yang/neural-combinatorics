-- Provenance (plan D7): copied from
--   discussions/schur_decomposition/cycle_commonality/lean/CycleCommonality/Defs.lean
--   at neural-combinatorics commit e2d96440.
-- Changes: import paths and the namespace prefix CycleCommonality -> ApicesCommonness; pruned in M11
-- (declarations unused by this development removed, module docstring updated to match).
import ApicesCommonness.Common.Foundation.Kernel

/-!
# The complement and the cycle density of a kernel

`cmpl W = 1 − W` (`isGraphon_cmpl`: the complement of a graphon is a graphon), and
`cycleDensity W μ r = t(C_r, W)` in the form of a trace of a kernel power.  `Fubini.lean` proves
it is the integral

```
  t(C_r, W) = ∫_{Ω^r} ∏_{i<r} W(x_i, x_{i+1}) dμ^{⊗r}        (indices cyclic).
```

The public statements use `homDensity` (`Graph/HomDensity.lean`); `cycleDensity` is used only
inside the transfer and equality arguments, where the two are identified.
-/

open MeasureTheory ApicesCommonness.Foundation

set_option linter.unusedSectionVars false

namespace ApicesCommonness

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The complementary graphon `1 − W`. -/
def cmpl (W : Ω → Ω → ℝ) : Ω → Ω → ℝ := fun x y => 1 - W x y

/-- `t(C_r, W)`: the cycle density of a kernel. -/
noncomputable def cycleDensity (W : Ω → Ω → ℝ) (μ : Measure Ω) (r : ℕ) : ℝ :=
  trace μ (compPow μ W (r - 1))

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Ω → Ω → ℝ}

/-- The complement of a graphon is a graphon. -/
lemma isGraphon_cmpl (hW : IsGraphon W μ) : IsGraphon (cmpl W) μ where
  meas := measurable_const.sub hW.meas
  nonneg := fun x y => by have := hW.le_one x y; show 0 ≤ 1 - W x y; linarith
  le_one := fun x y => by have := hW.nonneg x y; show 1 - W x y ≤ 1; linarith
  symm := fun x y => by show 1 - W x y = 1 - W y x; rw [hW.symm x y]

end ApicesCommonness
