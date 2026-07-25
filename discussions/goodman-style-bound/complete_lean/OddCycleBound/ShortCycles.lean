import OddCycleBound.BoundsC5C7
import OddCycleBound.BasicBounds

/-!
# `W`-facing short-cycle bounds (`m = 3, 5, 7`)

The integral bounds `C3_integral`, `C5_integral`, `C7_integral_all` (`BoundsC5C7.lean`) prove the
odd-cycle Goodman bound for the **complement** kernel `1 − U`:
`t(C_m, 1−U) ≥ (1−q)^m − (1−q)q^{m−1}` with `q = edgeDensity U μ`.  Instantiating them at `U = 1 − W`
and using `compl_compl`/`edgeDensity_compl` turns each into the headline shape for the original
graphon `W` with edge density `p = edgeDensity W μ`:

  `cycleDensity μ W m ≥ p^m − p(1−p)^{m−1}`   (`m = 3, 5, 7`, paper §2).

These are the three short-cycle inputs that `Main.small_cycle_bound` dispatches to; the `m = 9`
case is assembled directly in `Main.lean` (it splits on `p` and reuses the dense-region bound).
-/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Ω → Ω → ℝ}

/-- **Triangle bound (`m = 3`)** for the original graphon `W`: `t(C₃, W) ≥ p³ − p(1−p)²`.
Obtained from `C3_integral` at `U = 1 − W`.  `cycleDensity μ W 3` unfolds to `trace μ (compPow μ W 2)`
definitionally, matching the wired `C3_integral` after the `compl_compl` rewrite. -/
theorem cycleDensity_three_bound (hW : IsGraphon W μ) :
    cycleDensity μ W 3 ≥ edgeDensity W μ ^ 3 - edgeDensity W μ * (1 - edgeDensity W μ) ^ 2 := by
  have h := C3_integral (isGraphon_compl hW)
  rw [compl_compl, edgeDensity_compl hW,
    show (1:ℝ) - (1 - edgeDensity W μ) = edgeDensity W μ from by ring] at h
  exact h

/-- **`C₅` bound (`m = 5`)** for the original graphon `W`: `t(C₅, W) ≥ p⁵ − p(1−p)⁴`. -/
theorem cycleDensity_five_bound (hW : IsGraphon W μ) :
    cycleDensity μ W 5 ≥ edgeDensity W μ ^ 5 - edgeDensity W μ * (1 - edgeDensity W μ) ^ 4 := by
  have h := C5_integral (isGraphon_compl hW)
  rw [compl_compl, edgeDensity_compl hW,
    show (1:ℝ) - (1 - edgeDensity W μ) = edgeDensity W μ from by ring] at h
  exact h

/-- **`C₇` bound (`m = 7`)** for the original graphon `W`: `t(C₇, W) ≥ p⁷ − p(1−p)⁶`. -/
theorem cycleDensity_seven_bound (hW : IsGraphon W μ) :
    cycleDensity μ W 7 ≥ edgeDensity W μ ^ 7 - edgeDensity W μ * (1 - edgeDensity W μ) ^ 6 := by
  have h := C7_integral_all (isGraphon_compl hW)
  rw [compl_compl, edgeDensity_compl hW,
    show (1:ℝ) - (1 - edgeDensity W μ) = edgeDensity W μ from by ring] at h
  exact h

end OddCycleBound
