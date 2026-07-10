/-
# High-density theorem — the reflection inequality (M5/M6 shared machinery, part D core)

The reflection step of `thm:r1` and `thm:strip` pairs a point `s` in the negative window with its
reflection `ŝ = 2sₐ − s` in a positive partner band.  Because `q + ŝ = 1 − (q+s)`, the `ρ`-values
satisfy `ρ(q+s) + ρ(q+ŝ) ≥ 0` (`rho_reflect`), and the kernel weight is larger at the partner
(`κ(ŝ) ≥ κ(s)`).  The abstract inequality behind "the partner pays for the deficit" is:
`0 < a ≤ b`, `0 ≤ y`, `0 ≤ x + y  ⟹  0 ≤ a·x + b·y`.
-/

import OddCycleBound.HighDensity.RhoLemma

namespace OddCycleBound.HighDensity

/-- **Abstract weighted reflection.**  With `a = κ(s) ≤ κ(ŝ) = b` (both positive), `x = ρ(q+s)` the
possibly-negative value, `y = ρ(q+ŝ) ≥ 0` the partner value, and `x + y ≥ 0` (reflection), the
`κ`-weighted pair is nonnegative: `a·x + b·y = a·(x+y) + (b−a)·y ≥ 0`. -/
lemma reflection_weighted {a b x y : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hy : 0 ≤ y)
    (hxy : 0 ≤ x + y) : 0 ≤ a * x + b * y := by
  nlinarith [mul_nonneg ha hxy, mul_nonneg (sub_nonneg.mpr hab) hy]

end OddCycleBound.HighDensity
