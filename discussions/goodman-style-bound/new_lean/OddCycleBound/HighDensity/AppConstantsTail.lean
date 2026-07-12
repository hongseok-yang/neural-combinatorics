/-
# High-density theorem — `app:constants`, `eq:constant-A` `m ≥ 500` uniform tail

This file glues the three already-proved `eq:constant-A` ingredients into the single `m ≥ 500`
statement of `app:constants`:

* `P_ge_51`     (`StripAssembly.lean`)   — `P(θ) = (2/3−2θ)/(θ(1/2−2θ)²) ≥ 51` on `0 < θ ≤ 1/6`,
* `B0_ge`       (`AppConstantsB0.lean`)   — `201/200 ≤ B₀(θ)` on `0 ≤ θ ≤ 1/6`,
* `constA_tail` (`AppConstants.lean`)     — `(99/(100m))·51·(201/200)^m ≥ 1` for `m ≥ 500`.

Combining `51 ≤ P(θ)` with `(201/200)^m ≤ B₀(θ)^m` (monotonicity of `x ↦ x^m` on `x ≥ 0`) and the
tail arithmetic gives `(99/(100m))·P(θ)·B₀(θ)^m ≥ 1`, which is `eq:constant-A` at `m ≥ 500`.
-/

import OddCycleBound.HighDensity.AppConstants
import OddCycleBound.HighDensity.AppConstantsB0
import OddCycleBound.HighDensity.StripAssembly

namespace OddCycleBound.HighDensity

/-- **`eq:constant-A`, `m ≥ 500` uniform tail.**  For `0 < θ ≤ 1/6` and `m ≥ 500`,
`(99/(100m))·P(θ)·B₀(θ)^m ≥ 1`.  Assembles `P_ge_51`, `B0_ge`, and `constA_tail`. -/
theorem constA_m500 {m : ℕ} (hm : 500 ≤ m) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 6) :
    1 ≤ 99 / (100 * (m : ℝ)) * ((2 / 3 - 2 * θ) / (θ * (1 / 2 - 2 * θ) ^ 2)) * (B0 θ) ^ m := by
  set P : ℝ := (2 / 3 - 2 * θ) / (θ * (1 / 2 - 2 * θ) ^ 2) with hPdef
  -- the three ingredients
  have hP : (51 : ℝ) ≤ P := P_ge_51 hθ0 hθ
  have hB : (201 / 200 : ℝ) ≤ B0 θ := B0_ge hθ0.le hθ
  have htail : 1 ≤ 99 / (100 * (m : ℝ)) * 51 * (201 / 200) ^ m := constA_tail hm
  -- `(201/200)^m ≤ B₀(θ)^m`
  have hBm : (201 / 200 : ℝ) ^ m ≤ (B0 θ) ^ m := pow_le_pow_left₀ (by norm_num) hB m
  have hBmpos : (0 : ℝ) ≤ (201 / 200 : ℝ) ^ m := by positivity
  -- coefficient `99/(100m) ≥ 0`
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (500 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hcoef : (0 : ℝ) ≤ 99 / (100 * (m : ℝ)) := by positivity
  -- `51·(201/200)^m ≤ P·B₀(θ)^m`
  have hprod : (51 : ℝ) * (201 / 200) ^ m ≤ P * (B0 θ) ^ m :=
    mul_le_mul hP hBm hBmpos (by linarith)
  -- chain everything
  have hchain : 99 / (100 * (m : ℝ)) * 51 * (201 / 200) ^ m
      ≤ 99 / (100 * (m : ℝ)) * P * (B0 θ) ^ m := by
    calc 99 / (100 * (m : ℝ)) * 51 * (201 / 200) ^ m
        = 99 / (100 * (m : ℝ)) * (51 * (201 / 200) ^ m) := by ring
      _ ≤ 99 / (100 * (m : ℝ)) * (P * (B0 θ) ^ m) := by
            exact mul_le_mul_of_nonneg_left hprod hcoef
      _ = 99 / (100 * (m : ℝ)) * P * (B0 θ) ^ m := by ring
  linarith [htail, hchain]

end OddCycleBound.HighDensity
