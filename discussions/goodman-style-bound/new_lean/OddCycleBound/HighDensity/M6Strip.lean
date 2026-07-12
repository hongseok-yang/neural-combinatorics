/-
# High-density theorem — the residual strip (M6), analytic tail `m ≥ 63`

The residual range (`eq:remaining-range`) is `q ≤ 1/3`, `r ≥ 2`, `n > 2r`, `0 < ℓ < q+r/m`.  For
`m ≥ 63` the paper splits on `θ = r/m` and uses a reflection/threshold argument (`lem:threshold`,
`lem:right-reflection`, `lem:left-estimate`).

This file begins with **`lem:threshold`** (`threshold_bound`): the calculus maximum bound
`H(b) = m/((r-1)/b + (n-1)/(n/m)) − b ≤ 2/5` for `0 < b`, `m ≥ 63` odd, `r/m ≥ 1/6`, `n = m−2r`,
`n > 2r`.  It feeds `lem:right-reflection`.  Proved algebraically (no `√`) by completing the square:
`H(b) ≤ 2/5 ⟺ mb ≤ (b+2/5)(A₀ + B₀b)` with `A₀ = r-1`, `B₀ = (n-1)m/n`, which holds because the
discriminant `(A₀ + (2/5)B₀ − m)² ≤ (8/5)A₀B₀` (a cleared quartic in `n,r`, closed by `nlinarith`).
-/

import Mathlib.Tactic

open scoped BigOperators

namespace OddCycleBound.HighDensity

/-- **`lem:threshold`.**  For odd `m ≥ 63`, `r/m ≥ 1/6` (`m ≤ 6r`), `n = m−2r`, `n > 2r`, and `b > 0`:
`H(b) = m/((r-1)/b + (n-1)/(n/m)) − b ≤ 2/5`.  The maximum of `H` over `b > 0` is `(√m−√(r-1))²/B₀`
(`B₀ = (n-1)m/n`); the bound `< 2/5` is proved here without `√` via the discriminant of the quadratic
`B₀b² + (A₀ + (2/5)B₀ − m)b + (2/5)A₀ ≥ 0`. -/
theorem threshold_bound {m r n : ℕ} (hm63 : 63 ≤ m) (hmodd : m % 2 = 1) (h6r : m ≤ 6 * r)
    (hmn : m = n + 2 * r) (hn2r : 2 * r < n) {b : ℝ} (hb0 : 0 < b) :
    (m : ℝ) / (((r : ℝ) - 1) / b + ((n : ℝ) - 1) / ((n : ℝ) / (m : ℝ))) - b ≤ 2 / 5 := by
  -- real forms of the (integer) constraints
  have hr11 : (11 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 11 ≤ r by omega)
  have h9 : 2 * (n : ℝ) + 13 ≤ 9 * (r : ℝ) := by exact_mod_cast (show 2 * n + 13 ≤ 9 * r by omega)
  have h2 : 2 * (r : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (show 2 * r + 1 ≤ n by omega)
  have hn33 : (33 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 33 ≤ n by omega)
  have hmR : (m : ℝ) = (n : ℝ) + 2 * (r : ℝ) := by exact_mod_cast hmn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hm0 : (0 : ℝ) < (m : ℝ) := by rw [hmR]; linarith
  set A0 := (r : ℝ) - 1 with hA0def
  set B0 := ((n : ℝ) - 1) * (m : ℝ) / (n : ℝ) with hB0def
  have hA0pos : 0 < A0 := by rw [hA0def]; linarith
  have hB0pos : 0 < B0 := by
    rw [hB0def]; exact div_pos (mul_pos (by linarith) hm0) hn0
  -- rewrite the nested denominator `(n-1)/(n/m) = B₀`
  have hDrw : ((n : ℝ) - 1) / ((n : ℝ) / (m : ℝ)) = B0 := by
    rw [hB0def, div_div_eq_mul_div]
  rw [hDrw]
  -- discriminant inequality
  have hdisc : (A0 + (2 / 5) * B0 - (m : ℝ)) ^ 2 ≤ (8 / 5) * A0 * B0 := by
    have hcl : (5 * A0 * (n : ℝ) + 2 * ((n : ℝ) - 1) * (m : ℝ) - 5 * (m : ℝ) * (n : ℝ)) ^ 2
        ≤ 40 * A0 * ((n : ℝ) - 1) * (m : ℝ) * (n : ℝ) := by
      rw [hA0def, hmR]
      nlinarith [sq_nonneg ((n : ℝ) - 2 * (r : ℝ)), sq_nonneg ((n : ℝ) * (r : ℝ)),
        mul_pos hn0 (by linarith : (0 : ℝ) < (r : ℝ)), sq_nonneg ((n : ℝ) - (r : ℝ)),
        mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - 2 * (r : ℝ) - 1) hn0.le, h9, h2]
    have hkey : (A0 + (2 / 5) * B0 - (m : ℝ)) ^ 2 - (8 / 5) * A0 * B0
        = ((5 * A0 * (n : ℝ) + 2 * ((n : ℝ) - 1) * (m : ℝ) - 5 * (m : ℝ) * (n : ℝ)) ^ 2
            - 40 * A0 * ((n : ℝ) - 1) * (m : ℝ) * (n : ℝ)) / (25 * (n : ℝ) ^ 2) := by
      rw [hB0def]; field_simp; ring
    have hnum : (5 * A0 * (n : ℝ) + 2 * ((n : ℝ) - 1) * (m : ℝ) - 5 * (m : ℝ) * (n : ℝ)) ^ 2
        - 40 * A0 * ((n : ℝ) - 1) * (m : ℝ) * (n : ℝ) ≤ 0 := by linarith [hcl]
    have hratio : ((5 * A0 * (n : ℝ) + 2 * ((n : ℝ) - 1) * (m : ℝ) - 5 * (m : ℝ) * (n : ℝ)) ^ 2
        - 40 * A0 * ((n : ℝ) - 1) * (m : ℝ) * (n : ℝ)) / (25 * (n : ℝ) ^ 2) ≤ 0 :=
      div_nonpos_iff.mpr (Or.inr ⟨hnum, by positivity⟩)
    linarith [hkey, hratio]
  -- `mb ≤ (b + 2/5)(A₀ + B₀b)`  by completing the square
  have hcore : (m : ℝ) * b ≤ (b + 2 / 5) * (A0 + B0 * b) := by
    have hsq : 4 * B0 * ((b + 2 / 5) * (A0 + B0 * b) - (m : ℝ) * b)
        = (2 * B0 * b + (A0 + (2 / 5) * B0 - (m : ℝ))) ^ 2
          + ((8 / 5) * A0 * B0 - (A0 + (2 / 5) * B0 - (m : ℝ)) ^ 2) := by ring
    nlinarith [hsq, sq_nonneg (2 * B0 * b + (A0 + (2 / 5) * B0 - (m : ℝ))), hdisc, hB0pos, hb0]
  -- conclude `H(b) ≤ 2/5`
  have hABpos : 0 < A0 + B0 * b := add_pos hA0pos (mul_pos hB0pos hb0)
  have hcomb : A0 / b + B0 = (A0 + B0 * b) / b := by field_simp
  rw [hcomb, div_div_eq_mul_div, sub_le_iff_le_add, div_le_iff₀ hABpos]
  nlinarith [hcore]

end OddCycleBound.HighDensity
