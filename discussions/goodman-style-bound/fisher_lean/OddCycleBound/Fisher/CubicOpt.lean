import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Module 7 — The one-variable optimisation of the cubic

Corresponds to `fisher.tex`, Lemma `lem:cubic-critical-points`, Lemma
`lem:spectral-beyond-xminus`, and Lemma `lem:cubic-value`; Module 7 of the
blueprint.

This module is *pure real analysis*: it depends on nothing from the graph side,
only on the reals `n, e` with `e ≤ n²/3`.  It is fully self-contained and is the
most immediately provable piece.

* Critical points of `φ(x) = x³ - n x² + e x` are `x∓ = (n ∓ s)/3`,
  `s = √(n² - 3e)`; `φ` decreases on `[x₋, x₊]` and increases beyond, so its
  minimum on `[x₋, ∞)` is at `x₊`.
* `n - 2e/n ≥ x₋`.
* `φ(x₊) = (9en - 2n³ - 2(n² - 3e)^{3/2}) / 27`.
-/

namespace Fisher

open Real

variable (n e : ℝ)

/-- The cubic `φ(x) = x³ - n x² + e x`. -/
noncomputable def cubic (x : ℝ) : ℝ := x ^ 3 - n * x ^ 2 + e * x

/-- `s = √(n² - 3e)`. -/
noncomputable def sPar : ℝ := Real.sqrt (n ^ 2 - 3 * e)

/-- Lower critical point `x₋ = (n - s)/3`. -/
noncomputable def xMinus : ℝ := (n - sPar n e) / 3
/-- Upper critical point `x₊ = (n + s)/3`. -/
noncomputable def xPlus : ℝ := (n + sPar n e) / 3

/-- **Critical points and monotonicity** (`lem:cubic-critical-points`): `φ`
attains its minimum on `[x₋, ∞)` at `x₊`, i.e. `φ x₊ ≤ φ y` for `y ≥ x₋`. -/
theorem cubic_min_at_xPlus (he : e ≤ n ^ 2 / 3) {y : ℝ} (hy : xMinus n e ≤ y) :
    cubic n e (xPlus n e) ≤ cubic n e y := by
  have hrad : 0 ≤ n ^ 2 - 3 * e := by nlinarith
  have hs0 : 0 ≤ sPar n e := by
    exact Real.sqrt_nonneg _
  have hs2 : (sPar n e) ^ 2 = n ^ 2 - 3 * e := by
    exact Real.sq_sqrt hrad
  have hcrit : 3 * (xPlus n e) ^ 2 - 2 * n * xPlus n e + e = 0 := by
    dsimp only [xPlus]
    nlinarith [hs2]
  have htail : 0 ≤ y + 2 * xPlus n e - n := by
    dsimp only [xMinus, xPlus] at hy ⊢
    linarith [hs0]
  have hfactor :
      cubic n e y - cubic n e (xPlus n e) =
        (y - xPlus n e) ^ 2 * (y + 2 * xPlus n e - n) := by
    calc
      cubic n e y - cubic n e (xPlus n e) =
          (y - xPlus n e) ^ 2 * (y + 2 * xPlus n e - n) +
            (y - xPlus n e) *
              (3 * (xPlus n e) ^ 2 - 2 * n * xPlus n e + e) := by
                simp only [cubic]
                ring
      _ = (y - xPlus n e) ^ 2 * (y + 2 * xPlus n e - n) := by rw [hcrit, mul_zero, add_zero]
  rw [← sub_nonneg, hfactor]
  exact mul_nonneg (sq_nonneg _) htail

/-- **Spectral bound lies beyond `x₋`** (`lem:spectral-beyond-xminus`). -/
theorem avg_degree_ge_xMinus (hn : 0 < n) (he : e ≤ n ^ 2 / 3) :
    xMinus n e ≤ n - 2 * e / n := by
  have hrad : 0 ≤ n ^ 2 - 3 * e := by nlinarith
  have hs0 : 0 ≤ sPar n e := Real.sqrt_nonneg _
  have hs2 : (sPar n e) ^ 2 = n ^ 2 - 3 * e := Real.sq_sqrt hrad
  have hrewrite :
      n - 2 * e / n = n / 3 + 2 * (sPar n e) ^ 2 / (3 * n) := by
    field_simp [hn.ne']
    nlinarith [hs2]
  have hterm : 0 ≤ 2 * (sPar n e) ^ 2 / (3 * n) := by positivity
  rw [hrewrite]
  dsimp [xMinus]
  linarith

/-- **Value at the critical point** (`lem:cubic-value`):
`φ(x₊) = (9en - 2n³ - 2(n² - 3e)^{3/2}) / 27`. -/
theorem cubic_value_xPlus (he : e ≤ n ^ 2 / 3) :
    cubic n e (xPlus n e)
      = (9 * e * n - 2 * n ^ 3 - 2 * (n ^ 2 - 3 * e) ^ ((3 : ℝ) / 2)) / 27 := by
  have hrad : 0 ≤ n ^ 2 - 3 * e := by nlinarith
  have hs2 : (sPar n e) ^ 2 = n ^ 2 - 3 * e := Real.sq_sqrt hrad
  have hrpow :
      (n ^ 2 - 3 * e) ^ ((3 : ℝ) / 2) = (sPar n e) ^ 3 := by
    rw [Real.rpow_div_two_eq_sqrt (3 : ℝ) hrad]
    norm_num [sPar]
  have hs3 : (sPar n e) ^ 3 = sPar n e * (n ^ 2 - 3 * e) := by
    calc
      (sPar n e) ^ 3 = sPar n e * (sPar n e) ^ 2 := by ring
      _ = sPar n e * (n ^ 2 - 3 * e) := by rw [hs2]
  rw [hrpow]
  dsimp [cubic, xPlus]
  ring_nf
  nlinarith [hs3]

end Fisher
