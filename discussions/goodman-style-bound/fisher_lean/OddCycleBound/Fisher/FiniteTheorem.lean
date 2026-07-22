import OddCycleBound.Fisher.Spectral
import OddCycleBound.Fisher.CubicOpt

/-!
# Module 8 — Fisher's finite theorem

Corresponds to `fisher.tex`, Theorem `thm:fisher-finite` and Corollary
`cor:density-form`; Module 8 of the blueprint.

Combines the cubic-root consequence (Module 5), the spectral estimate
(Module 6), and the cubic optimisation (Module 7):

`R ≥ r(G) ≥ n - 2e/n ≥ x₋`, and `φ` is minimised at `x₊` on `[x₋, ∞)`, so
`T = φ(R) ≥ φ(x₊) = (9en - 2n³ - 2(n² - 3e)^{3/2})/27`.
-/

namespace Fisher

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Fisher's finite triangle lower bound** (`thm:fisher-finite`).
Assuming `n²/4 ≤ e ≤ n²/3`,
`T ≥ (9en - 2n³ - 2(n² - 3e)^{3/2}) / 27`. -/
theorem fisher_finite
    (hlo : (nR G) ^ 2 / 4 ≤ eR G) (hhi : eR G ≤ (nR G) ^ 2 / 3) :
    TR G ≥
      (9 * eR G * nR G - 2 * (nR G) ^ 3
        - 2 * ((nR G) ^ 2 - 3 * eR G) ^ ((3 : ℝ) / 2)) / 27 := by
  by_cases hn0 : nR G = 0
  · have he_nonneg : 0 ≤ eR G := by simp [eR]
    have he0 : eR G = 0 := by
      apply le_antisymm
      · simpa [hn0] using hhi
      · exact he_nonneg
    have hT_nonneg : 0 ≤ TR G := by simp [TR]
    simpa [hn0, he0] using hT_nonneg
  · have hn_nonneg : 0 ≤ nR G := by simp [nR]
    have hn_pos : 0 < nR G := lt_of_le_of_ne hn_nonneg (Ne.symm hn0)
    obtain ⟨R, hgrowthR, hTR⟩ := exists_root_ge_growth G hn_pos
    have havg :
        nR G - 2 * eR G / nR G ≤ growthFactor G :=
      growth_ge_avg_degree G
    have hxminus :
        xMinus (nR G) (eR G) ≤ nR G - 2 * eR G / nR G :=
      avg_degree_ge_xMinus (nR G) (eR G) hn_pos hhi
    have hR : xMinus (nR G) (eR G) ≤ R :=
      hxminus.trans (havg.trans hgrowthR)
    have hmin :
        cubic (nR G) (eR G) (xPlus (nR G) (eR G)) ≤
          cubic (nR G) (eR G) R :=
      cubic_min_at_xPlus (nR G) (eR G) hhi hR
    have hvalue := cubic_value_xPlus (nR G) (eR G) hhi
    calc
      (9 * eR G * nR G - 2 * (nR G) ^ 3
          - 2 * ((nR G) ^ 2 - 3 * eR G) ^ ((3 : ℝ) / 2)) / 27 =
          cubic (nR G) (eR G) (xPlus (nR G) (eR G)) := hvalue.symm
      _ ≤ cubic (nR G) (eR G) R := hmin
      _ = TR G := by simpa [cubic, phi] using hTR.symm

/-- **Density form** (`cor:density-form`).  With `p = 2e/n²`, `q = 6T/n³` and
`1/2 ≤ p ≤ 2/3`,
`q ≥ p - 4/9 - (4/9)(1 - 3p/2)^{3/2}`. -/
theorem fisher_density_form
    (hn : 0 < nR G)
    (p q : ℝ) (hp : p = 2 * eR G / (nR G) ^ 2) (hq : q = 6 * TR G / (nR G) ^ 3)
    (hplo : 1 / 2 ≤ p) (hphi : p ≤ 2 / 3) :
    q ≥ p - 4 / 9 - (4 / 9) * (1 - 3 * p / 2) ^ ((3 : ℝ) / 2) := by
  have hn0 : nR G ≠ 0 := hn.ne'
  have hn2_pos : 0 < (nR G) ^ 2 := sq_pos_of_pos hn
  have hn3_pos : 0 < (nR G) ^ 3 := pow_pos hn _
  have heq : eR G = p * (nR G) ^ 2 / 2 := by
    have hp' := hp
    field_simp [hn0] at hp'
    nlinarith
  have hlo : (nR G) ^ 2 / 4 ≤ eR G := by
    rw [heq]
    nlinarith
  have hhi : eR G ≤ (nR G) ^ 2 / 3 := by
    rw [heq]
    nlinarith
  have hf := fisher_finite G hlo hhi
  have ha : 0 ≤ 1 - 3 * p / 2 := by nlinarith
  have hrad :
      (nR G) ^ 2 - 3 * eR G = (nR G) ^ 2 * (1 - 3 * p / 2) := by
    rw [heq]
    ring
  have hn_rpow :
      ((nR G) ^ 2) ^ ((3 : ℝ) / 2) = (nR G) ^ 3 := by
    rw [Real.rpow_div_two_eq_sqrt (3 : ℝ) (sq_nonneg (nR G))]
    norm_num
    rw [Real.sqrt_sq hn.le]
  have hrad_rpow :
      ((nR G) ^ 2 - 3 * eR G) ^ ((3 : ℝ) / 2) =
        (nR G) ^ 3 * (1 - 3 * p / 2) ^ ((3 : ℝ) / 2) := by
    rw [hrad, Real.mul_rpow (sq_nonneg (nR G)) ha, hn_rpow]
  have hscale : 0 ≤ 6 / (nR G) ^ 3 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hf hscale
  rw [hrad_rpow, heq] at hscaled
  rw [hq]
  calc
    p - 4 / 9 - (4 / 9) * (1 - 3 * p / 2) ^ ((3 : ℝ) / 2) =
        (6 / (nR G) ^ 3) *
          ((9 * (p * (nR G) ^ 2 / 2) * nR G - 2 * (nR G) ^ 3
            - 2 * ((nR G) ^ 3 * (1 - 3 * p / 2) ^ ((3 : ℝ) / 2))) / 27) := by
              field_simp [hn0]
              ring
    _ ≤ (6 / (nR G) ^ 3) * TR G := hscaled
    _ = 6 * TR G / (nR G) ^ 3 := by ring

end Fisher
