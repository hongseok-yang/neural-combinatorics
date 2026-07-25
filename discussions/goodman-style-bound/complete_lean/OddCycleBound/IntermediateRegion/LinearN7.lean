import OddCycleBound.IntermediateRegion.LinearHighZeta
import OddCycleBound.IntermediateRegion.Bernstein

/-!
# The `N = 7` corner of the linear branch — small `v` (paper §9, `lem:N7-small-v`, line 3329)

Under `N = 7`, `ζ ≤ 7`, `0 < v ≤ 1/4`, `eq:linear-core` holds.  The proof (with `s = √v`) uses
`ℓ < (15/16)s` (`eq:ell-small-v`), `ξ ≥ 1/(4v)` (`eq:xi-small-v`, reduced to the polynomial
`16α(p−α)(α−q) ≥ e²`), the SOS lower bound `eq:cxi-small-v-poly`, the defect bound
`T₇ ≤ 6 + 15v/2 + v³/2`, and finally the Bernstein certificate `bernsteinP9_pos` (`eq:P9-small`).
-/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

namespace AdmissibleParams

variable (P : AdmissibleParams)

/-- `4·v·ξ = 16α(p−α)(α−q)/e²` (cleared form of `eq:xi-zeta-v`). -/
theorem four_v_xi_eq :
    4 * P.chartV * P.xi = 16 * P.alpha * (P.p - P.alpha) * (P.alpha - P.q) / P.e ^ 2 := by
  have hα := P.alpha_pos.ne'
  have he := P.e_pos.ne'
  unfold chartV chartSigma xi d
  field_simp
  ring

/-- `ζ ≤ 7` in cleared form: `L² ≤ 7α(α−q)`. -/
theorem chartZeta_le_seven_iff (hζ : P.chartZeta ≤ 7) : P.L ^ 2 ≤ 7 * P.alpha * (P.alpha - P.q) := by
  have hzu : P.chartZeta * P.chartU = P.ell ^ 2 := P.chartZeta_mul_chartU
  have hαell : P.alpha ^ 2 * P.ell ^ 2 = P.L ^ 2 := by rw [← mul_pow, P.alpha_mul_ell]
  have hu : P.chartU = (P.alpha - P.q) / P.alpha := by
    unfold chartU tau; rw [sub_div, div_self P.alpha_pos.ne']
  have h1 : P.ell ^ 2 ≤ 7 * P.chartU := hzu ▸ mul_le_mul_of_nonneg_right hζ P.chartU_pos.le
  have h2 : P.L ^ 2 ≤ 7 * P.alpha ^ 2 * P.chartU := by
    nlinarith [hαell, mul_le_mul_of_nonneg_left h1 (sq_nonneg P.alpha)]
  rw [hu] at h2
  have h3 : 7 * P.alpha ^ 2 * ((P.alpha - P.q) / P.alpha) = 7 * P.alpha * (P.alpha - P.q) := by
    field_simp
  rwa [h3] at h2

/-- Paper `eq:xi-small-v` (line 3346), raw form: `16α(p−α)(α−q) ≥ e²`, using `v ≤ 1/4` and `ζ ≤ 7`. -/
theorem xi_small_v_raw (hv : P.chartV ≤ 1 / 4) (hζ : P.chartZeta ≤ 7) :
    P.e ^ 2 ≤ 16 * P.alpha * (P.p - P.alpha) * (P.alpha - P.q) := by
  have hα := P.alpha_pos
  have hd : 0 < P.alpha - P.q := sub_pos.mpr P.alpha_gt_q
  have hcv : 0 ≤ 5 * P.alpha - 4 + 4 * P.q := by
    have hvV : P.chartV = (P.p - P.alpha) / P.alpha := by
      unfold chartV chartSigma; rw [sub_div, div_self hα.ne']
    rw [hvV, div_le_iff₀ hα] at hv
    unfold p at hv; linarith
  have hL2 := P.chartZeta_le_seven_iff hζ
  have hLsq : P.L ^ 2 = P.p * P.q - P.alpha ^ 2 := P.L_sq
  have hcz : 0 ≤ 8 * P.alpha ^ 2 - 7 * P.alpha * P.q - P.q + P.q ^ 2 := by
    unfold p at hL2 hLsq; nlinarith [hL2, hLsq]
  have hQ3 : 0 ≤ 3 * P.q - 1 := by linarith [P.q_gt_third]
  have hHalf : 0 ≤ 1 - 2 * P.alpha := by linarith [P.alpha_lt_half]
  have hSq : 0 ≤ 1 - 2 * P.q := by linarith [P.q_lt_half]
  unfold e p
  nlinarith [mul_nonneg hcz hHalf, mul_nonneg hcz hSq, mul_nonneg hd.le hHalf,
    mul_nonneg (mul_nonneg hcv hd.le) hSq, mul_nonneg (mul_nonneg hcv hHalf) hHalf,
    mul_nonneg (mul_nonneg hcv hSq) hSq, mul_nonneg (mul_nonneg hd.le hQ3) hHalf]

/-- Paper `eq:cxi-small-v-poly` (line 3383): `M(1+2v)√(1+v/2) ≤ (1+v)⁷` where `M = (1−7v/8)(1+5v+11v²)`,
via the SOS identity `eq:small-v-square-diff`. -/
theorem n7_sos {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 1 / 4) :
    (1 - 7 * v / 8) * (1 + 5 * v + 11 * v ^ 2) * (1 + 2 * v) * Real.sqrt (1 + v / 2)
      ≤ (1 + v) ^ 7 := by
  have hsqv : Real.sqrt (1 + v / 2) ^ 2 = 1 + v / 2 := Real.sq_sqrt (by linarith)
  have hL0 : 0 ≤ (1 - 7 * v / 8) * (1 + 5 * v + 11 * v ^ 2) * (1 + 2 * v) * Real.sqrt (1 + v / 2) := by
    have : 0 ≤ 1 - 7 * v / 8 := by linarith
    positivity
  have hsq : ((1 - 7 * v / 8) * (1 + 5 * v + 11 * v ^ 2) * (1 + 2 * v) * Real.sqrt (1 + v / 2)) ^ 2
      ≤ ((1 + v) ^ 7) ^ 2 := by
    have hpaper : 0 ≤ v * (128 * v ^ 13 + 1792 * v ^ 12 + 11648 * v ^ 11 + 46592 * v ^ 10
        + 128128 * v ^ 9 + 232540 * v ^ 8 + 345884 * v ^ 7 + 492971 * v ^ 6 + 464196 * v ^ 5
        + 258097 * v ^ 4 + 86924 * v ^ 3 + 18035 * v ^ 2 + 2254 * v + 160) := by positivity
    nlinarith [hpaper, hsqv]
  have hh := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hL0, Real.sqrt_sq (by positivity)] at hh

/-- Paper `eq:P9-small` (line 3420): the algebraic identity `9·M·(1−15s/16)(1+s²−15s/16) −
(6+15s²/2+s⁶/2) = P₉(s)`. -/
theorem n7_p9_id (s : ℝ) :
    9 * ((1 - 7 * s ^ 2 / 8) * (1 + 5 * s ^ 2 + 11 * (s ^ 2) ^ 2))
        * ((1 - 15 / 16 * s) * (1 + s ^ 2 - 15 / 16 * s))
      = 6 + 15 * s ^ 2 / 2 + (s ^ 2) ^ 3 / 2 + IntermediateRegion.bernsteinP9 s := by
  unfold IntermediateRegion.bernsteinP9; ring

set_option maxHeartbeats 400000 in
/-- **Paper lem:N7-small-v (line 3329):** `N = 7`, `ζ ≤ 7`, `0 < v ≤ 1/4` ⟹ `eq:linear-core`. -/
theorem linear_N7_small_v (hN7 : P.chartN = 7) (hζ : P.chartZeta ≤ 7) (hv : P.chartV ≤ 1 / 4) :
    P.chartTN ≤ ((P.chartN : ℝ) + 2) * P.chartCxi * (1 - P.ell) * (P.chartSigma - P.ell)
      * P.chartSigma ^ (P.chartN - 1) := by
  have hvpos : 0 < P.chartV := P.chartV_pos
  have hσ : P.chartSigma = 1 + P.chartV := P.chartSigma_eq_one_add
  have hα := P.alpha_pos
  set s := Real.sqrt P.chartV with hsdef
  have hs2 : s ^ 2 = P.chartV := Real.sq_sqrt P.chartV_pos.le
  have hs0 : 0 < s := Real.sqrt_pos.2 P.chartV_pos
  have hs12 : s ≤ 1 / 2 := by nlinarith [hs2, hv, hs0]
  -- φ ≥ (1+v)/(1+2v), with φ kept opaque
  have h4vξ : 1 ≤ 4 * P.chartV * P.xi := by
    rw [P.four_v_xi_eq, le_div_iff₀ (show (0 : ℝ) < P.e ^ 2 by have := P.e_pos; positivity)]
    linarith [P.xi_small_v_raw hv hζ]
  have hφ : (1 + P.chartV) / (1 + 2 * P.chartV) ≤ (1 + 4 * P.xi) / (2 + 4 * P.xi) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith [P.xi_pos])]
    nlinarith [h4vξ, hvpos, P.xi_pos]
  set phi := (1 + 4 * P.xi) / (2 + 4 * P.xi) with hphidef
  have hphipos : 0 < phi := by
    rw [hphidef]; exact div_pos (by linarith [P.xi_pos]) (by linarith [P.xi_pos])
  have hchartCxi : P.chartCxi = Real.sqrt (2 * P.alpha) * phi := by
    rw [hphidef]; unfold chartCxi; rw [mul_div_assoc]
  have hσ2 : (0 : ℝ) < 1 + 2 * P.chartV := by linarith
  have hφ2v : 1 + P.chartV ≤ phi * (1 + 2 * P.chartV) := (div_le_iff₀ hσ2).mp hφ
  -- ℓ < (15/16) s
  have hℓ2 : P.ell ^ 2 < 225 / 256 * P.chartV := by
    have hzv := P.zeta_v_div_eq_ell_sq
    have hden : 0 < P.chartZeta + 1 + P.chartV := by linarith [P.chartZeta_pos, hvpos]
    rw [← hzv, div_lt_iff₀ hden]
    nlinarith [hζ, hvpos, P.chartZeta_pos]
  have hℓ : P.ell < 15 / 16 * s := by
    have h := Real.sqrt_lt_sqrt (sq_nonneg P.ell)
      (show P.ell ^ 2 < (15 / 16 * s) ^ 2 by nlinarith [hℓ2, hs2])
    rwa [Real.sqrt_sq P.ell_pos.le, Real.sqrt_sq (by positivity)] at h
  have hℓ1 : P.ell < 1 := by nlinarith [hℓ, hs12]
  -- ζ ≥ 1 - v/2, T_7 ≤ 6 + 15v/2 + v³/2
  have hζlow : 1 - P.chartV / 2 ≤ P.chartZeta := by
    nlinarith [P.zeta_domain, P.chartZeta_pos, hvpos]
  have hs7 : s ^ 7 ≤ P.chartV ^ 3 / 2 := by
    rw [show s ^ 7 = (s ^ 2) ^ 3 * s by ring, hs2]; nlinarith [hs12, pow_nonneg hvpos.le 3]
  have hT7 : P.chartTN ≤ 6 + 15 * P.chartV / 2 + P.chartV ^ 3 / 2 := by
    have h := P.chartTN_le_one
    rw [hN7, ← hsdef] at h
    push_cast at h
    have hsvN : (0 : ℝ) < 1 - s ^ 7 := by nlinarith [hs7, pow_le_pow_left₀ hvpos.le hv 3]
    nlinarith [h, mul_le_mul_of_nonneg_right hζlow hsvN.le, hs7, pow_nonneg hs0.le 7,
      mul_nonneg (pow_nonneg hs0.le 7) hvpos.le]
  -- √(2α)·√(1+v/2) ≥ 1
  have hsqrt2a : 1 ≤ Real.sqrt (2 * P.alpha) * Real.sqrt (1 + P.chartV / 2) := by
    have hprod : 1 ≤ 2 * P.alpha * (1 + P.chartV / 2) := by
      have := P.alpha_lower; rw [div_lt_iff₀ (by linarith)] at this; nlinarith [this]
    rw [← Real.sqrt_mul (by positivity), show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by linarith [hprod])
  -- c_ξ σ^6 ≥ M := (1-7v/8)(1+5v+11v²)  (via the SOS bound eq:cxi-small-v-poly)
  have hsv2 : (0 : ℝ) < Real.sqrt (1 + P.chartV / 2) := Real.sqrt_pos.2 (by linarith)
  have hMcxi : (1 - 7 * P.chartV / 8) * (1 + 5 * P.chartV + 11 * P.chartV ^ 2)
      ≤ P.chartCxi * P.chartSigma ^ 6 := by
    have hSOS := n7_sos hvpos.le hv
    have hstep4 : (1 + P.chartV) ^ 7
        ≤ (P.chartCxi * P.chartSigma ^ 6) * (1 + 2 * P.chartV) * Real.sqrt (1 + P.chartV / 2) := by
      rw [hchartCxi, hσ]
      have hprod := mul_le_mul_of_nonneg_right
        (mul_le_mul hsqrt2a hφ2v (by positivity) (by positivity))
        (show (0 : ℝ) ≤ (1 + P.chartV) ^ 6 by positivity)
      nlinarith [hprod]
    have hpos : 0 < (1 + 2 * P.chartV) * Real.sqrt (1 + P.chartV / 2) := by positivity
    nlinarith [hSOS, hstep4, hpos]
  -- (1-15s/16)(1+s²-15s/16) ≤ (1-ℓ)(σ-ℓ)
  have hℓprod : (1 - 15 / 16 * s) * (1 + s ^ 2 - 15 / 16 * s)
      ≤ (1 - P.ell) * (P.chartSigma - P.ell) := by
    apply mul_le_mul (by linarith) (by rw [hσ, ← hs2]; linarith) (by nlinarith [hs12, sq_nonneg s])
      (by linarith)
  -- assemble via `bernsteinP9`
  have hMpos : (0 : ℝ) ≤ (1 - 7 * P.chartV / 8) * (1 + 5 * P.chartV + 11 * P.chartV ^ 2) := by
    have : 0 ≤ 1 - 7 * P.chartV / 8 := by linarith
    positivity
  have hℓprodpos : (0 : ℝ) ≤ (1 - 15 / 16 * s) * (1 + s ^ 2 - 15 / 16 * s) := by
    have : 0 ≤ 1 - 15 / 16 * s := by nlinarith [hs12]
    nlinarith [this, sq_nonneg s, hs0]
  have hσ6 : (0 : ℝ) ≤ P.chartSigma ^ 6 := by positivity
  have hRHS : 9 * ((1 - 7 * P.chartV / 8) * (1 + 5 * P.chartV + 11 * P.chartV ^ 2))
        * ((1 - 15 / 16 * s) * (1 + s ^ 2 - 15 / 16 * s))
      ≤ 9 * P.chartCxi * (1 - P.ell) * (P.chartSigma - P.ell) * P.chartSigma ^ 6 := by
    have hcombine : ((1 - 7 * P.chartV / 8) * (1 + 5 * P.chartV + 11 * P.chartV ^ 2))
        * ((1 - 15 / 16 * s) * (1 + s ^ 2 - 15 / 16 * s))
        ≤ (P.chartCxi * P.chartSigma ^ 6) * ((1 - P.ell) * (P.chartSigma - P.ell)) :=
      mul_le_mul hMcxi hℓprod hℓprodpos (mul_nonneg P.chartCxi_pos.le hσ6)
    nlinarith [hcombine]
  have hP9id : 9 * ((1 - 7 * P.chartV / 8) * (1 + 5 * P.chartV + 11 * P.chartV ^ 2))
        * ((1 - 15 / 16 * s) * (1 + s ^ 2 - 15 / 16 * s))
      = (6 + 15 * P.chartV / 2 + P.chartV ^ 3 / 2) + IntermediateRegion.bernsteinP9 s := by
    rw [← hs2]; exact n7_p9_id s
  have hP9 : 0 < IntermediateRegion.bernsteinP9 s :=
    IntermediateRegion.bernsteinP9_pos ⟨hs0.le, hs12⟩
  have hgoal : P.chartTN ≤ 9 * P.chartCxi * (1 - P.ell) * (P.chartSigma - P.ell) * P.chartSigma ^ 6 := by
    linarith [hT7, hRHS, hP9id, hP9]
  rw [hN7]
  have hcast : ((7 : ℕ) : ℝ) + 2 = 9 := by norm_num
  rw [show (7 : ℕ) - 1 = 6 from rfl, hcast]
  exact hgoal

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
