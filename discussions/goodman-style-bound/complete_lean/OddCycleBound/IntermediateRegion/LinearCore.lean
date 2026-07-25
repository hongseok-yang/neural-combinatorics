import OddCycleBound.IntermediateRegion.LinearBranch
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The linear core (paper §9, `paper_new_region2_v2.tex` lines 2822–3547)

This file proves `eq:linear-core` — the hypothesis of `scalar_target_of_linear_core` — via the paper's
compensation lemma and the case analysis of `prop:linear-branch`.  The single hardest input, the
one-variable growth lemma `lem:J-growth`, is developed in `JGrowth.lean`.

This increment establishes the **compensation lemma** (`lem:compensation`, line 2827):
`c_ξ·σ^{ζ/4} ≥ 1 − ℓ²`, split into `√(2α) ≥ 1 − ℓ²` (`eq:sqrt-compensation`) and `φ·σ^{ζ/4} ≥ 1`.
The `ξ`-lower bound `4ζvξ > 16/3` (`eq:xi-comp-bound`) reduces to the same polynomial
`3L²(p−α) > e²` proved in `QuadraticBranch.quad_coeff_raw`.
-/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

namespace AdmissibleParams

variable (P : AdmissibleParams)

/-! ### `ζ ≥ a > 3/4` (paper eq:zeta-lower, line 2494) -/

/-- Paper eq:zeta-lower (line 2494): `ζ ≥ a` (from `au ≤ ℓ²`). -/
theorem tau_le_chartZeta : P.tau ≤ P.chartZeta := by
  rw [chartZeta, le_div_iff₀ P.chartU_pos]
  have := P.tau_mul_chartU_le_ell_sq
  linarith

theorem chartZeta_gt_three_quarters : 3 / 4 < P.chartZeta :=
  lt_of_lt_of_le P.tau_gt_three_quarters P.tau_le_chartZeta

/-! ### `√(2α) ≥ 1 − ℓ²` (paper eq:sqrt-compensation, line 2836) -/

theorem sqrt_compensation : 1 - P.ell ^ 2 ≤ Real.sqrt (2 * P.alpha) := by
  have hℓ1 : P.ell ^ 2 < 1 := by
    have hℓa : P.ell < P.tau := P.ell_lt_tau
    have ha1 : P.tau < 1 := P.tau_lt_one
    nlinarith [P.ell_pos]
  -- reduce to `2a ≥ D(1−y)²`, i.e. the polynomial in `a = τ`, `y = ℓ²`.
  have hαD : P.alpha * P.chartD = P.tau := P.alpha_mul_chartD
  have hDpos := P.chartD_pos
  have hpoly : (1 - P.ell ^ 2) ^ 2 ≤ 2 * P.alpha := by
    -- `2a ≥ (1+a²+y)(1-y)²` with the chart-domain generators
    have hy_ge : P.tau * P.chartU ≤ P.ell ^ 2 := P.tau_mul_chartU_le_ell_sq
    have ha34 : 3 / 4 < P.tau := P.tau_gt_three_quarters
    have hu : P.chartU = 1 - P.tau := rfl
    have ha1 : P.tau < 1 := P.tau_lt_one
    have hℓa2 : P.ell ^ 2 < P.tau ^ 2 := by nlinarith [P.ell_lt_tau, P.ell_pos]
    -- `2a - D(1-y)² ≥ 0` then divide by `D`
    have hkey : (1 - P.ell ^ 2) ^ 2 * P.chartD ≤ 2 * P.tau := by
      unfold chartD
      rw [hu] at hy_ge
      have g1 : 0 ≤ P.ell ^ 2 - P.tau + P.tau ^ 2 := by nlinarith [hy_ge]
      have g2 : 0 ≤ P.tau - 3 / 4 := by linarith
      have g3 : 0 ≤ 1 - P.tau := by linarith
      have g4 : 0 ≤ 1 - P.ell ^ 2 := by linarith
      have g5 : 0 ≤ P.ell ^ 2 := sq_nonneg _
      have g6 : 0 ≤ P.tau ^ 2 - P.ell ^ 2 := by linarith [hℓa2]
      nlinarith [mul_nonneg (mul_nonneg g1 g4) g5, mul_nonneg (mul_nonneg g2 g4) g5,
        mul_nonneg (mul_nonneg g3 g4) g6, mul_nonneg (mul_nonneg g1 g2) g4,
        mul_nonneg g2 g3, mul_nonneg g2 g5, mul_nonneg g5 g6, g1, g5, g4]
    have h2 : (1 - P.ell ^ 2) ^ 2 * P.chartD ≤ 2 * P.alpha * P.chartD := by
      have : 2 * P.tau = 2 * P.alpha * P.chartD := by rw [← hαD]; ring
      rw [this] at hkey; exact hkey
    exact le_of_mul_le_mul_right h2 hDpos
  have h1ℓ : 0 ≤ 1 - P.ell ^ 2 := by linarith
  calc 1 - P.ell ^ 2 = Real.sqrt ((1 - P.ell ^ 2) ^ 2) := (Real.sqrt_sq h1ℓ).symm
    _ ≤ Real.sqrt (2 * P.alpha) := Real.sqrt_le_sqrt hpoly

/-! ### `4ζvξ > 16/3` (paper eq:xi-comp-bound, line 2862) -/

/-- Paper eq:xi-comp-bound (line 2862): `4ζvξ > 16/3`, from `quad_coeff_raw` (`3L²(p−α) > e²`). -/
theorem four_zeta_v_xi_gt : (16 : Real) / 3 < 4 * P.chartZeta * P.chartV * P.xi := by
  have hraw := P.quad_coeff_raw
  have he : (0 : Real) < P.e ^ 2 := by have := P.e_pos; positivity
  have hid : 4 * P.chartZeta * P.chartV * P.xi = 16 * P.L ^ 2 * (P.p - P.alpha) / P.e ^ 2 := by
    have hα := P.alpha_pos.ne'
    have hd : P.alpha - P.q ≠ 0 := (sub_pos.mpr P.alpha_gt_q).ne'
    have he' := P.e_pos.ne'
    unfold chartZeta ell chartU tau chartV chartSigma xi d p
    field_simp
    ring
  rw [hid, lt_div_iff₀ he]
  linarith [hraw]

/-! ### `ζv(1+4ξ) > 2(v+2)` (paper eq:key-log-comp, line 2866) -/

/-- Paper eq:key-log-comp (line 2866): `ζv(1+4ξ) > 2(v+2)`. -/
theorem key_log_comp : 2 * (P.chartV + 2) < P.chartZeta * P.chartV * (1 + 4 * P.xi) := by
  have hxi := P.four_zeta_v_xi_gt
  have hζ34 : 3 / 4 < P.chartZeta := P.chartZeta_gt_three_quarters
  have hv1 : P.chartV < 1 := P.chartV_lt_one
  have hvpos : 0 < P.chartV := P.chartV_pos
  have hζpos : 0 < P.chartZeta := P.chartZeta_pos
  -- `ζv(1+4ξ) = ζv + 4ζvξ > ζv + 16/3`; then case `ζ≥2` / `ζ<2`.
  by_cases hζ2 : 2 ≤ P.chartZeta
  · nlinarith [hxi, hζ2, hvpos]
  · have hζ2' : P.chartZeta < 2 := not_le.mp hζ2
    nlinarith [hxi, hζ34, hv1, hvpos, mul_pos hvpos (sub_pos.mpr hζ2')]

end AdmissibleParams

/-! ### The log lower bound `log(1+v) ≥ 2v/(v+2)` (paper line 2879) -/

/-- Paper (line 2879): `log(1+v) ≥ 2v/(v+2)` for `v ≥ 0`, via monotonicity of
`g(t) = log(1+t) − 2t/(t+2)` (`g(0) = 0`, `g' = t²/((1+t)(t+2)²) ≥ 0`). -/
theorem log_lower_bound {v : ℝ} (hv : 0 ≤ v) : 2 * v / (v + 2) ≤ Real.log (1 + v) := by
  have hHD : ∀ x : ℝ, 0 ≤ x →
      HasDerivAt (fun t => Real.log (1 + t) - 2 * t / (t + 2))
        (1 / (1 + x) - (2 * (x + 2) - 2 * x * 1) / (x + 2) ^ 2) x := by
    intro x hx
    have h1x : (1 : ℝ) + x ≠ 0 := by positivity
    have h2x : x + 2 ≠ 0 := by positivity
    have hlog : HasDerivAt (fun t => Real.log (1 + t)) (1 / (1 + x)) x := by
      have := ((hasDerivAt_id x).const_add (1 : ℝ)).log h1x
      simpa [one_div] using this
    have hnum : HasDerivAt (fun t => 2 * t) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    have hden : HasDerivAt (fun t => t + 2) 1 x := (hasDerivAt_id x).add_const 2
    have hfrac : HasDerivAt (fun t => 2 * t / (t + 2))
        ((2 * (x + 2) - 2 * x * 1) / (x + 2) ^ 2) x := hnum.div hden h2x
    exact hlog.sub hfrac
  have hcont : ContinuousOn (fun t => Real.log (1 + t) - 2 * t / (t + 2)) (Set.Ici 0) :=
    fun x hx => (hHD x hx).continuousAt.continuousWithinAt
  have hmono : MonotoneOn (fun t => Real.log (1 + t) - 2 * t / (t + 2)) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      exact (hHD x hx.le).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      rw [(hHD x hx.le).deriv]
      have h1x : (0 : ℝ) < 1 + x := by linarith
      have h2x : (0 : ℝ) < x + 2 := by linarith
      have hcombine : 1 / (1 + x) - (2 * (x + 2) - 2 * x * 1) / (x + 2) ^ 2
          = x ^ 2 / ((1 + x) * (x + 2) ^ 2) := by
        field_simp; ring
      rw [hcombine]; positivity
  have h := hmono Set.self_mem_Ici (Set.mem_Ici.mpr hv) hv
  simp only [Real.log_one, add_zero, mul_zero, zero_div, sub_zero] at h
  linarith

namespace AdmissibleParams

variable (P : AdmissibleParams)

/-! ### The compensation lemma (paper lem:compensation, line 2827) -/

/-- Paper `φσ^{ζ/4} ≥ 1` (line 2854): via `key_log_comp`, `log_lower_bound`, and `e^t > 1+t`. -/
theorem phi_sigma_ge : 1 ≤ (1 + 4 * P.xi) / (2 + 4 * P.xi) * P.chartSigma ^ (P.chartZeta / 4) := by
  have hξ := P.xi_pos
  have hσ : P.chartSigma = 1 + P.chartV := P.chartSigma_eq_one_add
  have hσpos : 0 < P.chartSigma := P.chartSigma_pos
  have hvpos : 0 < P.chartV := P.chartV_pos
  have hden1 : (0 : ℝ) < 1 + 4 * P.xi := by linarith
  have hden2 : (0 : ℝ) < 2 + 4 * P.xi := by linarith
  have hlog : 2 * P.chartV / (P.chartV + 2) ≤ Real.log P.chartSigma := by
    rw [hσ]; exact log_lower_bound P.chartV_pos.le
  have hζ4 : (0 : ℝ) ≤ P.chartZeta / 4 := by have := P.chartZeta_pos; positivity
  have hv2 : (0 : ℝ) < P.chartV + 2 := by linarith
  set t : ℝ := Real.log P.chartSigma * (P.chartZeta / 4) with ht
  have htlow : 1 / (1 + 4 * P.xi) < t := by
    have hquot : 1 / (1 + 4 * P.xi) < P.chartZeta * P.chartV / (2 * (P.chartV + 2)) := by
      rw [div_lt_div_iff₀ hden1 (by positivity)]
      nlinarith [P.key_log_comp]
    have hle2 : P.chartZeta * P.chartV / (2 * (P.chartV + 2)) ≤ t := by
      have e : P.chartZeta * P.chartV / (2 * (P.chartV + 2))
          = (2 * P.chartV / (P.chartV + 2)) * (P.chartZeta / 4) := by
        field_simp; ring
      rw [e, ht]
      exact mul_le_mul_of_nonneg_right hlog hζ4
    linarith
  have htpos : 0 < t := lt_trans (by positivity) htlow
  have hexp : P.chartSigma ^ (P.chartZeta / 4) = Real.exp t := Real.rpow_def_of_pos hσpos _
  have hlt : t + 1 < Real.exp t := Real.add_one_lt_exp htpos.ne'
  rw [hexp]
  have hφpos : (0 : ℝ) < (1 + 4 * P.xi) / (2 + 4 * P.xi) := div_pos hden1 hden2
  have hgt : (2 + 4 * P.xi) / (1 + 4 * P.xi) < Real.exp t := by
    have h1 : (2 + 4 * P.xi) / (1 + 4 * P.xi) = 1 + 1 / (1 + 4 * P.xi) := by
      field_simp; ring
    rw [h1]; linarith [hlt, htlow]
  have hmul := mul_lt_mul_of_pos_left hgt hφpos
  have heq : (1 + 4 * P.xi) / (2 + 4 * P.xi) * ((2 + 4 * P.xi) / (1 + 4 * P.xi)) = 1 := by
    field_simp
  rw [heq] at hmul
  linarith [hmul]

/-- **Paper lem:compensation (line 2827):** `c_ξ·σ^{ζ/4} ≥ 1 − ℓ²`. -/
theorem compensation : 1 - P.ell ^ 2 ≤ P.chartCxi * P.chartSigma ^ (P.chartZeta / 4) := by
  have hsqrt := P.sqrt_compensation
  have hphi := P.phi_sigma_ge
  have hden2 : (0 : ℝ) < 2 + 4 * P.xi := by linarith [P.xi_pos]
  have hid : P.chartCxi * P.chartSigma ^ (P.chartZeta / 4)
      = Real.sqrt (2 * P.alpha) * ((1 + 4 * P.xi) / (2 + 4 * P.xi) * P.chartSigma ^ (P.chartZeta / 4)) := by
    unfold chartCxi; ring
  rw [hid]
  calc 1 - P.ell ^ 2 ≤ Real.sqrt (2 * P.alpha) := hsqrt
    _ = Real.sqrt (2 * P.alpha) * 1 := (mul_one _).symm
    _ ≤ Real.sqrt (2 * P.alpha) * ((1 + 4 * P.xi) / (2 + 4 * P.xi) * P.chartSigma ^ (P.chartZeta / 4)) :=
        mul_le_mul_of_nonneg_left hphi (Real.sqrt_nonneg _)

/-! ### The crude `c_ξ` bound (paper eq:cxi-crude, line 2917) -/

/-- `α > 1/(2+v)` (from `q < α` and `p = (1+v)α`). -/
theorem alpha_lower : 1 / (2 + P.chartV) < P.alpha := by
  have hv2 : (0 : ℝ) < 2 + P.chartV := by linarith [P.chartV_pos]
  have hpα : P.p = (1 + P.chartV) * P.alpha := by
    have h1 : P.chartSigma * P.alpha = P.p := by
      have hα := P.alpha_pos.ne'; unfold chartSigma; field_simp
    rw [P.chartSigma_eq_one_add] at h1; linarith [h1]
  have hq : P.q = 1 - P.p := by unfold p; ring
  rw [div_lt_iff₀ hv2]
  nlinarith [P.alpha_gt_q, hpα, hq]

/-- Paper eq:cxi-crude (line 2917): `c_ξ > 1/√(2(2+v))`, from `α > 1/(2+v)` and `φ > 1/2`. -/
theorem cxi_crude : 1 / Real.sqrt (2 * (2 + P.chartV)) < P.chartCxi := by
  have hv2 : (0 : ℝ) < 2 + P.chartV := by linarith [P.chartV_pos]
  have hs : 0 < Real.sqrt (2 * (2 + P.chartV)) := Real.sqrt_pos.2 (by positivity)
  have hden2 : (0 : ℝ) < 2 + 4 * P.xi := by linarith [P.xi_pos]
  have hφpos : (0 : ℝ) < (1 + 4 * P.xi) / (2 + 4 * P.xi) :=
    div_pos (by linarith [P.xi_pos]) hden2
  have hφ : 1 / 2 < (1 + 4 * P.xi) / (2 + 4 * P.xi) := by
    rw [lt_div_iff₀ hden2]; linarith [P.xi_pos]
  have hαprod : 1 < P.alpha * (2 + P.chartV) := by
    have := P.alpha_lower; rw [div_lt_iff₀ hv2] at this; linarith [this]
  have hsqrt1 : 1 < Real.sqrt (P.alpha * (2 + P.chartV)) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_lt_sqrt (by norm_num) hαprod
  rw [div_lt_iff₀ hs]
  have hprod : P.chartCxi * Real.sqrt (2 * (2 + P.chartV))
      = 2 * Real.sqrt (P.alpha * (2 + P.chartV)) * ((1 + 4 * P.xi) / (2 + 4 * P.xi)) := by
    have hcomb : Real.sqrt (2 * P.alpha) * Real.sqrt (2 * (2 + P.chartV))
        = 2 * Real.sqrt (P.alpha * (2 + P.chartV)) := by
      rw [← Real.sqrt_mul (by have := P.alpha_pos; positivity),
        show 2 * P.alpha * (2 * (2 + P.chartV)) = 4 * (P.alpha * (2 + P.chartV)) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
        show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    unfold chartCxi
    rw [show Real.sqrt (2 * P.alpha) * (1 + 4 * P.xi) / (2 + 4 * P.xi) * Real.sqrt (2 * (2 + P.chartV))
        = (Real.sqrt (2 * P.alpha) * Real.sqrt (2 * (2 + P.chartV))) * ((1 + 4 * P.xi) / (2 + 4 * P.xi)) by
      ring, hcomb]
  rw [hprod]
  nlinarith [hsqrt1, hφ, mul_pos (sub_pos.mpr hsqrt1) hφpos]

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
