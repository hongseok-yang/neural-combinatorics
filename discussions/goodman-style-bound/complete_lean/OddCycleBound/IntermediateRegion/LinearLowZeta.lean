import OddCycleBound.IntermediateRegion.LinearCore
import OddCycleBound.IntermediateRegion.JGrowth

/-!
# Below the cycle scale (paper §9, `lem:linear-low-zeta`, line 3279)

If `ζ ≤ N` and `N ≥ 9` is odd, then `eq:linear-core` holds.  The proof applies `lem:J-growth`
(`JGrowth.J_growth`) with `x = ℓ`, together with the compensation lemma, `σ ≥ N(1+ℓ²)/(N−ℓ²)`,
`N−1−ζ/4 ≥ 3N/4−1`, and `1−ℓ > 2ℓ²/N`.
-/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

namespace AdmissibleParams

variable (P : AdmissibleParams)

set_option maxHeartbeats 800000 in
open OddCycleBound.IntermediateRegion in
/-- **Paper `lem:linear-low-zeta` (line 3279):** `ζ ≤ N`, odd `N ≥ 9` ⟹ `eq:linear-core`. -/
theorem linear_low_zeta (hN9 : 9 ≤ P.chartN) (hζ : P.chartZeta ≤ (P.chartN : ℝ)) :
    P.chartTN ≤ ((P.chartN : ℝ) + 2) * P.chartCxi * (1 - P.ell) * (P.chartSigma - P.ell)
      * P.chartSigma ^ (P.chartN - 1) := by
  have hNr : (0 : ℝ) < (P.chartN : ℝ) := by have := hN9; positivity
  have hNge : (9 : ℝ) ≤ (P.chartN : ℝ) := by exact_mod_cast hN9
  have hℓ0 : (0 : ℝ) ≤ P.ell := P.ell_pos.le
  have hℓ1 : P.ell < 1 := lt_trans P.ell_lt_tau P.tau_lt_one
  have hℓ2 : P.ell ^ 2 < 1 := by nlinarith [P.ell_pos]
  have hσpos : (0 : ℝ) < P.chartSigma := P.chartSigma_pos
  have hσa : P.chartSigma * P.tau = 1 + P.ell ^ 2 := P.chartSigma_mul_tau
  have hσge : 1 + P.ell ^ 2 ≤ P.chartSigma := by
    nlinarith [hσa, P.tau_lt_one, hσpos]
  have hσ1 : (1 : ℝ) ≤ P.chartSigma := by nlinarith [hσge, sq_nonneg P.ell]
  have hu : P.ell ^ 2 ≤ (P.chartN : ℝ) * P.chartU := by
    have := P.chartZeta_mul_chartU
    nlinarith [this, hζ, P.chartU_pos, mul_le_mul_of_nonneg_right hζ P.chartU_pos.le]
  have hNℓ2 : (0 : ℝ) < (P.chartN : ℝ) - P.ell ^ 2 := by nlinarith [hNge, hℓ2]
  -- `σ ≥ N(1+ℓ²)/(N−ℓ²)`
  have h1uc : (1 : ℝ) - P.chartU = P.tau := by unfold chartU; ring
  have hσlow : (P.chartN : ℝ) * (1 + P.ell ^ 2) / ((P.chartN : ℝ) - P.ell ^ 2) ≤ P.chartSigma := by
    rw [div_le_iff₀ hNℓ2]
    have h1 : (1 : ℝ) + P.ell ^ 2 = P.chartSigma * (1 - P.chartU) := by rw [h1uc]; linarith [hσa]
    nlinarith [h1, hu, hσpos, hNr,
      mul_nonneg hσpos.le (show (0 : ℝ) ≤ (P.chartN : ℝ) * P.chartU - P.ell ^ 2 by linarith [hu])]
  -- `2ℓ²/N ≤ 1−ℓ`
  have hdom : 2 * P.ell ^ 2 / (P.chartN : ℝ) ≤ 1 - P.ell := by
    rw [div_le_iff₀ hNr]
    have hae : P.chartU < P.tau - P.ell := P.tau_sub_ell_gt_chartU
    nlinarith [hu, hae, h1uc, hNr,
      mul_nonneg hNr.le (show (0 : ℝ) ≤ 2 * P.tau - 1 - P.ell by nlinarith [hae, h1uc])]
  -- oddness: `N = 2k+9`
  have hodd : ∃ k : ℕ, (P.chartN : ℝ) = 2 * (k : ℝ) + 9 := by
    obtain ⟨t, ht⟩ := P.m_odd
    have hn : 9 ≤ P.chartN := hN9
    have hcn : P.chartN = 2 * (t - 5) + 9 := by unfold chartN at hn ⊢; omega
    exact ⟨t - 5, by rw [hcn]; push_cast; ring⟩
  -- `J_growth` with `x = ℓ`
  have hJ := J_growth hodd hNge hℓ0 hℓ1 hdom
  set big : ℝ := ((P.chartN : ℝ) * (1 + P.ell ^ 2) / ((P.chartN : ℝ) - P.ell ^ 2))
    ^ (3 * (P.chartN : ℝ) / 4 - 1) with hbigdef
  have hbig0 : (0 : ℝ) ≤ big := by
    rw [hbigdef]; positivity
  have hJN : (P.chartN : ℝ) ≤ ((P.chartN : ℝ) + 2) * (1 - P.ell) ^ 2 * (1 + P.ell ^ 3) * big := by
    have h := mul_le_mul_of_nonneg_left hJ hNr.le
    rw [mul_one] at h
    have e : (P.chartN : ℝ) * (((P.chartN : ℝ) + 2) / (P.chartN : ℝ) * (1 - P.ell) ^ 2
        * (1 + P.ell ^ 3) * big) = ((P.chartN : ℝ) + 2) * (1 - P.ell) ^ 2 * (1 + P.ell ^ 3) * big := by
      field_simp
    rwa [e] at h
  -- exponent split `σ^{N-1} = σ^{ζ/4}·σ^{N-1-ζ/4}`
  have hcast : ((P.chartN - 1 : ℕ) : ℝ) = (P.chartN : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hσNat : P.chartSigma ^ (P.chartN - 1) = P.chartSigma ^ (P.chartZeta / 4)
      * P.chartSigma ^ ((P.chartN : ℝ) - 1 - P.chartZeta / 4) := by
    rw [← Real.rpow_natCast P.chartSigma (P.chartN - 1), hcast, ← Real.rpow_add hσpos]
    congr 1; ring
  set e' : ℝ := (P.chartN : ℝ) - 1 - P.chartZeta / 4 with he'def
  have he'ge : 3 * (P.chartN : ℝ) / 4 - 1 ≤ e' := by
    rw [he'def]; linarith [hζ]
  have hσe' : big ≤ P.chartSigma ^ e' := by
    calc big ≤ P.chartSigma ^ (3 * (P.chartN : ℝ) / 4 - 1) := by
            rw [hbigdef]
            exact Real.rpow_le_rpow (by positivity) hσlow (by linarith [hNge])
      _ ≤ P.chartSigma ^ e' := Real.rpow_le_rpow_of_exponent_le hσ1 he'ge
  have hσe'0 : (0 : ℝ) ≤ P.chartSigma ^ e' := Real.rpow_nonneg hσpos.le _
  have hζ40 : (0 : ℝ) ≤ P.chartSigma ^ (P.chartZeta / 4) := Real.rpow_nonneg hσpos.le _
  have hcomp := P.compensation
  have h1ℓ : (0 : ℝ) ≤ 1 - P.ell := by linarith
  have hσℓ : (0 : ℝ) ≤ P.chartSigma - P.ell := by nlinarith [hσge, P.ell_pos, sq_nonneg P.ell]
  have h1ℓ3 : 1 + P.ell ^ 3 ≤ (1 + P.ell) * (P.chartSigma - P.ell) := by
    nlinarith [hσge, P.ell_pos, sq_nonneg P.ell]
  -- assemble `N ≤ linear-core RHS`
  have key : (P.chartN : ℝ) ≤ ((P.chartN : ℝ) + 2) * P.chartCxi * (1 - P.ell)
      * (P.chartSigma - P.ell) * P.chartSigma ^ (P.chartN - 1) := by
    rw [hσNat]
    calc (P.chartN : ℝ)
        ≤ ((P.chartN : ℝ) + 2) * (1 - P.ell) ^ 2 * (1 + P.ell ^ 3) * big := hJN
      _ ≤ ((P.chartN : ℝ) + 2) * (1 - P.ell) ^ 2 * (1 + P.ell ^ 3) * P.chartSigma ^ e' := by
          gcongr
      _ ≤ ((P.chartN : ℝ) + 2) * (1 - P.ell) ^ 2 * ((1 + P.ell) * (P.chartSigma - P.ell))
            * P.chartSigma ^ e' := by gcongr
      _ = ((P.chartN : ℝ) + 2) * (1 - P.ell) * ((1 - P.ell) * (1 + P.ell))
            * (P.chartSigma - P.ell) * P.chartSigma ^ e' := by ring
      _ = ((P.chartN : ℝ) + 2) * (1 - P.ell) * (1 - P.ell ^ 2)
            * (P.chartSigma - P.ell) * P.chartSigma ^ e' := by ring
      _ ≤ ((P.chartN : ℝ) + 2) * (1 - P.ell) * (P.chartCxi * P.chartSigma ^ (P.chartZeta / 4))
            * (P.chartSigma - P.ell) * P.chartSigma ^ e' := by gcongr
      _ = ((P.chartN : ℝ) + 2) * P.chartCxi * (1 - P.ell) * (P.chartSigma - P.ell)
            * (P.chartSigma ^ (P.chartZeta / 4) * P.chartSigma ^ e') := by ring
  -- `T_N < N`
  have hTN : P.chartTN < (P.chartN : ℝ) := by
    have h := P.chartTN_lt
    have hℓpow : (0 : ℝ) < P.ell ^ (P.chartN + 1) := pow_pos P.ell_pos _
    nlinarith [h, hℓpow, hNr]
  linarith [hTN, key]

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
