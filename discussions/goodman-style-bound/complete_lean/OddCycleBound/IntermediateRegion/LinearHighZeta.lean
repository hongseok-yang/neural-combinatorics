import OddCycleBound.IntermediateRegion.LinearBroad

/-!
# The high-`ζ` linear-branch estimate (paper §9, `lem:linear-high-zeta`, line 2900)

If `ζ ≥ N` and `v ≤ 5/8` (any odd `N ≥ 7`), then `eq:linear-core` holds.  Again all calculus is avoided:
after `eq:T-high-zeta`, `eq:cxi-crude`, and dropping `(N+2)/N ≥ 1`, `(1+y²)^{N−6} ≥ 1`, `y^{N−2} ≤ y⁵`,
`√(2(2+y²)) ≤ 147/64`, the sufficient condition `eq:h-sufficient` reduces (with `y = √v ≤ 4/5`) to the
polynomial `(147/64)(1+y⁵)y² ≤ (1−y)(1−y+y²)(1+y²)⁵`, a Bernstein-positivity certificate on `[0,4/5]`.
-/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

/-- Paper `eq:h-sufficient` reduced form: `(147/64)(1+y⁵)y² ≤ (1−y)(1−y+y²)(1+y²)⁵` on `[0,4/5]`,
via a Bernstein-positivity certificate on `[0,4/5]` (all 14 coefficients positive). -/
theorem highzeta_base {y : ℝ} (hlo : 0 ≤ y) (hhi : y ≤ 4 / 5) :
    147 / 64 * (1 + y ^ 5) * y ^ 2 ≤ (1 - y) * (1 - y + y ^ 2) * (1 + y ^ 2) ^ 5 := by
  have ha : 0 ≤ 5 * y := by linarith
  have hb : 0 ≤ 4 - 5 * y := by linarith
  have term : ∀ (c : ℝ) (i j : ℕ), 0 ≤ c → 0 ≤ c * (5 * y) ^ i * (4 - 5 * y) ^ j :=
    fun c i j hc => mul_nonneg (mul_nonneg hc (pow_nonneg ha i)) (pow_nonneg hb j)
  have key : (4 : ℝ) ^ 13 * ((1 - y) * (1 - y + y ^ 2) * (1 + y ^ 2) ^ 5 - 147 / 64 * (1 + y ^ 5) * y ^ 2) =
        (1) * (5 * y) ^ 0 * (4 - 5 * y) ^ 13
      + (57 / 5) * (5 * y) ^ 1 * (4 - 5 * y) ^ 12
      + (6181 / 100) * (5 * y) ^ 2 * (4 - 5 * y) ^ 11
      + (103939 / 500) * (5 * y) ^ 3 * (4 - 5 * y) ^ 10
      + (240211 / 500) * (5 * y) ^ 4 * (4 - 5 * y) ^ 9
      + (401873 / 500) * (5 * y) ^ 5 * (4 - 5 * y) ^ 8
      + (6271877 / 6250) * (5 * y) ^ 6 * (4 - 5 * y) ^ 7
      + (148832671 / 156250) * (5 * y) ^ 7 * (4 - 5 * y) ^ 6
      + (108328461 / 156250) * (5 * y) ^ 8 * (4 - 5 * y) ^ 5
      + (300213423 / 781250) * (5 * y) ^ 9 * (4 - 5 * y) ^ 4
      + (6107852569 / 39062500) * (5 * y) ^ 10 * (4 - 5 * y) ^ 3
      + (8277051023 / 195312500) * (5 * y) ^ 11 * (4 - 5 * y) ^ 2
      + (5767250283 / 976562500) * (5 * y) ^ 12 * (4 - 5 * y) ^ 1
      + (202186509 / 4882812500) * (5 * y) ^ 13 * (4 - 5 * y) ^ 0 := by
    ring
  have hsum : 0 ≤ 4 ^ 13 * ((1 - y) * (1 - y + y ^ 2) * (1 + y ^ 2) ^ 5 - 147 / 64 * (1 + y ^ 5) * y ^ 2) := by
    rw [key]
    linarith [term (1) 0 13 (by norm_num), term (57 / 5) 1 12 (by norm_num),
      term (6181 / 100) 2 11 (by norm_num), term (103939 / 500) 3 10 (by norm_num),
      term (240211 / 500) 4 9 (by norm_num), term (401873 / 500) 5 8 (by norm_num),
      term (6271877 / 6250) 6 7 (by norm_num), term (148832671 / 156250) 7 6 (by norm_num),
      term (108328461 / 156250) 8 5 (by norm_num), term (300213423 / 781250) 9 4 (by norm_num),
      term (6107852569 / 39062500) 10 3 (by norm_num), term (8277051023 / 195312500) 11 2 (by norm_num),
      term (5767250283 / 976562500) 12 1 (by norm_num), term (202186509 / 4882812500) 13 0 (by norm_num)]
  nlinarith [hsum]

/-- Paper `eq:h-sufficient` assembled: `N(v+y^N)√(2(2+v)) ≤ (N+2)(1−y)(1−y+y²)(1+y²)^{N−1}`
(`y = √v`, `v ≤ 5/8`, odd `N ≥ 7`), from `highzeta_base` and the factor bounds. -/
theorem highzeta_targetHZ {N : ℕ} (hN : 7 ≤ N) {y v : ℝ} (hy2 : y ^ 2 = v) (hy0 : 0 < y)
    (hv58 : v ≤ 5 / 8) :
    (N : ℝ) * (v + y ^ N) * Real.sqrt (2 * (2 + v))
      ≤ ((N : ℝ) + 2) * (1 - y) * (1 - y + y ^ 2) * (1 + y ^ 2) ^ (N - 1) := by
  have hvpos : 0 < v := by rw [← hy2]; positivity
  have hy45 : y ≤ 4 / 5 := by
    have : y ^ 2 ≤ (4 / 5) ^ 2 := by rw [hy2]; nlinarith [hv58]
    nlinarith [this, hy0]
  have hy1 : y < 1 := by linarith
  have hNr : (7 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hbase := highzeta_base hy0.le hy45
  have hyNsplit : y ^ N = y ^ 2 * y ^ (N - 2) := by rw [← pow_add]; congr 1; omega
  have hyN2le5 : y ^ (N - 2) ≤ y ^ 5 := pow_le_pow_of_le_one hy0.le hy1.le (by omega)
  have hsqrtbound : Real.sqrt (2 * (2 + v)) ≤ 147 / 64 := by
    rw [show (147 : ℝ) / 64 = Real.sqrt ((147 / 64) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [hv58])
  have hsqrtpos : 0 < Real.sqrt (2 * (2 + v)) := Real.sqrt_pos.2 (by positivity)
  have hpowsplit : (1 + y ^ 2) ^ (N - 1) = (1 + y ^ 2) ^ 5 * (1 + y ^ 2) ^ (N - 6) := by
    rw [← pow_add]; congr 1; omega
  have h1y2 : (1 : ℝ) ≤ 1 + y ^ 2 := by nlinarith [hy0]
  have hNbound : (N : ℝ) ≤ ((N : ℝ) + 2) * (1 + y ^ 2) ^ (N - 6) := by
    nlinarith [(one_le_pow₀ h1y2 : (1 : ℝ) ≤ (1 + y ^ 2) ^ (N - 6)), hNr]
  have hfac : 0 ≤ (1 - y) * (1 - y + y ^ 2) * (1 + y ^ 2) ^ 5 := by
    have : 0 ≤ 1 - y := by linarith
    have : 0 ≤ 1 - y + y ^ 2 := by nlinarith [sq_nonneg y]
    positivity
  have hlhs : (N : ℝ) * (v + y ^ N) * Real.sqrt (2 * (2 + v))
      ≤ (N : ℝ) * (y ^ 2 * (1 + y ^ 5)) * (147 / 64) := by
    have e1 : v + y ^ N = y ^ 2 * (1 + y ^ (N - 2)) := by rw [← hy2, hyNsplit]; ring
    rw [e1]
    have hbnd : y ^ 2 * (1 + y ^ (N - 2)) ≤ y ^ 2 * (1 + y ^ 5) :=
      mul_le_mul_of_nonneg_left (by linarith [hyN2le5]) (by positivity)
    calc (N : ℝ) * (y ^ 2 * (1 + y ^ (N - 2))) * Real.sqrt (2 * (2 + v))
        ≤ (N : ℝ) * (y ^ 2 * (1 + y ^ 5)) * Real.sqrt (2 * (2 + v)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbnd (by positivity)) hsqrtpos.le
      _ ≤ (N : ℝ) * (y ^ 2 * (1 + y ^ 5)) * (147 / 64) :=
          mul_le_mul_of_nonneg_left hsqrtbound (by positivity)
  calc (N : ℝ) * (v + y ^ N) * Real.sqrt (2 * (2 + v))
      ≤ (N : ℝ) * (y ^ 2 * (1 + y ^ 5)) * (147 / 64) := hlhs
    _ = (N : ℝ) * (147 / 64 * (1 + y ^ 5) * y ^ 2) := by ring
    _ ≤ (N : ℝ) * ((1 - y) * (1 - y + y ^ 2) * (1 + y ^ 2) ^ 5) :=
        mul_le_mul_of_nonneg_left hbase (by positivity)
    _ ≤ ((N : ℝ) + 2) * (1 + y ^ 2) ^ (N - 6) * ((1 - y) * (1 - y + y ^ 2) * (1 + y ^ 2) ^ 5) :=
        mul_le_mul_of_nonneg_right hNbound hfac
    _ = ((N : ℝ) + 2) * (1 - y) * (1 - y + y ^ 2) * (1 + y ^ 2) ^ (N - 1) := by rw [hpowsplit]; ring

namespace AdmissibleParams

variable (P : AdmissibleParams)

/-- **Paper lem:linear-high-zeta (line 2900):** if `ζ ≥ N` and `v ≤ 5/8` (any odd `N ≥ 7`), then
`eq:linear-core`. -/
theorem linear_high_zeta (hζ : (P.chartN : ℝ) ≤ P.chartZeta) (hv : P.chartV ≤ 5 / 8) :
    P.chartTN ≤ ((P.chartN : ℝ) + 2) * P.chartCxi * (1 - P.ell) * (P.chartSigma - P.ell)
      * P.chartSigma ^ (P.chartN - 1) := by
  have hvpos : 0 < P.chartV := P.chartV_pos
  have hN7 : 7 ≤ P.chartN := by have := P.m_ge_nine; unfold chartN; omega
  have hσ : P.chartSigma = 1 + P.chartV := P.chartSigma_eq_one_add
  set y := Real.sqrt P.chartV with hy
  have hy2 : y ^ 2 = P.chartV := Real.sq_sqrt P.chartV_pos.le
  have hy0 : 0 < y := Real.sqrt_pos.2 P.chartV_pos
  have hy1 : y < 1 := by nlinarith [hy2, hvpos, P.chartV_lt_one, hy0]
  have hyNlt : y ^ P.chartN < 1 := P.chartVsqrtN_lt_one
  -- Step 1: `T_N ≤ N(v + y^N)`
  have h1yN : 0 < 1 - y ^ P.chartN := by linarith
  have hT1 : P.chartTN ≤ (P.chartN : ℝ) * (P.chartV + y ^ P.chartN) := by
    have h := P.chartTN_le_one
    rw [← hy] at h
    nlinarith [h, mul_le_mul_of_nonneg_right hζ h1yN.le]
  have hℓ0 : 0 ≤ P.ell := P.ell_pos.le
  have hℓy : P.ell ≤ y := by
    have h := Real.sqrt_le_sqrt P.ell_sq_lt_chartV.le
    rwa [Real.sqrt_sq hℓ0, ← hy] at h
  have hℓ1 : P.ell < 1 := lt_of_le_of_lt hℓy hy1
  -- `(1-y)(1-y+y²) ≤ (1-ℓ)(σ-ℓ)`
  have hσℓ : (1 - y) * (1 - y + y ^ 2) ≤ (1 - P.ell) * (P.chartSigma - P.ell) := by
    have h2n : 0 ≤ 1 - y + y ^ 2 := by nlinarith [sq_nonneg y]
    exact mul_le_mul (by linarith) (by rw [hσ, ← hy2]; linarith) h2n (by linarith)
  have hσpoweq : P.chartSigma ^ (P.chartN - 1) = (1 + y ^ 2) ^ (P.chartN - 1) := by rw [hσ, hy2]
  -- TargetHZ (extracted lemma) and cxi_crude
  have hTargetHZ := highzeta_targetHZ hN7 hy2 hy0 hv
  have hcxi := P.cxi_crude
  have hsqrtpos : 0 < Real.sqrt (2 * (2 + P.chartV)) := Real.sqrt_pos.2 (by positivity)
  -- `N(v+y^N) ≤ (N+2)·cξ·(1-ℓ)(σ-ℓ)·σ^{N-1}`
  have hchain : (P.chartN : ℝ) * (P.chartV + y ^ P.chartN)
      ≤ ((P.chartN : ℝ) + 2) * P.chartCxi * (1 - P.ell) * (P.chartSigma - P.ell)
        * P.chartSigma ^ (P.chartN - 1) := by
    rw [hσpoweq]
    have hstep : (P.chartN : ℝ) * (P.chartV + y ^ P.chartN)
        ≤ ((P.chartN : ℝ) + 2) * (1 / Real.sqrt (2 * (2 + P.chartV)))
          * ((1 - y) * (1 - y + y ^ 2)) * (1 + y ^ 2) ^ (P.chartN - 1) := by
      rw [show ((P.chartN : ℝ) + 2) * (1 / Real.sqrt (2 * (2 + P.chartV)))
            * ((1 - y) * (1 - y + y ^ 2)) * (1 + y ^ 2) ^ (P.chartN - 1)
          = (((P.chartN : ℝ) + 2) * (1 - y) * (1 - y + y ^ 2) * (1 + y ^ 2) ^ (P.chartN - 1))
            / Real.sqrt (2 * (2 + P.chartV)) by field_simp, le_div_iff₀ hsqrtpos]
      exact hTargetHZ
    calc (P.chartN : ℝ) * (P.chartV + y ^ P.chartN)
        ≤ ((P.chartN : ℝ) + 2) * (1 / Real.sqrt (2 * (2 + P.chartV)))
          * ((1 - y) * (1 - y + y ^ 2)) * (1 + y ^ 2) ^ (P.chartN - 1) := hstep
      _ ≤ ((P.chartN : ℝ) + 2) * P.chartCxi * ((1 - P.ell) * (P.chartSigma - P.ell))
          * (1 + y ^ 2) ^ (P.chartN - 1) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul (mul_le_mul_of_nonneg_left hcxi.le (by positivity)) hσℓ
              (mul_nonneg (by linarith) (by nlinarith [sq_nonneg y]))
              (mul_nonneg (by positivity) P.chartCxi_pos.le)
      _ = ((P.chartN : ℝ) + 2) * P.chartCxi * (1 - P.ell) * (P.chartSigma - P.ell)
          * (1 + y ^ 2) ^ (P.chartN - 1) := by ring
  linarith [hT1, hchain]

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
