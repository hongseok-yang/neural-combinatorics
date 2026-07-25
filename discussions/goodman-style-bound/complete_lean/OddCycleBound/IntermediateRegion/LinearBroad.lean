import OddCycleBound.IntermediateRegion.LinearCore

/-!
# The two broad linear-branch estimates (paper §9, lines 2900–3028)

`lem:linear-large-v` (`v ≥ 5/8`) is proved here.  The key simplification (avoiding all calculus) is the
rational tangent bound `√v ≤ 2v/3 + 3/8` (`(4√v−3)² ≥ 0`), giving `1+v−√v ≥ 5/8 + v/3`.  After
`eq:cxi-crude`, `eq:T-geometric-cancel`, and squaring, `eq:large-v-target` reduces to a polynomial
inequality proved by induction on `N` (base `N = 7` is a Bernstein-positivity certificate on `[5/8,1]`;
the step `N ↦ N+2` uses `28561(N+4)²N²(N+1)² ≥ 4096(N+2)⁴(N+3)²`, whose excess factors as
`(105N³+397N²−348N−768)(233N³+…)`).
-/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

/-- `√v ≤ 2v/3 + 3/8` for `v ≥ 0` (from `(4√v − 3)² ≥ 0`). -/
theorem sqrt_le_tangent {v : ℝ} (hv : 0 ≤ v) : Real.sqrt v ≤ 2 * v / 3 + 3 / 8 := by
  have hsq : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv
  nlinarith [sq_nonneg (4 * Real.sqrt v - 3), Real.sqrt_nonneg v, hsq]

/-- Bernoulli: `1 − ℓ^{N+1} ≤ (N+1)(1−ℓ)` (needs only `ℓ ≥ −1`). -/
theorem one_sub_pow_le_mul {ℓ : ℝ} (h0 : -1 ≤ ℓ) (N : ℕ) :
    1 - ℓ ^ (N + 1) ≤ (N + 1) * (1 - ℓ) := by
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ ℓ - 1 by linarith) (N + 1)
  have he : (1 + (ℓ - 1)) ^ (N + 1) = ℓ ^ (N + 1) := by congr 1; ring
  rw [he] at hb
  push_cast at hb ⊢
  nlinarith [hb]

/-- Base `N = 7` of `eq:large-v-target` (squared): `6272(2+v) ≤ 81(5/8+v/3)²(1+v)¹²` on `[5/8,1]`,
via a Bernstein-positivity certificate on `[5/8,1]` (all 15 coefficients positive). -/
theorem largev_base {v : ℝ} (hlo : 5 / 8 ≤ v) (hhi : v ≤ 1) :
    6272 * (2 + v) ≤ 81 * (5 / 8 + v / 3) ^ 2 * (1 + v) ^ 12 := by
  have ha : 0 ≤ 8 * v - 5 := by linarith
  have hb : 0 ≤ 8 - 8 * v := by linarith
  have term : ∀ (c : ℝ) (i j : ℕ), 0 ≤ c → 0 ≤ c * (8 * v - 5) ^ i * (8 - 8 * v) ^ j :=
    fun c i j hc => mul_nonneg (mul_nonneg hc (pow_nonneg ha i)) (pow_nonneg hb j)
  have key : (3 : ℝ) ^ 14 * (81 * (5 / 8 + v / 3) ^ 2 * (1 + v) ^ 12 - 6272 * (2 + v)) =
        (716479292632209 / 274877906944) * (8 * v - 5) ^ 0 * (8 - 8 * v) ^ 14
      + (50946634394371611 / 549755813888) * (8 * v - 5) ^ 1 * (8 - 8 * v) ^ 13
      + (4621619066927132361 / 4398046511104) * (8 * v - 5) ^ 2 * (8 - 8 * v) ^ 12
      + (440030248051873479 / 68719476736) * (8 * v - 5) ^ 3 * (8 - 8 * v) ^ 11
      + (214917207942261825 / 8589934592) * (8 * v - 5) ^ 4 * (8 - 8 * v) ^ 10
      + (18301101227075667 / 268435456) * (8 * v - 5) ^ 5 * (8 - 8 * v) ^ 9
      + (9095477904503991 / 67108864) * (8 * v - 5) ^ 6 * (8 - 8 * v) ^ 8
      + (105568483632183 / 524288) * (8 * v - 5) ^ 7 * (8 - 8 * v) ^ 7
      + (14800511100375 / 65536) * (8 * v - 5) ^ 8 * (8 - 8 * v) ^ 6
      + (391102542831 / 2048) * (8 * v - 5) ^ 9 * (8 - 8 * v) ^ 5
      + (123023940039 / 1024) * (8 * v - 5) ^ 10 * (8 - 8 * v) ^ 4
      + (874009227 / 16) * (8 * v - 5) ^ 11 * (8 - 8 * v) ^ 3
      + (33982977 / 2) * (8 * v - 5) ^ 12 * (8 - 8 * v) ^ 2
      + (3239712) * (8 * v - 5) ^ 13 * (8 - 8 * v) ^ 1
      + (285888) * (8 * v - 5) ^ 14 * (8 - 8 * v) ^ 0 := by
    ring
  have hsum : 0 ≤ 3 ^ 14 * (81 * (5 / 8 + v / 3) ^ 2 * (1 + v) ^ 12 - 6272 * (2 + v)) := by
    rw [key]
    linarith [term (716479292632209 / 274877906944) 0 14 (by norm_num),
      term (50946634394371611 / 549755813888) 1 13 (by norm_num),
      term (4621619066927132361 / 4398046511104) 2 12 (by norm_num),
      term (440030248051873479 / 68719476736) 3 11 (by norm_num),
      term (214917207942261825 / 8589934592) 4 10 (by norm_num),
      term (18301101227075667 / 268435456) 5 9 (by norm_num),
      term (9095477904503991 / 67108864) 6 8 (by norm_num),
      term (105568483632183 / 524288) 7 7 (by norm_num),
      term (14800511100375 / 65536) 8 6 (by norm_num),
      term (391102542831 / 2048) 9 5 (by norm_num),
      term (123023940039 / 1024) 10 4 (by norm_num),
      term (874009227 / 16) 11 3 (by norm_num),
      term (33982977 / 2) 12 2 (by norm_num),
      term (3239712 : ℝ) 13 1 (by norm_num),
      term (285888 : ℝ) 14 0 (by norm_num)]
  nlinarith [hsum]

/-- Paper `eq:large-v-target` (squared), by induction on `N = 2k+7` (base is `largev_base`, step is the
factored polynomial `28561(N+4)²N²(N+1)² ≥ 4096(N+2)⁴(N+3)²`). -/
theorem largev_targetSq (k : ℕ) {v : ℝ} (hlo : 5 / 8 ≤ v) (hhi : v ≤ 1) :
    2 * (2 * (k : ℝ) + 7) ^ 2 * ((2 * (k : ℝ) + 7) + 1) ^ 2 * (2 + v)
      ≤ ((2 * (k : ℝ) + 7) + 2) ^ 2 * (5 / 8 + v / 3) ^ 2 * (1 + v) ^ (4 * k + 12) := by
  induction k with
  | zero =>
    have hbase := largev_base hlo hhi
    norm_num
    nlinarith [hbase]
  | succ k ih =>
    set N : ℝ := 2 * (k : ℝ) + 7 with hN
    have hNge : (7 : ℝ) ≤ N := by rw [hN]; have := Nat.cast_nonneg (α := ℝ) k; linarith
    have h1v : (13 : ℝ) / 8 ≤ 1 + v := by linarith
    have h2v : (0 : ℝ) < 2 + v := by linarith
    have hpoly4 : ((13 : ℝ) / 8) ^ 4 ≤ (1 + v) ^ 4 := pow_le_pow_left₀ (by norm_num) h1v 4
    have hnpoly : 4096 * (N + 2) ^ 4 * (N + 3) ^ 2 ≤ 28561 * (N + 4) ^ 2 * N ^ 2 * (N + 1) ^ 2 := by
      have hc1 : 0 ≤ 105 * N ^ 3 + 397 * N ^ 2 - 348 * N - 768 := by nlinarith [hNge]
      have hc2 : 0 ≤ 233 * N ^ 3 + 1293 * N ^ 2 + 1700 * N + 768 := by nlinarith [hNge]
      nlinarith [mul_nonneg hc1 hc2]
    have hstep_poly : (N + 2) ^ 4 * (N + 3) ^ 2 ≤ N ^ 2 * (N + 1) ^ 2 * (N + 4) ^ 2 * (1 + v) ^ 4 := by
      nlinarith [hnpoly, hpoly4, mul_nonneg (mul_nonneg (sq_nonneg N) (sq_nonneg (N + 1)))
        (sq_nonneg (N + 4)), sq_nonneg (N + 2), sq_nonneg (N + 3), hNge]
    have hexp : (1 + v) ^ (4 * (k + 1) + 12) = (1 + v) ^ (4 * k + 12) * (1 + v) ^ 4 := by
      rw [show 4 * (k + 1) + 12 = (4 * k + 12) + 4 by ring, pow_add]
    have hcastN : (2 * ((k + 1 : ℕ) : ℝ) + 7) = N + 2 := by rw [hN]; push_cast; ring
    rw [hcastN, hexp]
    -- `ih : 2 N² (N+1)² (2+v) ≤ (N+2)² (5/8+v/3)² (1+v)^{4k+12}`.
    have hih2 := mul_le_mul_of_nonneg_right ih
      (show (0 : ℝ) ≤ (N + 4) ^ 2 * (1 + v) ^ 4 by positivity)
    have hN2 : (0 : ℝ) < (N + 2) ^ 2 := by positivity
    nlinarith [hih2, mul_le_mul_of_nonneg_right hstep_poly (show (0 : ℝ) ≤ 2 * (2 + v) by linarith),
      hN2, h2v]

namespace AdmissibleParams

variable (P : AdmissibleParams)

/-- **Paper lem:linear-large-v (line 2984):** if `v ≥ 5/8` (any odd `N ≥ 7`), then `eq:linear-core`. -/
theorem linear_large_v (hv : 5 / 8 ≤ P.chartV) :
    P.chartTN ≤ ((P.chartN : ℝ) + 2) * P.chartCxi * (1 - P.ell) * (P.chartSigma - P.ell)
      * P.chartSigma ^ (P.chartN - 1) := by
  have hℓ0 : 0 ≤ P.ell := P.ell_pos.le
  have hℓ1 : P.ell < 1 := (P.ell_lt_tau).trans P.tau_lt_one
  have h1ℓ : 0 < 1 - P.ell := by linarith
  have hvlt : P.chartV < 1 := P.chartV_lt_one
  have hvpos : 0 < P.chartV := P.chartV_pos
  have hσ : P.chartSigma = 1 + P.chartV := P.chartSigma_eq_one_add
  have hcxipos := P.chartCxi_pos
  -- `T_N < N(N+1)(1−ℓ)`
  have hTN : P.chartTN < (P.chartN : ℝ) * ((P.chartN : ℝ) + 1) * (1 - P.ell) := by
    have h1 := P.chartTN_lt
    have h2 := one_sub_pow_le_mul (by linarith : (-1 : ℝ) ≤ P.ell) P.chartN
    have hN0 : (0 : ℝ) ≤ (P.chartN : ℝ) := by positivity
    nlinarith [h1, mul_le_mul_of_nonneg_left h2 hN0]
  -- `σ − ℓ ≥ 5/8 + v/3`
  have hℓsqrt : P.ell ≤ Real.sqrt P.chartV := by
    have h := Real.sqrt_le_sqrt P.ell_sq_lt_chartV.le
    rwa [Real.sqrt_sq hℓ0] at h
  have hσℓ : 5 / 8 + P.chartV / 3 ≤ P.chartSigma - P.ell := by
    have ht := sqrt_le_tangent (show (0 : ℝ) ≤ P.chartV by linarith)
    rw [hσ]; linarith [hℓsqrt, ht]
  have hσℓpos : 0 < P.chartSigma - P.ell := by
    have : 0 < 5 / 8 + P.chartV / 3 := by linarith
    linarith [hσℓ]
  -- the squared target via `largev_targetSq`
  have hs : 0 < Real.sqrt (2 * (2 + P.chartV)) := Real.sqrt_pos.2 (by positivity)
  obtain ⟨k, hk⟩ : ∃ k, P.chartN = 2 * k + 7 := by
    have h1 := P.two_mul_chartR
    have h2 : 7 ≤ P.chartN := by have := P.m_ge_nine; unfold chartN; omega
    exact ⟨P.chartR - 4, by omega⟩
  have hkcast : (2 * (k : ℝ) + 7) = (P.chartN : ℝ) := by rw [hk]; push_cast; ring
  have hexpeq : 4 * k + 12 = 2 * (P.chartN - 1) := by rw [hk]; omega
  -- restate `largev_targetSq` in chart terms
  have hTargetSq : ((P.chartN : ℝ) * ((P.chartN : ℝ) + 1)) ^ 2 * (2 * (2 + P.chartV))
      ≤ (((P.chartN : ℝ) + 2) * (5 / 8 + P.chartV / 3) * (1 + P.chartV) ^ (P.chartN - 1)) ^ 2 := by
    have := largev_targetSq k (by linarith : (5 : ℝ) / 8 ≤ P.chartV) (le_of_lt hvlt)
    rw [hkcast, hexpeq] at this
    rw [show (2 * (P.chartN - 1)) = (P.chartN - 1) * 2 by ring, pow_mul] at this
    nlinarith [this]
  -- Target: `N(N+1)√(2(2+v)) ≤ (N+2)(5/8+v/3)(1+v)^{N-1}`
  have hNNpos : 0 ≤ (P.chartN : ℝ) * ((P.chartN : ℝ) + 1) := by positivity
  have hBpos : 0 ≤ ((P.chartN : ℝ) + 2) * (5 / 8 + P.chartV / 3) * (1 + P.chartV) ^ (P.chartN - 1) := by
    have : 0 < 5 / 8 + P.chartV / 3 := by linarith
    positivity
  have hTarget : (P.chartN : ℝ) * ((P.chartN : ℝ) + 1) * Real.sqrt (2 * (2 + P.chartV))
      ≤ ((P.chartN : ℝ) + 2) * (5 / 8 + P.chartV / 3) * (1 + P.chartV) ^ (P.chartN - 1) := by
    have hsq : (Real.sqrt (2 * (2 + P.chartV))) ^ 2 = 2 * (2 + P.chartV) :=
      Real.sq_sqrt (by positivity)
    have hAsq : ((P.chartN : ℝ) * ((P.chartN : ℝ) + 1) * Real.sqrt (2 * (2 + P.chartV))) ^ 2
        ≤ (((P.chartN : ℝ) + 2) * (5 / 8 + P.chartV / 3) * (1 + P.chartV) ^ (P.chartN - 1)) ^ 2 := by
      rw [mul_pow, hsq]; nlinarith [hTargetSq]
    have hAnn : 0 ≤ (P.chartN : ℝ) * ((P.chartN : ℝ) + 1) * Real.sqrt (2 * (2 + P.chartV)) :=
      mul_nonneg hNNpos (Real.sqrt_nonneg _)
    nlinarith [hAsq, hAnn, hBpos, sq_nonneg (((P.chartN : ℝ) + 2) * (5 / 8 + P.chartV / 3)
      * (1 + P.chartV) ^ (P.chartN - 1) - (P.chartN : ℝ) * ((P.chartN : ℝ) + 1)
      * Real.sqrt (2 * (2 + P.chartV)))]
  -- `N(N+1) ≤ (N+2)·cξ·(σ−ℓ)·σ^{N−1}`
  have hcs : 1 / Real.sqrt (2 * (2 + P.chartV)) * (5 / 8 + P.chartV / 3)
      ≤ P.chartCxi * (P.chartSigma - P.ell) :=
    mul_le_mul P.cxi_crude.le hσℓ (by positivity) hcxipos.le
  have hmain : (P.chartN : ℝ) * ((P.chartN : ℝ) + 1)
      ≤ ((P.chartN : ℝ) + 2) * P.chartCxi * (P.chartSigma - P.ell) * P.chartSigma ^ (P.chartN - 1) := by
    have hstep1 : (P.chartN : ℝ) * ((P.chartN : ℝ) + 1)
        ≤ ((P.chartN : ℝ) + 2) * (1 / Real.sqrt (2 * (2 + P.chartV)) * (5 / 8 + P.chartV / 3))
          * (1 + P.chartV) ^ (P.chartN - 1) := by
      rw [show ((P.chartN : ℝ) + 2) * (1 / Real.sqrt (2 * (2 + P.chartV)) * (5 / 8 + P.chartV / 3))
            * (1 + P.chartV) ^ (P.chartN - 1)
          = (((P.chartN : ℝ) + 2) * (5 / 8 + P.chartV / 3) * (1 + P.chartV) ^ (P.chartN - 1))
            / Real.sqrt (2 * (2 + P.chartV)) by field_simp,
        le_div_iff₀ hs]
      exact hTarget
    have h1vpow : (0 : ℝ) ≤ (1 + P.chartV) ^ (P.chartN - 1) := pow_nonneg (by linarith) _
    have hNfac : (0 : ℝ) ≤ (P.chartN : ℝ) + 2 := by positivity
    rw [show P.chartSigma ^ (P.chartN - 1) = (1 + P.chartV) ^ (P.chartN - 1) from by rw [hσ]]
    calc (P.chartN : ℝ) * ((P.chartN : ℝ) + 1)
        ≤ ((P.chartN : ℝ) + 2) * (1 / Real.sqrt (2 * (2 + P.chartV)) * (5 / 8 + P.chartV / 3))
          * (1 + P.chartV) ^ (P.chartN - 1) := hstep1
      _ ≤ ((P.chartN : ℝ) + 2) * (P.chartCxi * (P.chartSigma - P.ell)) * (1 + P.chartV) ^ (P.chartN - 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcs hNfac) h1vpow
      _ = ((P.chartN : ℝ) + 2) * P.chartCxi * (P.chartSigma - P.ell) * (1 + P.chartV) ^ (P.chartN - 1) := by
          ring
  -- assemble: `T_N < N(N+1)(1-ℓ) ≤ (N+2)cξ(1-ℓ)(σ-ℓ)σ^{N-1}`
  have hfinal : (P.chartN : ℝ) * ((P.chartN : ℝ) + 1) * (1 - P.ell)
      ≤ ((P.chartN : ℝ) + 2) * P.chartCxi * (1 - P.ell) * (P.chartSigma - P.ell) * P.chartSigma ^ (P.chartN - 1) := by
    have := mul_le_mul_of_nonneg_right hmain h1ℓ.le
    nlinarith [this]
  linarith [hTN, hfinal]

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
