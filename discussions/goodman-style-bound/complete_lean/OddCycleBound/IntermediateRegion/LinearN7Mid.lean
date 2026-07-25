import OddCycleBound.IntermediateRegion.LinearN7

/-!
# The `N = 7` corner of the linear branch — middle `v` (paper §9, `lem:N7-middle-v`, line 3433)

Under `N = 7`, `ζ ≤ 7`, `1/4 ≤ v ≤ 5/8`, `eq:linear-core` holds.  The paper proves the reduced
target `eq:middle-target`
`63/10·(1−y²)(1−y)(1+v−y)(1+v)⁶ ≥ 6+8v` (with `y² = 7v/(8+v)`) by a logarithmic-derivative
monotonicity argument that uses `lem:bernstein-Q10`.  We take a **derivative-free** route: isolate
the single square-root term `y` and square.  Because `y` occurs only through `y²`, multiplying the
whole target by `10(8+v)²` and substituting `(8+v)y² = 7v` collapses everything to
`BB(v)·y ≤ Plin(v)` with `BB, Plin` polynomials; squaring reduces `eq:middle-target` to two
rational polynomial inequalities on `[1/4,5/8]` (rational endpoints), each a Bernstein-positivity
certificate exactly as in `Bernstein.lean` / `LinearBroad.largev_base`.

The `ξ > 1/3` step (giving `φ ≥ 7/10`) reduces to `12α²(α−q) ≥ e²`, an LP Positivstellensatz
certificate over the admissible domain (with `ζ ≤ 7`, `1/4 ≤ v ≤ 5/8`), like `xi_small_v_raw`.
-/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

/-! ### The two Bernstein-positivity certificates on `[1/4,5/8]` (from `eq:middle-target`, squared) -/

/-- `Plin(v) ≥ 0` on `[1/4,5/8]`: the linear (rational) part of `eq:middle-target`,
`Plin = 63(8−6v)(1+v)⁶(8+16v+v²) − 10(6+8v)(8+v)²`.  Bernstein certificate on `[1/4,5/8]`. -/
theorem n7mid_Plin_nonneg {v : ℝ} (hlo : 1 / 4 ≤ v) (hhi : v ≤ 5 / 8) :
    0 ≤ 63 * (8 - 6 * v) * (1 + v) ^ 6 * (8 + 16 * v + v ^ 2) - 10 * (6 + 8 * v) * (8 + v) ^ 2 := by
  have ha : 0 ≤ 8 * v - 2 := by linarith
  have hb : 0 ≤ 5 - 8 * v := by linarith
  have term : ∀ (c : ℝ) (i j : ℕ), 0 ≤ c → 0 ≤ c * (8 * v - 2) ^ i * (5 - 8 * v) ^ j :=
    fun c i j hc => mul_nonneg (mul_nonneg hc (pow_nonneg ha i)) (pow_nonneg hb j)
  have key : (3 : ℝ) ^ 9 *
      (63 * (8 - 6 * v) * (1 + v) ^ 6 * (8 + 16 * v + v ^ 2) - 10 * (6 + 8 * v) * (8 + v) ^ 2) =
        (1756109835 / 131072) * (8 * v - 2) ^ 0 * (5 - 8 * v) ^ 9
      + (40660141095 / 262144) * (8 * v - 2) ^ 1 * (5 - 8 * v) ^ 8
      + (103060814895 / 131072) * (8 * v - 2) ^ 2 * (5 - 8 * v) ^ 7
      + (601677459855 / 262144) * (8 * v - 2) ^ 3 * (5 - 8 * v) ^ 6
      + (4463366559885 / 1048576) * (8 * v - 2) ^ 4 * (5 - 8 * v) ^ 5
      + (10914686688825 / 2097152) * (8 * v - 2) ^ 5 * (5 - 8 * v) ^ 4
      + (8800526635947 / 2097152) * (8 * v - 2) ^ 6 * (5 - 8 * v) ^ 3
      + (9022934196963 / 4194304) * (8 * v - 2) ^ 7 * (5 - 8 * v) ^ 2
      + (21336069758067 / 33554432) * (8 * v - 2) ^ 8 * (5 - 8 * v) ^ 1
      + (5535366403743 / 67108864) * (8 * v - 2) ^ 9 * (5 - 8 * v) ^ 0 := by ring
  have hsum : 0 ≤ (3 : ℝ) ^ 9 *
      (63 * (8 - 6 * v) * (1 + v) ^ 6 * (8 + 16 * v + v ^ 2) - 10 * (6 + 8 * v) * (8 + v) ^ 2) := by
    rw [key]
    linarith [term (1756109835 / 131072) 0 9 (by norm_num),
      term (40660141095 / 262144) 1 8 (by norm_num),
      term (103060814895 / 131072) 2 7 (by norm_num),
      term (601677459855 / 262144) 3 6 (by norm_num),
      term (4463366559885 / 1048576) 4 5 (by norm_num),
      term (10914686688825 / 2097152) 5 4 (by norm_num),
      term (8800526635947 / 2097152) 6 3 (by norm_num),
      term (9022934196963 / 4194304) 7 2 (by norm_num),
      term (21336069758067 / 33554432) 8 1 (by norm_num),
      term (5535366403743 / 67108864) 9 0 (by norm_num)]
  nlinarith [hsum]

set_option maxHeartbeats 800000 in
/-- `K(v) ≤ Plin(v)²` on `[1/4,5/8]`, where `K = 63²·7·v(8+v)(8−6v)²(1+v)¹²(2+v)²` is the squared
square-root part of `eq:middle-target`.  Bernstein certificate on `[1/4,5/8]` (degree 18). -/
theorem n7mid_Psq_nonneg {v : ℝ} (hlo : 1 / 4 ≤ v) (hhi : v ≤ 5 / 8) :
    63 ^ 2 * 7 * v * (8 + v) * (8 - 6 * v) ^ 2 * (1 + v) ^ 12 * (2 + v) ^ 2
      ≤ (63 * (8 - 6 * v) * (1 + v) ^ 6 * (8 + 16 * v + v ^ 2) - 10 * (6 + 8 * v) * (8 + v) ^ 2) ^ 2 := by
  have ha : 0 ≤ 8 * v - 2 := by linarith
  have hb : 0 ≤ 5 - 8 * v := by linarith
  have term : ∀ (c : ℝ) (i j : ℕ), 0 ≤ c → 0 ≤ c * (8 * v - 2) ^ i * (5 - 8 * v) ^ j :=
    fun c i j hc => mul_nonneg (mul_nonneg hc (pow_nonneg ha i)) (pow_nonneg hb j)
  have key : (3 : ℝ) ^ 18 *
      ((63 * (8 - 6 * v) * (1 + v) ^ 6 * (8 + 16 * v + v ^ 2) - 10 * (6 + 8 * v) * (8 + v) ^ 2) ^ 2
        - 63 ^ 2 * 7 * v * (8 + v) * (8 - 6 * v) ^ 2 * (1 + v) ^ 12 * (2 + v) ^ 2) =
        (9904104929558925 / 8589934592) * (8 * v - 2) ^ 0 * (5 - 8 * v) ^ 18
      + (791655569498623725 / 8589934592) * (8 * v - 2) ^ 1 * (5 - 8 * v) ^ 17
      + (55208710212890689125 / 34359738368) * (8 * v - 2) ^ 2 * (5 - 8 * v) ^ 16
      + (61588017889275938175 / 4294967296) * (8 * v - 2) ^ 3 * (5 - 8 * v) ^ 15
      + (2800137794654872236825 / 34359738368) * (8 * v - 2) ^ 4 * (5 - 8 * v) ^ 14
      + (11186360742541972120875 / 34359738368) * (8 * v - 2) ^ 5 * (5 - 8 * v) ^ 13
      + (132674590262406380594445 / 137438953472) * (8 * v - 2) ^ 6 * (5 - 8 * v) ^ 12
      + (150836625348458429046105 / 68719476736) * (8 * v - 2) ^ 7 * (5 - 8 * v) ^ 11
      + (4293185654813710006564875 / 1099511627776) * (8 * v - 2) ^ 8 * (5 - 8 * v) ^ 10
      + (6044568416884907918042535 / 1099511627776) * (8 * v - 2) ^ 9 * (5 - 8 * v) ^ 9
      + (27082010558820191751987435 / 4398046511104) * (8 * v - 2) ^ 10 * (5 - 8 * v) ^ 8
      + (6030359500640729532253785 / 1099511627776) * (8 * v - 2) ^ 11 * (5 - 8 * v) ^ 7
      + (33958776296437838245924461 / 8796093022208) * (8 * v - 2) ^ 12 * (5 - 8 * v) ^ 6
      + (18651492200659961355449643 / 8796093022208) * (8 * v - 2) ^ 13 * (5 - 8 * v) ^ 5
      + (31285906543601660491141689 / 35184372088832) * (8 * v - 2) ^ 14 * (5 - 8 * v) ^ 4
      + (4834026447633763067861631 / 17592186044416) * (8 * v - 2) ^ 15 * (5 - 8 * v) ^ 3
      + (33172364895613045016328261 / 562949953421312) * (8 * v - 2) ^ 16 * (5 - 8 * v) ^ 2
      + (4404341800047643158142701 / 562949953421312) * (8 * v - 2) ^ 17 * (5 - 8 * v) ^ 1
      + (1089485341562353580307117 / 2251799813685248) * (8 * v - 2) ^ 18 * (5 - 8 * v) ^ 0 := by
    ring
  have hsum : 0 ≤ (3 : ℝ) ^ 18 *
      ((63 * (8 - 6 * v) * (1 + v) ^ 6 * (8 + 16 * v + v ^ 2) - 10 * (6 + 8 * v) * (8 + v) ^ 2) ^ 2
        - 63 ^ 2 * 7 * v * (8 + v) * (8 - 6 * v) ^ 2 * (1 + v) ^ 12 * (2 + v) ^ 2) := by
    rw [key]
    linarith [term (9904104929558925 / 8589934592) 0 18 (by norm_num),
      term (791655569498623725 / 8589934592) 1 17 (by norm_num),
      term (55208710212890689125 / 34359738368) 2 16 (by norm_num),
      term (61588017889275938175 / 4294967296) 3 15 (by norm_num),
      term (2800137794654872236825 / 34359738368) 4 14 (by norm_num),
      term (11186360742541972120875 / 34359738368) 5 13 (by norm_num),
      term (132674590262406380594445 / 137438953472) 6 12 (by norm_num),
      term (150836625348458429046105 / 68719476736) 7 11 (by norm_num),
      term (4293185654813710006564875 / 1099511627776) 8 10 (by norm_num),
      term (6044568416884907918042535 / 1099511627776) 9 9 (by norm_num),
      term (27082010558820191751987435 / 4398046511104) 10 8 (by norm_num),
      term (6030359500640729532253785 / 1099511627776) 11 7 (by norm_num),
      term (33958776296437838245924461 / 8796093022208) 12 6 (by norm_num),
      term (18651492200659961355449643 / 8796093022208) 13 5 (by norm_num),
      term (31285906543601660491141689 / 35184372088832) 14 4 (by norm_num),
      term (4834026447633763067861631 / 17592186044416) 15 3 (by norm_num),
      term (33172364895613045016328261 / 562949953421312) 16 2 (by norm_num),
      term (4404341800047643158142701 / 562949953421312) 17 1 (by norm_num),
      term (1089485341562353580307117 / 2251799813685248) 18 0 (by norm_num)]
  nlinarith [hsum]

/-! ### The reduced target `eq:middle-target` (line 3477), derivative-free -/

set_option maxHeartbeats 400000 in
/-- **Paper `eq:middle-target` (line 3477):** `63/10·(1−y²)(1−y)(1+v−y)(1+v)⁶ ≥ 6+8v`, for
`y ≥ 0` with `(8+v)y² = 7v` and `1/4 ≤ v ≤ 5/8`.  Proved by isolating `y` and squaring, then the
two Bernstein certificates `n7mid_Plin_nonneg` / `n7mid_Psq_nonneg`. -/
theorem n7mid_middle_target {v y : ℝ} (hlo : 1 / 4 ≤ v) (hhi : v ≤ 5 / 8)
    (hy0 : 0 ≤ y) (hy2c : (8 + v) * y ^ 2 = 7 * v) :
    6 + 8 * v ≤ 63 / 10 * (1 - y ^ 2) * (1 - y) * (1 + v - y) * (1 + v) ^ 6 := by
  have hden : (0 : ℝ) < 8 + v := by linarith
  have hPlin := n7mid_Plin_nonneg hlo hhi
  have hPsq := n7mid_Psq_nonneg hlo hhi
  have hBB0 : 0 ≤ 63 * (8 + v) * (8 - 6 * v) * (1 + v) ^ 6 * (2 + v) := by
    have : 0 ≤ 8 - 6 * v := by linarith
    positivity
  -- `(BB·y)² ≤ Plin²`
  have hsq : (63 * (8 + v) * (8 - 6 * v) * (1 + v) ^ 6 * (2 + v) * y) ^ 2
      ≤ (63 * (8 - 6 * v) * (1 + v) ^ 6 * (8 + 16 * v + v ^ 2) - 10 * (6 + 8 * v) * (8 + v) ^ 2) ^ 2 := by
    have hcl : (63 * (8 + v) * (8 - 6 * v) * (1 + v) ^ 6 * (2 + v) * y) ^ 2 * (8 + v)
        = 7 * v * (63 * (8 + v) * (8 - 6 * v) * (1 + v) ^ 6 * (2 + v)) ^ 2 := by
      have e : (63 * (8 + v) * (8 - 6 * v) * (1 + v) ^ 6 * (2 + v) * y) ^ 2 * (8 + v)
          = (63 * (8 + v) * (8 - 6 * v) * (1 + v) ^ 6 * (2 + v)) ^ 2 * ((8 + v) * y ^ 2) := by ring
      rw [e, hy2c]; ring
    have hcl2 : (63 * (8 + v) * (8 - 6 * v) * (1 + v) ^ 6 * (2 + v) * y) ^ 2 * (8 + v)
        ≤ (63 * (8 - 6 * v) * (1 + v) ^ 6 * (8 + 16 * v + v ^ 2) - 10 * (6 + 8 * v) * (8 + v) ^ 2) ^ 2
          * (8 + v) := by
      rw [hcl]
      nlinarith [mul_le_mul_of_nonneg_right hPsq hden.le]
    exact le_of_mul_le_mul_right hcl2 hden
  -- `BB·y ≤ Plin`
  have hBBy : 63 * (8 + v) * (8 - 6 * v) * (1 + v) ^ 6 * (2 + v) * y
      ≤ 63 * (8 - 6 * v) * (1 + v) ^ 6 * (8 + 16 * v + v ^ 2) - 10 * (6 + 8 * v) * (8 + v) ^ 2 := by
    calc 63 * (8 + v) * (8 - 6 * v) * (1 + v) ^ 6 * (2 + v) * y
        = Real.sqrt ((63 * (8 + v) * (8 - 6 * v) * (1 + v) ^ 6 * (2 + v) * y) ^ 2) :=
          (Real.sqrt_sq (mul_nonneg hBB0 hy0)).symm
      _ ≤ Real.sqrt ((63 * (8 - 6 * v) * (1 + v) ^ 6 * (8 + 16 * v + v ^ 2)
            - 10 * (6 + 8 * v) * (8 + v) ^ 2) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 63 * (8 - 6 * v) * (1 + v) ^ 6 * (8 + 16 * v + v ^ 2) - 10 * (6 + 8 * v) * (8 + v) ^ 2 :=
          Real.sqrt_sq hPlin
  -- pull back to the target through the identity (needs `hy2c`)
  rw [← sub_nonneg]
  have hmul : (0 : ℝ) < 10 * (8 + v) ^ 2 := by positivity
  have hid : 10 * (8 + v) ^ 2 * (63 / 10 * (1 - y ^ 2) * (1 - y) * (1 + v - y) * (1 + v) ^ 6 - (6 + 8 * v))
      = (63 * (8 - 6 * v) * (1 + v) ^ 6 * (8 + 16 * v + v ^ 2) - 10 * (6 + 8 * v) * (8 + v) ^ 2)
        - 63 * (8 + v) * (8 - 6 * v) * (1 + v) ^ 6 * (2 + v) * y := by
    linear_combination (63 * v ^ 8 * y - 63 * v ^ 8 - 63 * v ^ 7 * y ^ 2 + 1008 * v ^ 7 * y
      - 1323 * v ^ 7 - 882 * v ^ 6 * y ^ 2 + 5733 * v ^ 6 * y - 6615 * v ^ 6 - 3969 * v ^ 5 * y ^ 2
      + 16758 * v ^ 5 * y - 15435 * v ^ 5 - 8820 * v ^ 4 * y ^ 2 + 28665 * v ^ 4 * y - 19845 * v ^ 4
      - 11025 * v ^ 3 * y ^ 2 + 29988 * v ^ 3 * y - 14553 * v ^ 3 - 7938 * v ^ 2 * y ^ 2
      + 18963 * v ^ 2 * y - 5733 * v ^ 2 - 3087 * v * y ^ 2 + 6678 * v * y - 945 * v - 504 * y ^ 2
      + 1008 * y) * hy2c
  have hfin : 0 ≤ 10 * (8 + v) ^ 2
      * (63 / 10 * (1 - y ^ 2) * (1 - y) * (1 + v - y) * (1 + v) ^ 6 - (6 + 8 * v)) := by
    rw [hid]; linarith [hBBy]
  exact (mul_nonneg_iff_of_pos_left hmul).mp hfin

/-! ### `ξ ≥ 1/3` (giving `φ ≥ 7/10`) -/

namespace AdmissibleParams

variable (P : AdmissibleParams)

/-- Paper `eq:varphi-7/10` raw form (line 3457): `12α²(α−q) ≥ e²`, from `ζ ≤ 7`, `1/4 ≤ v ≤ 5/8`.
An LP Positivstellensatz certificate over the admissible domain (like `xi_small_v_raw`). -/
theorem xi_ge_third_raw (hζ : P.chartZeta ≤ 7) (hv1 : 1 / 4 ≤ P.chartV) (hv2 : P.chartV ≤ 5 / 8) :
    P.e ^ 2 ≤ 12 * P.alpha ^ 2 * (P.alpha - P.q) := by
  have hα := P.alpha_pos
  have hd : 0 < P.alpha - P.q := sub_pos.mpr P.alpha_gt_q
  have hL2 := P.chartZeta_le_seven_iff hζ
  have hLsq : P.L ^ 2 = P.p * P.q - P.alpha ^ 2 := P.L_sq
  -- `z7 ≥ 0` (`ζ ≤ 7`)
  have hz7 : 0 ≤ 7 * P.alpha * (P.alpha - P.q) - ((1 - P.q) * P.q - P.alpha ^ 2) := by
    unfold p at hL2 hLsq; nlinarith [hL2, hLsq]
  -- `vlo ≥ 0` (`v ≥ 1/4`) and `vhi ≥ 0` (`v ≤ 5/8`)
  have hvV : P.chartV = (P.p - P.alpha) / P.alpha := by
    unfold chartV chartSigma; rw [sub_div, div_self hα.ne']
  have hvlo : 0 ≤ 4 - 4 * P.q - 5 * P.alpha := by
    rw [hvV, le_div_iff₀ hα] at hv1; unfold p at hv1; linarith
  have hvhi : 0 ≤ 13 * P.alpha - 8 + 8 * P.q := by
    rw [hvV, div_le_iff₀ hα] at hv2; unfold p at hv2; linarith
  unfold e
  nlinarith [hd, hz7, hvlo, hvhi, mul_nonneg hd.le hz7, mul_nonneg hz7 hvhi,
    mul_nonneg hvlo hvhi, mul_nonneg (mul_nonneg hd.le hd.le) hd.le,
    mul_nonneg (mul_nonneg hd.le hd.le) hvhi, mul_nonneg hd.le (mul_nonneg hvhi hvhi),
    mul_nonneg hvlo (mul_nonneg hvhi hvhi)]

/-- Paper `eq:varphi-7/10` (line 3457): `φ ≥ 7/10`, from `ξ ≥ 1/3`. -/
theorem phi_ge_seven_tenths (hζ : P.chartZeta ≤ 7) (hv1 : 1 / 4 ≤ P.chartV) (hv2 : P.chartV ≤ 5 / 8) :
    7 / 10 ≤ (1 + 4 * P.xi) / (2 + 4 * P.xi) := by
  have he : (0 : ℝ) < P.e ^ 2 := by have := P.e_pos; positivity
  have hden2 : (0 : ℝ) < 2 + 4 * P.xi := by linarith [P.xi_pos]
  have hξ3 : 1 / 3 ≤ P.xi := by
    have hraw := P.xi_ge_third_raw hζ hv1 hv2
    rw [xi, le_div_iff₀ he]
    unfold d
    nlinarith [hraw]
  rw [le_div_iff₀ hden2]; linarith [hξ3]

set_option maxHeartbeats 800000 in
/-- **Paper `lem:N7-middle-v` (line 3433):** `N = 7`, `ζ ≤ 7`, `1/4 ≤ v ≤ 5/8` ⟹ `eq:linear-core`. -/
theorem linear_N7_middle_v (hN7 : P.chartN = 7) (hζ : P.chartZeta ≤ 7)
    (hv1 : 1 / 4 ≤ P.chartV) (hv2 : P.chartV ≤ 5 / 8) :
    P.chartTN ≤ ((P.chartN : ℝ) + 2) * P.chartCxi * (1 - P.ell) * (P.chartSigma - P.ell)
      * P.chartSigma ^ (P.chartN - 1) := by
  have hvpos : 0 < P.chartV := P.chartV_pos
  have hσ : P.chartSigma = 1 + P.chartV := P.chartSigma_eq_one_add
  have hα := P.alpha_pos
  have hden : (0 : ℝ) < 8 + P.chartV := by linarith
  -- `y` with `y² = 7v/(8+v)`, and `ℓ ≤ y`
  set y : ℝ := Real.sqrt (7 * P.chartV / (8 + P.chartV)) with hydef
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hy2 : y ^ 2 = 7 * P.chartV / (8 + P.chartV) := Real.sq_sqrt (by positivity)
  have hy2c : (8 + P.chartV) * y ^ 2 = 7 * P.chartV := by
    rw [hy2]; field_simp
  -- `ℓ ≤ y`
  have hℓ2y2 : P.ell ^ 2 ≤ y ^ 2 := by
    have hzv := P.zeta_v_div_eq_ell_sq
    have hden' : 0 < P.chartZeta + 1 + P.chartV := by linarith [P.chartZeta_pos]
    rw [← hzv, hy2, div_le_div_iff₀ hden' hden]
    nlinarith [mul_nonneg (mul_nonneg (by linarith [hζ] : (0 : ℝ) ≤ 7 - P.chartZeta) hvpos.le)
      (by linarith [hvpos] : (0 : ℝ) ≤ 1 + P.chartV)]
  have hℓy : P.ell ≤ y := by
    have h := Real.sqrt_le_sqrt hℓ2y2
    rwa [Real.sqrt_sq P.ell_pos.le, Real.sqrt_sq hy0] at h
  -- `y < 1` and `1 + v − y > 0`
  have hy1 : y < 1 := by
    have : y ^ 2 < 1 := by rw [hy2, div_lt_one hden]; linarith
    nlinarith [hy0, this]
  have h1vy : 0 ≤ 1 + P.chartV - y := by linarith [hy1, hvpos]
  -- `√(2α) ≥ 1 − y²`
  have hsqrt2a : 1 - y ^ 2 ≤ Real.sqrt (2 * P.alpha) := by
    have h := P.sqrt_compensation
    have : 1 - y ^ 2 ≤ 1 - P.ell ^ 2 := by linarith [hℓ2y2]
    linarith [h, this]
  have h1y2 : (0 : ℝ) ≤ 1 - y ^ 2 := by nlinarith [hy1, hy0]
  -- `φ ≥ 7/10`
  have hφ := P.phi_ge_seven_tenths hζ hv1 hv2
  have hchartCxi : P.chartCxi = Real.sqrt (2 * P.alpha) * ((1 + 4 * P.xi) / (2 + 4 * P.xi)) := by
    unfold chartCxi; rw [mul_div_assoc]
  -- `c_ξ ≥ (7/10)(1 − y²)`
  have hcξ : 7 / 10 * (1 - y ^ 2) ≤ P.chartCxi := by
    rw [hchartCxi]
    calc 7 / 10 * (1 - y ^ 2) = (1 - y ^ 2) * (7 / 10) := by ring
      _ ≤ Real.sqrt (2 * P.alpha) * ((1 + 4 * P.xi) / (2 + 4 * P.xi)) :=
          mul_le_mul hsqrt2a hφ (by norm_num) (Real.sqrt_nonneg _)
  -- `T₇ ≤ 6 + 8v`
  have hζlow : 1 - P.chartV / 2 ≤ P.chartZeta := by
    nlinarith [P.zeta_domain, P.chartZeta_pos, hvpos]
  have hT7 : P.chartTN ≤ 6 + 8 * P.chartV := by
    set s := Real.sqrt P.chartV with hsdef
    have hs2 : s ^ 2 = P.chartV := Real.sq_sqrt hvpos.le
    have hs0 : 0 < s := Real.sqrt_pos.2 hvpos
    have hs58 : s ^ 2 ≤ 5 / 8 := by rw [hs2]; exact hv2
    have h := P.chartTN_le_one
    rw [hN7, ← hsdef] at h
    push_cast at h
    -- `v^{7/2} = s^7 ≤ v/2` on `[1/4,5/8]`
    have hs7 : s ^ 7 ≤ P.chartV / 2 := by
      have hsv2 : (s * P.chartV ^ 2) ^ 2 = P.chartV ^ 5 := by rw [mul_pow, hs2]; ring
      have hv5 : P.chartV ^ 5 ≤ (5 / 8 : ℝ) ^ 5 := by
        apply pow_le_pow_left₀ hvpos.le hv2
      have hsv2le : s * P.chartV ^ 2 ≤ 1 / 2 := by
        nlinarith [hsv2, hv5, mul_nonneg hs0.le (pow_nonneg hvpos.le 2)]
      have : s ^ 7 = s * P.chartV ^ 2 * P.chartV := by rw [show s ^ 7 = s * (s ^ 2) ^ 3 by ring, hs2]; ring
      rw [this]; nlinarith [hsv2le, hvpos, mul_nonneg hs0.le (pow_nonneg hvpos.le 2)]
    have hsvN : (0 : ℝ) ≤ 1 - s ^ 7 := by nlinarith [hs7, hvpos]
    nlinarith [h, mul_le_mul_of_nonneg_right hζlow hsvN, hs7, pow_nonneg hs0.le 7]
  -- reduce `eq:linear-core` to `eq:middle-target`
  have hℓ1 : P.ell < 1 := lt_of_le_of_lt hℓy hy1
  have hmid := n7mid_middle_target hv1 hv2 hy0 hy2c
  have hcξ0 : 0 ≤ P.chartCxi := P.chartCxi_pos.le
  -- monotone chain: `63/10·(1−y²)(1−y)(1+v−y)(1+v)⁶ ≤ 9·c_ξ(1−ℓ)(σ−ℓ)σ⁶`
  have hchain : 63 / 10 * (1 - y ^ 2) * (1 - y) * (1 + P.chartV - y) * (1 + P.chartV) ^ 6
      ≤ 9 * P.chartCxi * (1 - P.ell) * (P.chartSigma - P.ell) * P.chartSigma ^ 6 := by
    rw [hσ]
    have h1v6 : (0 : ℝ) ≤ (1 + P.chartV) ^ 6 := by positivity
    have hstep : 63 / 10 * (1 - y ^ 2) * (1 - y) * (1 + P.chartV - y)
        ≤ 9 * P.chartCxi * (1 - P.ell) * (1 + P.chartV - P.ell) := by
      have c1 : 63 / 10 * (1 - y ^ 2) ≤ 9 * P.chartCxi := by linarith [hcξ]
      have c2 : 63 / 10 * (1 - y ^ 2) * (1 - y) ≤ 9 * P.chartCxi * (1 - P.ell) :=
        mul_le_mul c1 (by linarith [hℓy]) (by linarith [hy1]) (by linarith [hcξ0])
      exact mul_le_mul c2 (by linarith [hℓy]) h1vy
        (mul_nonneg (mul_nonneg (by norm_num) hcξ0) (by linarith [hℓ1]))
    calc 63 / 10 * (1 - y ^ 2) * (1 - y) * (1 + P.chartV - y) * (1 + P.chartV) ^ 6
        = (63 / 10 * (1 - y ^ 2) * (1 - y) * (1 + P.chartV - y)) * (1 + P.chartV) ^ 6 := by ring
      _ ≤ (9 * P.chartCxi * (1 - P.ell) * (1 + P.chartV - P.ell)) * (1 + P.chartV) ^ 6 :=
          mul_le_mul_of_nonneg_right hstep h1v6
      _ = 9 * P.chartCxi * (1 - P.ell) * (1 + P.chartV - P.ell) * (1 + P.chartV) ^ 6 := by ring
  -- assemble
  have hgoal : P.chartTN ≤ 9 * P.chartCxi * (1 - P.ell) * (P.chartSigma - P.ell) * P.chartSigma ^ 6 :=
    le_trans hT7 (le_trans hmid hchain)
  rw [hN7]
  have hcast : ((7 : ℕ) : ℝ) + 2 = 9 := by norm_num
  rw [show (7 : ℕ) - 1 = 6 from rfl, hcast]
  exact hgoal

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
