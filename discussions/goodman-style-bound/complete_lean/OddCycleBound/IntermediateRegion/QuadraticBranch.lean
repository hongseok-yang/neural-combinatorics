import OddCycleBound.IntermediateRegion.Scalar.Chart
import Mathlib.Algebra.Ring.GeomSum

/-!
# The quadratic Huber branch (paper §8, `paper_new_region2_v2.tex` lines 2673–2792)

Assuming `2ρξ ≤ 1`, this file proves the scalar target `R_m ≤ C_m·ψ(ξ,ρ)` for every odd `N ≥ 7`
(`prop:quadratic-branch`, line 2733).  The reduction is:

* the quadratic dual witness (`psi_ge_dual_two_rho_xi`) gives `C·ψ ≥ C·ρ·ξ² = 2α³·A·κ²`;
* the finite quotient `K_A` satisfies `A ≥ m·α^N·K_A` and, by AM–GM on `eq:KA-sum`,
  `K_A ≥ (chartR)·v·σ^{chartR−1}`;
* the coefficient estimate `lem:quad-coeff` reduces to the polynomial inequality `3L²(p−α) > e²`;
* combining these, the defect `u·T_N` is dominated once `ζ·T_N ≤ (2/3)·m·chartR·σ^{chartR−1}`
  (`eq:E-N`/`eq:H-N`), which is checked by a case split on `N` and `v`.
-/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

open Finset in
/-- AM–GM in the form used by `eq:KA-AMGM` (line 2690): the geometric-mean bound
`Σ_{j<n} σ^{2j} ≥ n·σ^{n−1}`, proved by pairing `j ↔ n−1−j` (`sum_range_reflect`) and the
two-term inequality `2σ^{n−1} ≤ σ^{2j} + σ^{2(n−1−j)}`. -/
theorem sum_pow_two_mul_ge (σ : ℝ) (n : ℕ) :
    (n : ℝ) * σ ^ (n - 1) ≤ ∑ j ∈ Finset.range n, σ ^ (2 * j) := by
  have hpair : ∀ j ∈ Finset.range n,
      2 * σ ^ (n - 1) ≤ σ ^ (2 * j) + σ ^ (2 * (n - 1 - j)) := by
    intro j hj
    have hjlt : j < n := Finset.mem_range.mp hj
    have hsum : j + (n - 1 - j) = n - 1 := by omega
    have h1 : σ ^ j * σ ^ (n - 1 - j) = σ ^ (n - 1) := by rw [← pow_add, hsum]
    have hA : σ ^ (2 * j) = (σ ^ j) ^ 2 := by rw [pow_mul']
    have hB : σ ^ (2 * (n - 1 - j)) = (σ ^ (n - 1 - j)) ^ 2 := by rw [pow_mul']
    nlinarith [sq_nonneg (σ ^ j - σ ^ (n - 1 - j)), h1, hA, hB]
  have hreflect :
      (∑ j ∈ Finset.range n, σ ^ (2 * (n - 1 - j))) = ∑ j ∈ Finset.range n, σ ^ (2 * j) :=
    Finset.sum_range_reflect (fun j => σ ^ (2 * j)) n
  have hdouble :
      (∑ j ∈ Finset.range n, (σ ^ (2 * j) + σ ^ (2 * (n - 1 - j))))
        = 2 * ∑ j ∈ Finset.range n, σ ^ (2 * j) := by
    rw [Finset.sum_add_distrib, hreflect]; ring
  have hle :
      (∑ j ∈ Finset.range n, (2 * σ ^ (n - 1)))
        ≤ ∑ j ∈ Finset.range n, (σ ^ (2 * j) + σ ^ (2 * (n - 1 - j))) :=
    Finset.sum_le_sum hpair
  rw [hdouble, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
  linarith

namespace AdmissibleParams

variable (P : AdmissibleParams)

/-! ### The finite quotient `K_A` (paper eq:KA-sum, eq:KA-AMGM) -/

/-- Paper eq:KA-sum (line 2560): `K_A = v·Σ_{j<chartR} σ^{2j}` (geometric-series form, using
`σ^{N+1} − 1 = (σ² − 1)Σ σ^{2j}` and `(σ²−1)/(σ+1) = σ − 1 = v`). -/
theorem chartKA_eq_sum :
    P.chartKA = P.chartV * ∑ j ∈ Finset.range P.chartR, P.chartSigma ^ (2 * j) := by
  have hσ1 : (0 : ℝ) < P.chartSigma + 1 := by linarith [P.chartSigma_pos]
  have hgeom : (∑ j ∈ Finset.range P.chartR, (P.chartSigma ^ 2) ^ j) * (P.chartSigma ^ 2 - 1)
      = (P.chartSigma ^ 2) ^ P.chartR - 1 := geom_sum_mul _ _
  have hpow : (P.chartSigma ^ 2) ^ P.chartR = P.chartSigma ^ (P.chartN + 1) := by
    rw [← pow_mul, P.two_mul_chartR]
  have hpow2 : ∀ j, (P.chartSigma ^ 2) ^ j = P.chartSigma ^ (2 * j) := by
    intro j; rw [← pow_mul]
  unfold chartKA chartV
  rw [div_eq_iff hσ1.ne']
  have hgeom' : (∑ j ∈ Finset.range P.chartR, P.chartSigma ^ (2 * j)) * (P.chartSigma ^ 2 - 1)
      = P.chartSigma ^ (P.chartN + 1) - 1 := by
    rw [← hpow]; rw [← hgeom]; congr 1; apply Finset.sum_congr rfl; intro j _; rw [hpow2]
  nlinarith [hgeom']

/-- Paper eq:KA-AMGM (line 2690): `K_A ≥ chartR·v·σ^{chartR−1}`. -/
theorem chartKA_ge :
    (P.chartR : Real) * P.chartV * P.chartSigma ^ (P.chartR - 1) ≤ P.chartKA := by
  rw [P.chartKA_eq_sum]
  have hsum := sum_pow_two_mul_ge P.chartSigma P.chartR
  have hv : 0 ≤ P.chartV := P.chartV_pos.le
  nlinarith [mul_le_mul_of_nonneg_left hsum hv]

/-! ### `A ≥ m·α^N·K_A` (paper eq:KA-def, line 2549) -/

/-- Paper eq:KA-def (line 2549): `k_m(α) = α^N·K_A`. -/
theorem k_alpha_eq_chartKA : P.k P.alpha = P.alpha ^ P.chartN * P.chartKA := by
  have hm9 := P.m_ge_nine
  have hn1 : P.m - 1 = P.chartN + 1 := by unfold chartN; omega
  have hαpos := P.alpha_pos
  have hpα : (0 : ℝ) < P.p + P.alpha := add_pos P.p_pos P.alpha_pos
  have hαsucc : P.alpha ^ (P.chartN + 1) = P.alpha ^ P.chartN * P.alpha := pow_succ _ _
  have hσpow : P.chartSigma ^ (P.chartN + 1) = P.p ^ (P.chartN + 1) / P.alpha ^ (P.chartN + 1) := by
    unfold chartSigma; rw [div_pow]
  have hσadd : P.chartSigma + 1 = (P.p + P.alpha) / P.alpha := by
    unfold chartSigma; field_simp
  unfold k chartKA
  rw [hn1, hσpow, hσadd, hαsucc]
  field_simp

/-- `A ≥ m·α^N·K_A` (drop the nonnegative `2L^N` summand of `A`). -/
theorem A_ge_m_mul : (P.m : Real) * (P.alpha ^ P.chartN * P.chartKA) ≤ P.A := by
  unfold A
  rw [show P.m - 2 = P.chartN by unfold chartN; rfl, ← P.k_alpha_eq_chartKA]
  have : (0 : ℝ) ≤ 2 * P.L ^ P.chartN := by
    have := pow_nonneg P.L_nonneg P.chartN; linarith
  linarith

/-! ### The witness identity `C·ρ·ξ² = 2α³Aκ²` (paper eq:witness-quadratic, line 2366) -/

/-- Paper eq:witness-quadratic (line 2366): `C·ρ·ξ² = 2α³·A·κ²`. -/
theorem C_mul_rho_mul_xi_sq : P.C * P.rho * P.xi ^ 2 = 2 * P.alpha ^ 3 * P.A * P.kappa ^ 2 := by
  have hraSq : Real.sqrt P.alpha ^ 2 = P.alpha := Real.sq_sqrt P.alpha_nonneg
  have hrtPos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsEq : Real.sqrt (2 * P.alpha) = Real.sqrt 2 * Real.sqrt P.alpha :=
    Real.sqrt_mul (by norm_num) _
  have hroot : Real.sqrt (2 * P.alpha) * Real.sqrt P.alpha = Real.sqrt 2 * P.alpha := by
    rw [hsEq, show Real.sqrt 2 * Real.sqrt P.alpha * Real.sqrt P.alpha
        = Real.sqrt 2 * Real.sqrt P.alpha ^ 2 by ring, hraSq]
  have he : P.e ≠ 0 := P.e_pos.ne'
  have ha : P.alpha ≠ 0 := P.alpha_pos.ne'
  have hf : P.f ≠ 0 := P.f_pos.ne'
  have hB : P.B ≠ 0 := P.B_pos.ne'
  unfold C rho xi kappa
  field_simp
  linear_combination (4 * P.A * P.d ^ 2) * hroot

/-! ### Coefficient estimate (paper lem:quad-coeff, line 2703) -/

/-- Paper lem:quad-coeff reduced form: `3L²(p − α) > e²`.  Positivstellensatz certificate
`12(3L²(p−α) − e²) = 12·G·D + 4·D·T + 12·D·T² + S²·Q₃ + 4·S·P·Q₃ + 7·T²·Q₃`, where
`G = q−α²−qα ≥ 0`, `D = α−q`, `T = e = 1−2α`, `S = 1−2q`, `P = 1−q−α`, `Q₃ = 3q−1`. -/
theorem quad_coeff_raw : P.e ^ 2 < 3 * P.L ^ 2 * (P.p - P.alpha) := by
  have hLsq : P.L ^ 2 = P.p * P.q - P.alpha ^ 2 := P.L_sq
  have hp : P.p = 1 - P.q := rfl
  have hG : 0 ≤ P.q - P.alpha ^ 2 - P.q * P.alpha := by
    linarith [P.leading_eigenvalue_quadratic_nonpos]
  have hD : 0 < P.alpha - P.q := sub_pos.mpr P.alpha_gt_q
  have hT : 0 < 1 - 2 * P.alpha := by linarith [P.alpha_lt_half]
  have hS : 0 < 1 - 2 * P.q := by linarith [P.q_lt_half]
  have hQ3 : 0 < 3 * P.q - 1 := by linarith [P.q_gt_third]
  have hPa : 0 < 1 - P.q - P.alpha := by
    have := P.alpha_lt_half; have := P.q_lt_half; linarith
  have he : P.e = 1 - 2 * P.alpha := rfl
  rw [he, hLsq, hp]
  nlinarith [mul_nonneg hG hD.le, mul_pos hD hT, mul_nonneg (mul_nonneg hD.le hT.le) hT.le,
    mul_nonneg (mul_nonneg hS.le hS.le) hQ3.le, mul_nonneg (mul_nonneg hS.le hPa.le) hQ3.le,
    mul_nonneg (mul_nonneg hT.le hT.le) hQ3.le]

/-- The coefficient estimate in cleared chart form: `u < 3·ζ·(α·v·κ²)` (paper eq:M-lower). -/
theorem quad_coeff : P.chartU < 3 * P.chartZeta * (P.alpha * P.chartV * P.kappa ^ 2) := by
  have hraw := P.quad_coeff_raw
  have he2 : (0 : ℝ) < P.e ^ 2 := by have := P.e_pos; positivity
  have hgt : 1 < 3 * P.L ^ 2 * (P.p - P.alpha) / P.e ^ 2 := by
    rw [lt_div_iff₀ he2]; linarith [hraw]
  have hid : 3 * P.chartZeta * (P.alpha * P.chartV * P.kappa ^ 2)
      = (3 * P.L ^ 2 * (P.p - P.alpha) / P.e ^ 2) * P.chartU := by
    have hα := P.alpha_pos.ne'
    have he := P.e_pos.ne'
    have hd : P.alpha - P.q ≠ 0 := (sub_pos.mpr P.alpha_gt_q).ne'
    unfold chartZeta ell chartU tau chartV chartSigma kappa d p
    field_simp
  rw [hid]
  have hmul := mul_lt_mul_of_pos_right hgt P.chartU_pos
  linarith [hmul]

/-! ### The defect target `ζ·T_N ≤ (2/3)·m·chartR·σ^{chartR−1}` (paper eq:E-N/eq:H-N) -/

/-- Completing the square in `eq:T-bound-one`: `4(1−w)·ζ·T_N ≤ N²(1+v)²`, where `w = (√v)^N`. -/
theorem chartZeta_mul_chartTN_comp_sq :
    4 * (1 - (Real.sqrt P.chartV) ^ P.chartN) * P.chartZeta * P.chartTN
      ≤ (P.chartN : Real) ^ 2 * (1 + P.chartV) ^ 2 := by
  set w := (Real.sqrt P.chartV) ^ P.chartN with hw
  have hw1 : w < 1 := P.chartVsqrtN_lt_one
  have hfac : 0 ≤ 4 * (1 - w) * P.chartZeta :=
    mul_nonneg (by linarith) P.chartZeta_pos.le
  have hstep := mul_le_mul_of_nonneg_left P.chartTN_le_one hfac
  nlinarith [hstep, sq_nonneg ((P.chartN : Real) * (1 + P.chartV) - 2 * (1 - w) * P.chartZeta)]

/-- Shared cast facts for the defect target. -/
theorem chartSigma_eq_one_add (P : AdmissibleParams) : P.chartSigma = 1 + P.chartV := by
  unfold chartV chartSigma; ring

/-- Paper eq:E-N (line 2751), `N ≥ 9`, `v ≤ 3/5`. -/
theorem quad_target_E9 (_hT : 0 < P.chartTN) (hN9 : 9 ≤ P.chartN) (hv : P.chartV ≤ 3 / 5) :
    3 * P.chartZeta * P.chartTN
      ≤ 2 * (P.m : Real) * P.chartR * P.chartSigma ^ (P.chartR - 1) := by
  have hVpos : 0 < P.chartV := P.chartV_pos
  have h2R : 2 * P.chartR = P.chartN + 1 := P.two_mul_chartR
  have hNge9 : (9 : Real) ≤ (P.chartN : Real) := by exact_mod_cast hN9
  have hcast : (2 : Real) * (P.chartR : Real) = (P.chartN : Real) + 1 := by exact_mod_cast h2R
  have hmcast : (P.m : Real) = (P.chartN : Real) + 2 := by
    have : P.m = P.chartN + 2 := by have := P.m_ge_nine; unfold chartN; omega
    rw [this]; push_cast; ring
  have h2mr : 2 * ((P.m : Real) * (P.chartR : Real)) = ((P.chartN : Real) + 2) * ((P.chartN : Real) + 1) := by
    rw [hmcast]; nlinarith [hcast, hNge9]
  have hsqrt1 : Real.sqrt P.chartV ≤ 1 := by
    rw [show (1 : Real) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by linarith [P.chartV_lt_one])
  have hcomp := P.chartZeta_mul_chartTN_comp_sq
  rw [P.chartSigma_eq_one_add]
  set w := (Real.sqrt P.chartV) ^ P.chartN with hw
  have hw1 : w < 1 := P.chartVsqrtN_lt_one
  have h1w : (544 / 625 : Real) ≤ 1 - w := by
    have h1 : w ≤ (Real.sqrt P.chartV) ^ 8 :=
      pow_le_pow_of_le_one (Real.sqrt_nonneg _) hsqrt1 (by omega)
    have h2 : (Real.sqrt P.chartV) ^ 8 = P.chartV ^ 4 := by
      rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, Real.sq_sqrt P.chartV_pos.le]
    have h3 : P.chartV ^ 4 ≤ (3 / 5 : Real) ^ 4 := pow_le_pow_left₀ hVpos.le hv 4
    rw [h2] at h1; nlinarith [h1, h3]
  have hpoly8 : 3 * (P.chartN : Real) ^ 2 ≤ 8 * (1 - w) * ((P.m : Real) * (P.chartR : Real)) := by
    nlinarith [h2mr, h1w, hNge9, mul_nonneg (show (0:Real) ≤ 1 - w - 544/625 by linarith)
      (show (0:Real) ≤ ((P.chartN : Real) + 2) * ((P.chartN : Real) + 1) by nlinarith [hNge9])]
  have hpowge : (1 + P.chartV) ^ 2 ≤ (1 + P.chartV) ^ (P.chartR - 1) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have h4wpos : (0 : Real) < 4 * (1 - w) := by linarith
  apply le_of_mul_le_mul_left _ h4wpos
  have hprod1 := mul_le_mul_of_nonneg_right hpoly8 (sq_nonneg (1 + P.chartV))
  have hprod2 := mul_le_mul_of_nonneg_left hpowge
    (show (0:Real) ≤ 8 * (1 - w) * ((P.m : Real) * (P.chartR : Real)) by positivity)
  nlinarith [hcomp, hprod1, hprod2]

/-- Paper eq:H-N (line 2758), `N ≥ 9`, `v > 3/5`. -/
theorem quad_target_H9 (hT : 0 < P.chartTN) (hN9 : 9 ≤ P.chartN) (hv : 3 / 5 < P.chartV) :
    3 * P.chartZeta * P.chartTN
      ≤ 2 * (P.m : Real) * P.chartR * P.chartSigma ^ (P.chartR - 1) := by
  have hVpos : 0 < P.chartV := P.chartV_pos
  have h2R : 2 * P.chartR = P.chartN + 1 := P.two_mul_chartR
  have hNge9 : (9 : Real) ≤ (P.chartN : Real) := by exact_mod_cast hN9
  have hcast : (2 : Real) * (P.chartR : Real) = (P.chartN : Real) + 1 := by exact_mod_cast h2R
  have hmcast : (P.m : Real) = (P.chartN : Real) + 2 := by
    have : P.m = P.chartN + 2 := by have := P.m_ge_nine; unfold chartN; omega
    rw [this]; push_cast; ring
  have h2mr : 2 * (P.m : Real) * (P.chartR : Real) = ((P.chartN : Real) + 2) * ((P.chartN : Real) + 1) := by
    rw [hmcast]; nlinarith [hcast, hNge9]
  have h85 : (8 / 5 : Real) ≤ 1 + P.chartV := by linarith
  have hZT := P.chartZeta_mul_chartTN_lt hT
  rw [P.chartSigma_eq_one_add]
  have hpowsplit : (1 + P.chartV) ^ (P.chartR - 1) = (1 + P.chartV) * (1 + P.chartV) ^ (P.chartR - 2) := by
    rw [show P.chartR - 1 = (P.chartR - 2) + 1 by omega, pow_succ]; ring
  have hHpoly : 9 * (P.chartN : Real) ≤ 2 * ((P.chartN : Real) + 2) * (1 + P.chartV) ^ (P.chartR - 2) := by
    rcases Nat.lt_or_ge P.chartR 6 with hR5 | hR6
    · have hR5' : P.chartR = 5 := by omega
      have hN9' : P.chartN = 9 := by omega
      rw [hR5', show (P.chartN : Real) = 9 by rw [hN9']; norm_num]
      have hp3 : ((8:Real)/5) ^ 3 ≤ (1 + P.chartV) ^ 3 := pow_le_pow_left₀ (by norm_num) h85 3
      rw [show (5:ℕ) - 2 = 3 from rfl]
      nlinarith [hp3]
    · have hp4 : ((8:Real)/5) ^ 4 ≤ (1 + P.chartV) ^ (P.chartR - 2) := by
        calc ((8:Real)/5) ^ 4 ≤ ((8:Real)/5) ^ (P.chartR - 2) :=
              pow_le_pow_right₀ (by norm_num) (by omega)
          _ ≤ (1 + P.chartV) ^ (P.chartR - 2) := pow_le_pow_left₀ (by norm_num) h85 _
      have h92 : (9 : Real) / 2 ≤ (1 + P.chartV) ^ (P.chartR - 2) := by
        rw [show ((8:Real)/5)^4 = 4096/625 by norm_num] at hp4; linarith
      nlinarith [h92, hNge9]
  rw [hpowsplit, h2mr]
  have hkey : 9 * (P.chartN : Real) * ((P.chartN : Real) + 1) / 2 * (1 + P.chartV)
      ≤ ((P.chartN : Real) + 2) * ((P.chartN : Real) + 1)
          * ((1 + P.chartV) * (1 + P.chartV) ^ (P.chartR - 2)) := by
    have hfac : (0 : Real) ≤ ((P.chartN : Real) + 1) * (1 + P.chartV) := by nlinarith [hNge9]
    nlinarith [mul_le_mul_of_nonneg_left hHpoly hfac, hNge9]
  nlinarith [hZT, hkey]

/-- Paper `N = 7` corner of the quadratic branch (`v ≤ 9/10` uses `eq:E-N`, `v > 9/10` uses
`eq:H-N`). -/
theorem quad_target_seven (hT : 0 < P.chartTN) (hN7 : P.chartN = 7) :
    3 * P.chartZeta * P.chartTN
      ≤ 2 * (P.m : Real) * P.chartR * P.chartSigma ^ (P.chartR - 1) := by
  have hVpos : 0 < P.chartV := P.chartV_pos
  have hR4' : P.chartR = 4 := by
    have h2R : 2 * P.chartR = P.chartN + 1 := P.two_mul_chartR
    omega
  have hm9 : (P.m : Real) = 9 := by
    have : P.m = 9 := by unfold chartN at hN7; omega
    rw [this]; norm_num
  have hsqrt1 : Real.sqrt P.chartV ≤ 1 := by
    rw [show (1 : Real) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by linarith [P.chartV_lt_one])
  have hcomp := P.chartZeta_mul_chartTN_comp_sq
  rw [hN7] at hcomp
  rw [P.chartSigma_eq_one_add, hR4', hm9, show (4:ℕ) - 1 = 2 + 1 from rfl, pow_succ]
  set w := (Real.sqrt P.chartV) ^ 7 with hw
  have hw0 : (0 : Real) ≤ w := pow_nonneg (Real.sqrt_nonneg _) _
  have hcomp7 : 4 * (1 - w) * P.chartZeta * P.chartTN ≤ 7 ^ 2 * (1 + P.chartV) ^ 2 := by
    rw [hw]; exact hcomp
  have hw1 : w < 1 := by rw [hw, ← hN7]; exact P.chartVsqrtN_lt_one
  by_cases hv : P.chartV ≤ 9 / 10
  · -- E7
    have hwle : w ≤ P.chartV ^ 3 := by
      have h2 : w = P.chartV ^ 3 * Real.sqrt P.chartV := by
        rw [hw, show (7 : ℕ) = 2 * 3 + 1 by norm_num, pow_succ, pow_mul,
          Real.sq_sqrt P.chartV_pos.le]
      rw [h2]; nlinarith [pow_nonneg hVpos.le 3, hsqrt1, Real.sqrt_nonneg P.chartV]
    have hE7poly : (49 : Real) / 96 ≤ (1 - w) * (1 + P.chartV) := by
      have hpoly : (49 : Real) / 96 ≤ (1 - P.chartV ^ 3) * (1 + P.chartV) := by
        nlinarith [hv, hVpos, mul_nonneg hVpos.le (show (0:Real) ≤ 9/10 - P.chartV by linarith),
          mul_nonneg (mul_nonneg hVpos.le hVpos.le) (show (0:Real) ≤ 9/10 - P.chartV by linarith),
          mul_nonneg (mul_nonneg (mul_nonneg hVpos.le hVpos.le) hVpos.le)
            (show (0:Real) ≤ 9/10 - P.chartV by linarith)]
      have hmono : (1 - P.chartV ^ 3) * (1 + P.chartV) ≤ (1 - w) * (1 + P.chartV) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        linarith [hwle]
      linarith
    have h4wpos : (0 : Real) < 4 * (1 - w) := by linarith
    apply le_of_mul_le_mul_left _ h4wpos
    push_cast
    nlinarith [hcomp7, mul_le_mul_of_nonneg_right hE7poly (sq_nonneg (1 + P.chartV)), hVpos]
  · -- H7
    have hv : (9 : Real) / 10 < P.chartV := not_le.mp hv
    have hZT := P.chartZeta_mul_chartTN_lt hT
    rw [hN7] at hZT
    have hsq : (7 : Real) / 2 ≤ (1 + P.chartV) ^ 2 := by nlinarith [hv]
    push_cast at hZT ⊢
    nlinarith [hZT, mul_le_mul_of_nonneg_left hsq (show (0:Real) ≤ 72 * (1 + P.chartV) by nlinarith [hVpos]), hVpos]

/-- Paper eq:E-N/eq:H-N (lines 2751/2758): `3·ζ·T_N ≤ 2·m·chartR·σ^{chartR−1}`. -/
theorem quad_target (hT : 0 < P.chartTN) :
    3 * P.chartZeta * P.chartTN
      ≤ 2 * (P.m : Real) * P.chartR * P.chartSigma ^ (P.chartR - 1) := by
  by_cases hN9 : 9 ≤ P.chartN
  · by_cases hv : P.chartV ≤ 3 / 5
    · exact P.quad_target_E9 hT hN9 hv
    · exact P.quad_target_H9 hT hN9 (not_le.mp hv)
  · have h1 := P.two_mul_chartR
    have h2 : 7 ≤ P.chartN := by have := P.m_ge_nine; unfold chartN; omega
    exact P.quad_target_seven hT (by omega)

/-! ### Payment and the branch conclusion -/

/-- The payment inequality `u·T_N ≤ 2·m·chartR·(α·v·κ²)·σ^{chartR−1}` (paper eq:quad-payment-final,
line 2726), combining `quad_coeff` and `quad_target`. -/
theorem key_payment (hT : 0 < P.chartTN) :
    P.chartU * P.chartTN
      ≤ 2 * (P.m : Real) * P.chartR * (P.alpha * P.chartV * P.kappa ^ 2)
          * P.chartSigma ^ (P.chartR - 1) := by
  have hQT := P.quad_target hT
  have hqc := P.quad_coeff
  have hζ := P.chartZeta_pos
  have hu := P.chartU_pos.le
  have hM2pos : (0 : Real) < 2 * (P.m : Real) * P.chartR * P.chartSigma ^ (P.chartR - 1) := by
    have hmn : 0 < P.m := by have := P.m_ge_nine; omega
    have hm : (0 : Real) < (P.m : Real) := by exact_mod_cast hmn
    have hr : (0 : Real) < (P.chartR : Real) := by exact_mod_cast P.chartR_pos
    have hs : (0 : Real) < P.chartSigma ^ (P.chartR - 1) := pow_pos P.chartSigma_pos _
    positivity
  have h1 := mul_le_mul_of_nonneg_left hQT hu
  have h2 := mul_lt_mul_of_pos_right hqc hM2pos
  have h3 : 3 * P.chartZeta * (P.chartU * P.chartTN)
      < 3 * P.chartZeta * ((P.alpha * P.chartV * P.kappa ^ 2)
          * (2 * (P.m : Real) * P.chartR * P.chartSigma ^ (P.chartR - 1))) := by
    nlinarith [h1, h2]
  have h4 := lt_of_mul_lt_mul_left h3 (by positivity : (0 : Real) ≤ 3 * P.chartZeta)
  nlinarith [h4]

/-- **Paper prop:quadratic-branch (line 2733):** under `2ρξ ≤ 1`, the scalar target holds for
every odd `N ≥ 7`. -/
theorem quadratic_branch (hgate : 2 * P.rho * P.xi ≤ 1) : P.R ≤ P.C * psi P.xi P.rho := by
  by_cases hT : P.chartTN ≤ 0
  · exact P.scalar_target_of_chartTN_nonpos hT
  replace hT : 0 < P.chartTN := not_le.mp hT
  -- witness: C·ψ ≥ C·ρ·ξ² = 2α³Aκ²
  have hwit : P.rho * P.xi ^ 2 * (1 + 4 * P.xi) / (1 + 2 * P.xi) ≤ psi P.xi P.rho :=
    psi_ge_dual_two_rho_xi P.rho_pos P.xi_pos.le hgate
  have hxi := P.xi_pos
  have hfrac : P.rho * P.xi ^ 2 ≤ P.rho * P.xi ^ 2 * (1 + 4 * P.xi) / (1 + 2 * P.xi) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg P.rho_pos.le (sq_nonneg P.xi)) hxi.le]
  have hCwit : 2 * P.alpha ^ 3 * P.A * P.kappa ^ 2 ≤ P.C * psi P.xi P.rho := by
    rw [← P.C_mul_rho_mul_xi_sq]
    have : P.C * P.rho * P.xi ^ 2 ≤ P.C * psi P.xi P.rho :=
      le_trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (le_trans hfrac hwit) P.C_pos.le) (le_refl _)
    linarith [this]
  -- R ≤ 2α³Aκ²
  have hR := P.R_eq_alpha_pow_mul_chartFN
  have hFT := P.chartFN_le_chartU_mul_chartTN
  have hαm : (0 : Real) < P.alpha ^ P.m := pow_pos P.alpha_pos _
  have hR2 : P.R ≤ P.alpha ^ P.m * (P.chartU * P.chartTN) := by
    rw [hR]; exact mul_le_mul_of_nonneg_left hFT hαm.le
  have hkp := P.key_payment hT
  have hR3 : P.alpha ^ P.m * (P.chartU * P.chartTN)
      ≤ P.alpha ^ P.m * (2 * (P.m : Real) * P.chartR * (P.alpha * P.chartV * P.kappa ^ 2)
          * P.chartSigma ^ (P.chartR - 1)) := mul_le_mul_of_nonneg_left hkp hαm.le
  have hαpow : P.alpha ^ P.m * P.alpha = P.alpha ^ 3 * P.alpha ^ P.chartN := by
    rw [← pow_succ, show P.m + 1 = P.chartN + 3 by have := P.m_ge_nine; unfold chartN; omega,
      pow_add]; ring
  have hR4 : P.alpha ^ P.m * (2 * (P.m : Real) * P.chartR * (P.alpha * P.chartV * P.kappa ^ 2)
        * P.chartSigma ^ (P.chartR - 1)) ≤ 2 * P.alpha ^ 3 * P.A * P.kappa ^ 2 := by
    have hαpos := P.alpha_pos
    have hEq : P.alpha ^ P.m * (2 * (P.m : Real) * P.chartR * (P.alpha * P.chartV * P.kappa ^ 2)
          * P.chartSigma ^ (P.chartR - 1))
        = 2 * P.alpha ^ 3 * ((P.m : Real) * (P.alpha ^ P.chartN
            * ((P.chartR : Real) * P.chartV * P.chartSigma ^ (P.chartR - 1)))) * P.kappa ^ 2 := by
      rw [show P.alpha ^ P.m * (2 * (P.m : Real) * P.chartR * (P.alpha * P.chartV * P.kappa ^ 2)
            * P.chartSigma ^ (P.chartR - 1))
          = (P.alpha ^ P.m * P.alpha) * (2 * (P.m : Real) * P.chartR * P.chartV * P.kappa ^ 2
            * P.chartSigma ^ (P.chartR - 1)) by ring, hαpow]
      ring
    rw [hEq]
    have h1 : 2 * P.alpha ^ 3 * ((P.m : Real) * (P.alpha ^ P.chartN
          * ((P.chartR : Real) * P.chartV * P.chartSigma ^ (P.chartR - 1)))) * P.kappa ^ 2
        ≤ 2 * P.alpha ^ 3 * ((P.m : Real) * (P.alpha ^ P.chartN * P.chartKA)) * P.kappa ^ 2 := by
      gcongr
      exact P.chartKA_ge
    have h2 : 2 * P.alpha ^ 3 * ((P.m : Real) * (P.alpha ^ P.chartN * P.chartKA)) * P.kappa ^ 2
        ≤ 2 * P.alpha ^ 3 * P.A * P.kappa ^ 2 := by
      gcongr
      exact P.A_ge_m_mul
    linarith [h1, h2]
  linarith [hR2, hR3, hR4, hCwit]

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
