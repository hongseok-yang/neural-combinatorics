import OddCycleBound.IntermediateRegion.Scalar.ThreeGeometric
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The dimensionless chart (paper §7, `paper_new_region2_v2.tex` lines 2411–2521)

The scalar target `R ≤ C·ψ(ξ,ρ)` is proved in a dimensionless chart obtained by dividing every
quantity by the frontier eigenvalue `α`.  Following the paper (§7):

* `a = q/α` (`= P.tau`), `ℓ = L/α` (`= P.ell`), `u = 1 − a`, `σ = p/α`,
* `D = 1 + a² + ℓ²`, `ζ = ℓ²/u`, `v = σ − 1`, `N = m − 2`,
* `Hζ = ζ + 1 + v`, `Q = v² + vζ + 2v + 2ζ + 2`.

This file (increment 1) sets up the coordinates, their positivity, and the master algebraic
identities `eq:chart-inverse-1` (line 2430) — in cleared, denominator-free form
(`α²·D = q`, `q·D = a²`, `α·D = a`, `σ·a = 1 + ℓ²`).  The chart domain (`lem:chart-domain`, 2441),
the normalized defect `F_N`/`T_N`, the finite quotients `K_A`/`K_L`, and the three `T_N` bounds
(`lem:T-bounds`, 2571) are added in subsequent increments.
-/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar
namespace AdmissibleParams

variable (P : AdmissibleParams)

/-! ### Chart coordinates (paper eq:N-def 2414, eq:chart-basic 2418, eq:zeta-v-def 2472) -/

/-- Paper §7 `N = m − 2` (odd, `≥ 7` since `m ≥ 9`). -/
def chartN : Nat := P.m - 2

/-- Paper §7 `u = 1 − a = 1 − q/α`. -/
def chartU : Real := 1 - P.tau

/-- Paper §7 `σ = p/α`. -/
def chartSigma : Real := P.p / P.alpha

/-- Paper §7 `v = σ − 1`. -/
def chartV : Real := P.chartSigma - 1

/-- Paper §7 `ζ = ℓ²/u`. -/
def chartZeta : Real := P.ell ^ 2 / P.chartU

/-- Paper §7 `D = 1 + a² + ℓ²`. -/
def chartD : Real := 1 + P.tau ^ 2 + P.ell ^ 2

/-- Paper §7 `Hζ = ζ + 1 + v`. -/
def chartH : Real := P.chartZeta + 1 + P.chartV

/-- Paper §7 `Q = v² + vζ + 2v + 2ζ + 2` (eq:Q-chart 2500). -/
def chartQpoly : Real :=
  P.chartV ^ 2 + P.chartV * P.chartZeta + 2 * P.chartV + 2 * P.chartZeta + 2

/-! ### Elementary scaling identities -/

theorem alpha_mul_tau : P.alpha * P.tau = P.q := by
  unfold tau
  field_simp [P.alpha_pos.ne']

theorem alpha_mul_ell : P.alpha * P.ell = P.L := by
  unfold ell
  field_simp [P.alpha_pos.ne']

/-! ### Positivity of the chart coordinates -/

theorem tau_pos : 0 < P.tau := div_pos P.q_pos P.alpha_pos

theorem tau_lt_one : P.tau < 1 := (div_lt_one P.alpha_pos).2 P.alpha_gt_q

theorem chartU_pos : 0 < P.chartU := by
  unfold chartU; linarith [P.tau_lt_one]

theorem L_pos : 0 < P.L := by
  have hpos : 0 < P.p * P.q - P.alpha ^ 2 := by
    have hquad := P.leading_eigenvalue_quadratic_nonpos
    have hp : P.p = 1 - P.q := rfl
    nlinarith [P.q_pos, P.alpha_gt_q, mul_pos P.q_pos (sub_pos.mpr P.alpha_gt_q)]
  unfold L
  rwa [Real.sqrt_pos]

theorem ell_pos : 0 < P.ell := div_pos P.L_pos P.alpha_pos

theorem chartD_pos : 0 < P.chartD := by
  unfold chartD; positivity

theorem chartSigma_pos : 0 < P.chartSigma := div_pos P.p_pos P.alpha_pos

theorem chartSigma_gt_one : 1 < P.chartSigma :=
  (one_lt_div P.alpha_pos).2 P.alpha_lt_p

theorem chartV_pos : 0 < P.chartV := by
  unfold chartV; linarith [P.chartSigma_gt_one]

theorem chartZeta_pos : 0 < P.chartZeta :=
  div_pos (pow_pos P.ell_pos 2) P.chartU_pos

/-! ### Master identity `α²·D = q` and the cleared inverse relations (paper eq:chart-inverse-1) -/

/-- The master chart identity: `α²·D = q` (equivalent to `α = a/D`).  Everything in the inverse
relations follows from this and the `L` identity. -/
theorem chartD_mul_alpha_sq : P.alpha ^ 2 * P.chartD = P.q := by
  have ht2 : P.alpha ^ 2 * P.tau ^ 2 = P.q ^ 2 := by
    rw [← P.alpha_mul_tau]; ring
  have hl2 : P.alpha ^ 2 * P.ell ^ 2 = P.L ^ 2 := by
    rw [← P.alpha_mul_ell]; ring
  have hL : P.L ^ 2 = P.p * P.q - P.alpha ^ 2 := P.L_sq
  have hp : P.p = 1 - P.q := rfl
  unfold chartD
  linear_combination ht2 + hl2 + hL + P.q * hp

/-- `α·D = a` (paper `α = a/D`, cleared). -/
theorem alpha_mul_chartD : P.alpha * P.chartD = P.tau := by
  have hmaster := P.chartD_mul_alpha_sq
  have h1 : P.alpha * P.chartD * P.alpha = P.tau * P.alpha := by
    have e : P.alpha * P.chartD * P.alpha = P.alpha ^ 2 * P.chartD := by ring
    rw [e, hmaster, ← P.alpha_mul_tau]; ring
  exact mul_right_cancel₀ P.alpha_pos.ne' h1

/-- `q·D = a²` (paper `q = a²/D`, cleared). -/
theorem chartD_mul_q : P.q * P.chartD = P.tau ^ 2 := by
  have hmaster := P.chartD_mul_alpha_sq
  have htau2 : P.tau ^ 2 * P.alpha ^ 2 = P.q ^ 2 := by
    rw [← P.alpha_mul_tau]; ring
  have h1 : P.q * P.chartD * P.alpha ^ 2 = P.tau ^ 2 * P.alpha ^ 2 := by
    have e : P.q * P.chartD * P.alpha ^ 2 = P.q * (P.alpha ^ 2 * P.chartD) := by ring
    rw [e, hmaster, htau2]; ring
  exact mul_right_cancel₀ (pow_ne_zero 2 P.alpha_pos.ne') h1

/-- `σ·a = 1 + ℓ²` (paper `σ = (1 + ℓ²)/a`, cleared). -/
theorem chartSigma_mul_tau : P.chartSigma * P.tau = 1 + P.ell ^ 2 := by
  have hl2 : P.alpha ^ 2 * P.ell ^ 2 = P.L ^ 2 := by
    rw [← P.alpha_mul_ell]; ring
  have hL : P.L ^ 2 = P.p * P.q - P.alpha ^ 2 := P.L_sq
  have hst : P.chartSigma * P.alpha = P.p := by
    unfold chartSigma; field_simp [P.alpha_pos.ne']
  have hta : P.tau * P.alpha = P.q := by
    rw [mul_comm]; exact P.alpha_mul_tau
  have h1 : P.chartSigma * P.tau * P.alpha ^ 2 = (1 + P.ell ^ 2) * P.alpha ^ 2 := by
    have e : P.chartSigma * P.tau * P.alpha ^ 2
        = (P.chartSigma * P.alpha) * (P.tau * P.alpha) := by ring
    rw [e, hst, hta]
    linear_combination -hl2 - hL
  exact mul_right_cancel₀ (pow_ne_zero 2 P.alpha_pos.ne') h1

/-! ### The chart domain (paper `lem:chart-domain`, line 2441) -/

/-- `ℓ < a` (paper eq:chart-domain `0 < ℓ < a < 1`). -/
theorem ell_lt_tau : P.ell < P.tau := by
  unfold ell tau
  exact (div_lt_div_iff_of_pos_right P.alpha_pos).2 P.L_lt_q

/-- `D < 3a²` (paper eq:chart-domain; from `q = a²/D > 1/3`). -/
theorem chartD_lt_three_tau_sq : P.chartD < 3 * P.tau ^ 2 := by
  have hqD : P.q * P.chartD = P.tau ^ 2 := P.chartD_mul_q
  have hDpos := P.chartD_pos
  nlinarith [P.q_gt_third, hDpos, hqD,
    mul_pos hDpos (show (0:ℝ) < 3 * P.q - 1 by linarith [P.q_gt_third])]

/-- The frontier ceiling `a·u ≤ ℓ²` (paper eq:chart-domain `ℓ² ≥ a(1−a)`, from
`α² + qα − q ≤ 0`). -/
theorem tau_mul_chartU_le_ell_sq : P.tau * P.chartU ≤ P.ell ^ 2 := by
  have hquad := P.leading_eigenvalue_quadratic_nonpos
  have hl2 : P.alpha ^ 2 * P.ell ^ 2 = P.L ^ 2 := by rw [← P.alpha_mul_ell]; ring
  have hL : P.L ^ 2 = P.p * P.q - P.alpha ^ 2 := P.L_sq
  have hp : P.p = 1 - P.q := rfl
  have hau : P.alpha ^ 2 * (P.tau * P.chartU) = P.q * (P.alpha - P.q) := by
    unfold chartU
    have h1 : P.alpha ^ 2 * P.tau = P.alpha * P.q := by rw [← P.alpha_mul_tau]; ring
    have h2 : P.alpha ^ 2 * P.tau ^ 2 = P.q ^ 2 := by rw [← P.alpha_mul_tau]; ring
    linear_combination h1 - h2
  have hkey : P.alpha ^ 2 * (P.tau * P.chartU) ≤ P.alpha ^ 2 * P.ell ^ 2 := by
    rw [hau, hl2, hL, hp]; nlinarith [hquad]
  exact le_of_mul_le_mul_left hkey (pow_pos P.alpha_pos 2)

/-- `a > 3/4` (paper eq:chart-domain `a > (1+√13)/6 > 3/4`; from `1 + a ≤ D < 3a²`). -/
theorem tau_gt_three_quarters : 3 / 4 < P.tau := by
  have hDge : 1 + P.tau ≤ P.chartD := by
    have hu : P.chartU = 1 - P.tau := rfl
    have h := P.tau_mul_chartU_le_ell_sq
    rw [hu] at h
    unfold chartD
    nlinarith [h]
  have h3 : 1 + P.tau < 3 * P.tau ^ 2 := lt_of_le_of_lt hDge P.chartD_lt_three_tau_sq
  have ha23 : (2:ℝ) / 3 < P.tau := by
    show (2:ℝ) / 3 < P.q / P.alpha
    rw [lt_div_iff₀ P.alpha_pos]
    nlinarith [P.q_gt_third, P.alpha_lt_half]
  nlinarith [h3, ha23, P.tau_pos]

/-- `σ < 2` (paper eq:chart-domain `1 < σ < 2`; from `p < 2/3 < 2α`). -/
theorem chartSigma_lt_two : P.chartSigma < 2 := by
  show P.p / P.alpha < 2
  rw [div_lt_iff₀ P.alpha_pos]
  have hp : P.p < 2 / 3 := by have := P.q_gt_third; unfold p; linarith
  have hα : 1 / 3 < P.alpha := P.q_gt_third.trans P.alpha_gt_q
  linarith

/-- `v < 1` (paper eq:zeta-lower `0 < v < 1`). -/
theorem chartV_lt_one : P.chartV < 1 := by
  unfold chartV; linarith [P.chartSigma_lt_two]

/-! ### The `ζ`–`v` inverse relations (paper eq:zeta-v-inverse, line 2478) -/

/-- `ζ·u = ℓ²` (definition of `ζ`, cleared). -/
theorem chartZeta_mul_chartU : P.chartZeta * P.chartU = P.ell ^ 2 := by
  unfold chartZeta
  field_simp [P.chartU_pos.ne']

/-- `a·Hζ = 1 + ζ` (paper `a = (ζ+1)/Hζ`, cleared). -/
theorem tau_mul_chartH : P.tau * P.chartH = 1 + P.chartZeta := by
  have hA : P.tau * P.chartV + P.tau = 1 + P.ell ^ 2 := by
    have h := P.chartSigma_mul_tau
    have hv : P.chartSigma = P.chartV + 1 := by unfold chartV; ring
    rw [hv] at h
    linear_combination h
  have hB : P.chartZeta - P.chartZeta * P.tau = P.ell ^ 2 := by
    have h := P.chartZeta_mul_chartU
    have hu : P.chartU = 1 - P.tau := rfl
    rw [hu] at h
    linear_combination h
  unfold chartH
  linear_combination hA - hB

/-- `u·Hζ = v` (paper `u = v/Hζ`, cleared). -/
theorem chartU_mul_chartH : P.chartU * P.chartH = P.chartV := by
  have ha := P.tau_mul_chartH
  have hu : P.chartU = 1 - P.tau := rfl
  unfold chartH at ha ⊢
  rw [hu]
  linear_combination -ha

theorem chartH_pos : 0 < P.chartH := by
  unfold chartH; linarith [P.chartZeta_pos, P.chartV_pos]

/-! ### The core chart identities (paper eq:D-Q 2504, eq:H-identity 2512, eq:zeta-domain 2486) -/

/-- The `H`-identity (paper eq:H-identity, 2512): a pure polynomial identity in `ζ, v`. -/
theorem chartH_identity :
    P.chartZeta * P.chartH ^ 2 - (P.chartZeta + 1) * (P.chartZeta + P.chartV) ^ 2
      = P.chartZeta ^ 2 + P.chartZeta - P.chartV ^ 2 := by
  unfold chartH; ring

/-- `D·Hζ² = (ζ+1)·Q` (paper eq:D-Q, 2504, cleared). -/
theorem chartD_mul_chartH_sq :
    P.chartD * P.chartH ^ 2 = (P.chartZeta + 1) * P.chartQpoly := by
  have haH := P.tau_mul_chartH
  have huH := P.chartU_mul_chartH
  have hell := P.chartZeta_mul_chartU
  have e1 : P.chartD * P.chartH ^ 2
      = P.chartH ^ 2 + (P.tau * P.chartH) ^ 2 + (P.chartZeta * P.chartU) * P.chartH ^ 2 := by
    unfold chartD
    rw [← hell]; ring
  have e2 : (P.chartZeta * P.chartU) * P.chartH ^ 2
      = P.chartZeta * (P.chartU * P.chartH) * P.chartH := by ring
  rw [e1, e2, haH, huH]
  unfold chartH chartQpoly
  ring

/-- The frontier ceiling in chart form: `ζ(ζ+v) ≥ 1` (paper eq:zeta-domain, 2486). -/
theorem zeta_domain : 1 ≤ P.chartZeta * (P.chartZeta + P.chartV) := by
  have hceil := P.tau_mul_chartU_le_ell_sq
  have hell := P.chartZeta_mul_chartU
  have haH := P.tau_mul_chartH
  have huH := P.chartU_mul_chartH
  have hvpos := P.chartV_pos
  have step1 : (1 + P.chartZeta) * P.chartV
      ≤ P.chartZeta * P.chartV * P.chartH := by
    have hmul : (P.tau * P.chartU) * P.chartH ^ 2 ≤ P.ell ^ 2 * P.chartH ^ 2 :=
      mul_le_mul_of_nonneg_right hceil (sq_nonneg _)
    have eL : (P.tau * P.chartU) * P.chartH ^ 2
        = (P.tau * P.chartH) * (P.chartU * P.chartH) := by ring
    have eR : P.ell ^ 2 * P.chartH ^ 2
        = P.chartZeta * (P.chartU * P.chartH) * P.chartH := by
      rw [← hell]; ring
    rw [eL, eR, haH, huH] at hmul
    exact hmul
  have step2 : 1 + P.chartZeta ≤ P.chartZeta * P.chartH := by
    have h : (1 + P.chartZeta) * P.chartV ≤ (P.chartZeta * P.chartH) * P.chartV := by
      have e : P.chartZeta * P.chartV * P.chartH = (P.chartZeta * P.chartH) * P.chartV := by ring
      rw [← e]; exact step1
    exact le_of_mul_le_mul_right h hvpos
  unfold chartH at step2
  nlinarith [step2]

/-- `Q < 3(ζ+1)` (paper eq:Q-upper, 2508; from `D < 3a²`). -/
theorem chartQpoly_lt : P.chartQpoly < 3 * (P.chartZeta + 1) := by
  have hDQ := P.chartD_mul_chartH_sq
  have haH := P.tau_mul_chartH
  have hDlt := P.chartD_lt_three_tau_sq
  have hHpos := P.chartH_pos
  have h1 : P.chartD * P.chartH ^ 2 < 3 * P.tau ^ 2 * P.chartH ^ 2 :=
    mul_lt_mul_of_pos_right hDlt (pow_pos hHpos 2)
  have e : 3 * P.tau ^ 2 * P.chartH ^ 2 = 3 * (P.tau * P.chartH) ^ 2 := by ring
  rw [hDQ, e, haH] at h1
  have hz1 : 0 < P.chartZeta + 1 := by linarith [P.chartZeta_pos]
  have e2 : (3:ℝ) * (1 + P.chartZeta) ^ 2 = (P.chartZeta + 1) * (3 * (P.chartZeta + 1)) := by ring
  rw [e2] at h1
  exact lt_of_mul_lt_mul_left h1 hz1.le

/-- The positivity behind eq:H-identity: `ζ² + ζ − v² > 0` (paper 2516, `= (1−v)(1+v+ζ)` via
the `ζ`-domain). -/
theorem chartH_identity_pos : 0 < P.chartZeta ^ 2 + P.chartZeta - P.chartV ^ 2 := by
  have hzd := P.zeta_domain
  nlinarith [hzd,
    mul_pos (show (0:ℝ) < 1 - P.chartV by linarith [P.chartV_lt_one])
      (show (0:ℝ) < 1 + P.chartV + P.chartZeta by linarith [P.chartV_pos, P.chartZeta_pos])]

/-! ### The normalized defect and finite quotients (paper §7.1, lines 2523–2567) -/

/-- Paper eq:F-def (2526): the normalized defect `F_N = R/α^m = 1 − a^N − ℓ²(a^N − ℓ^N)`. -/
def chartFN : Real :=
  1 - P.tau ^ P.chartN - P.ell ^ 2 * (P.tau ^ P.chartN - P.ell ^ P.chartN)

/-- Paper eq:T-def (2531): `T_N = N − ζ(a^N − ℓ^N)`. -/
def chartTN : Real :=
  (P.chartN : Real) - P.chartZeta * (P.tau ^ P.chartN - P.ell ^ P.chartN)

/-- Paper eq:KA-def (2549): `K_A = (σ^{N+1} − 1)/(σ + 1)`. -/
def chartKA : Real := (P.chartSigma ^ (P.chartN + 1) - 1) / (P.chartSigma + 1)

/-- Paper eq:KL-def (2552): `K_L = (σ^{N+1} − ℓ^{N+1})/(σ + ℓ)`. -/
def chartKL : Real :=
  (P.chartSigma ^ (P.chartN + 1) - P.ell ^ (P.chartN + 1)) / (P.chartSigma + P.ell)

/-- The central reduction bridge: `R = α^m · F_N` (paper eq:F-def, cleared of the division). -/
theorem R_eq_alpha_pow_mul_chartFN : P.R = P.alpha ^ P.m * P.chartFN := by
  have hm9 : 9 ≤ P.m := P.m_ge_nine
  have hN2 : P.chartN + 2 = P.m := by unfold chartN; omega
  have hatN : P.alpha ^ P.chartN * P.tau ^ P.chartN = P.q ^ P.chartN := by
    rw [← mul_pow, P.alpha_mul_tau]
  have haeN : P.alpha ^ P.chartN * P.ell ^ P.chartN = P.L ^ P.chartN := by
    rw [← mul_pow, P.alpha_mul_ell]
  have hae2 : P.alpha ^ 2 * P.ell ^ 2 = P.L ^ 2 := by
    rw [← mul_pow, P.alpha_mul_ell]
  have hmsplit : P.alpha ^ P.m = P.alpha ^ P.chartN * P.alpha ^ 2 := by
    rw [← pow_add, hN2]
  have hLmsplit : P.L ^ P.m = P.L ^ P.chartN * P.L ^ 2 := by
    rw [← pow_add, hN2]
  have hqsplit : P.q ^ (P.m - 1) = P.q ^ P.chartN * P.q := by
    rw [← pow_succ, show P.chartN + 1 = P.m - 1 by unfold chartN; omega]
  have hL : P.L ^ 2 = P.p * P.q - P.alpha ^ 2 := P.L_sq
  unfold chartFN R
  rw [hmsplit, hLmsplit, hqsplit]
  linear_combination (P.alpha ^ 2 + P.alpha ^ 2 * P.ell ^ 2) * hatN
    - (P.alpha ^ 2 * P.ell ^ 2) * haeN
    + (P.q ^ P.chartN - P.L ^ P.chartN) * hae2
    + P.q ^ P.chartN * hL

/-- Paper eq:F-T (2535): `F_N ≤ u·T_N` (the `ℓ²` terms cancel; Bernoulli `1 − a^N ≤ Nu`). -/
theorem chartFN_le_chartU_mul_chartTN : P.chartFN ≤ P.chartU * P.chartTN := by
  have hζu : P.chartZeta * P.chartU = P.ell ^ 2 := P.chartZeta_mul_chartU
  have hbern : 1 - (P.chartN : Real) * P.chartU ≤ P.tau ^ P.chartN := by
    have h := one_add_mul_le_pow
      (show (-2:ℝ) ≤ -P.chartU by unfold chartU; linarith [P.tau_pos]) P.chartN
    have heq : (1 + -P.chartU) ^ P.chartN = P.tau ^ P.chartN := by
      congr 1; unfold chartU; ring
    rw [heq] at h
    linarith [h]
  have hrhs : P.chartU * P.chartTN
      = (P.chartN : Real) * P.chartU
        - P.ell ^ 2 * (P.tau ^ P.chartN - P.ell ^ P.chartN) := by
    unfold chartTN
    have huζ : P.chartU * P.chartZeta = P.ell ^ 2 := by rw [mul_comm]; exact hζu
    linear_combination -(P.tau ^ P.chartN - P.ell ^ P.chartN) * huζ
  rw [hrhs]
  unfold chartFN
  linarith [hbern]

/-- Reduction gate (paper eq:T-positive, 2538): if `T_N ≤ 0` then `R ≤ 0 ≤ C·ψ`. -/
theorem scalar_target_of_chartTN_nonpos (h : P.chartTN ≤ 0) :
    P.R ≤ P.C * psi P.xi P.rho := by
  have hR : P.R ≤ 0 := by
    rw [P.R_eq_alpha_pow_mul_chartFN]
    have hFN : P.chartFN ≤ 0 :=
      le_trans P.chartFN_le_chartU_mul_chartTN
        (mul_nonpos_of_nonneg_of_nonpos P.chartU_pos.le h)
    exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg P.alpha_pos.le _) hFN
  have hpsi : 0 ≤ P.C * psi P.xi P.rho :=
    mul_nonneg P.C_pos.le (psi_nonneg P.rho_pos.le)
  linarith

/-! ### `T_N` bound two (paper eq:T-bound-two, 2576) -/

theorem chartN_pos_real : (0:ℝ) < (P.chartN : Real) := by
  have : 0 < P.chartN := by have := P.m_ge_nine; unfold chartN; omega
  exact_mod_cast this

/-- Convexity of `x ↦ x^N`: `N·ℓ^{N-1}·(a − ℓ) ≤ a^N − ℓ^N` (via Bernoulli in `a/ℓ`). -/
theorem tau_pow_sub_ell_pow_ge :
    (P.chartN : Real) * P.ell ^ (P.chartN - 1) * (P.tau - P.ell)
      ≤ P.tau ^ P.chartN - P.ell ^ P.chartN := by
  have hℓ := P.ell_pos
  have hℓa := P.ell_lt_tau
  have hN1 : P.chartN - 1 + 1 = P.chartN := by have := P.m_ge_nine; unfold chartN; omega
  have hbern := one_add_mul_le_pow
    (show (-2:ℝ) ≤ P.tau / P.ell - 1 by
      have : (1:ℝ) ≤ P.tau / P.ell := (one_le_div hℓ).2 hℓa.le
      linarith) P.chartN
  have e1 : (1 + (P.tau / P.ell - 1)) ^ P.chartN = P.tau ^ P.chartN / P.ell ^ P.chartN := by
    rw [show (1:ℝ) + (P.tau / P.ell - 1) = P.tau / P.ell by ring, div_pow]
  rw [e1] at hbern
  have hℓN : (0:ℝ) < P.ell ^ P.chartN := pow_pos hℓ _
  rw [le_div_iff₀ hℓN] at hbern
  have hℓsplit : P.ell ^ (P.chartN - 1) * P.ell = P.ell ^ P.chartN := by
    rw [← pow_succ, hN1]
  have e2 : (1 + (P.chartN : Real) * (P.tau / P.ell - 1)) * P.ell ^ P.chartN
      = P.ell ^ P.chartN
        + (P.chartN : Real) * P.ell ^ (P.chartN - 1) * (P.tau - P.ell) := by
    rw [← hℓsplit]
    field_simp
  rw [e2] at hbern
  linarith [hbern]

/-- `a − ℓ > u` (paper 2606; from `D < 3a²` ⟹ `ℓ < 2a−1`). -/
theorem tau_sub_ell_gt_chartU : P.chartU < P.tau - P.ell := by
  have hDlt := P.chartD_lt_three_tau_sq
  have hDeq : P.chartD = 1 + P.tau ^ 2 + P.ell ^ 2 := rfl
  have hell2 : P.ell ^ 2 < 2 * P.tau ^ 2 - 1 := by rw [hDeq] at hDlt; linarith
  have hlt : P.ell ^ 2 < (2 * P.tau - 1) ^ 2 := by nlinarith [sq_nonneg (P.tau - 1)]
  have h2a1 : 0 < 2 * P.tau - 1 := by linarith [P.tau_gt_three_quarters]
  have hell_lt : P.ell < 2 * P.tau - 1 := by
    by_contra hcon
    have hge : 2 * P.tau - 1 ≤ P.ell := not_lt.mp hcon
    nlinarith [hlt, hge, h2a1, P.ell_pos]
  unfold chartU
  linarith [hell_lt]

/-- Paper eq:T-bound-two (2576): `T_N < N(1 − ℓ^{N+1})`. -/
theorem chartTN_lt : P.chartTN < (P.chartN : Real) * (1 - P.ell ^ (P.chartN + 1)) := by
  have hconv := P.tau_pow_sub_ell_pow_ge
  have hstep1 := P.tau_sub_ell_gt_chartU
  have hζpos := P.chartZeta_pos
  have hζu : P.chartZeta * P.chartU = P.ell ^ 2 := P.chartZeta_mul_chartU
  have hℓpos := P.ell_pos
  have hNpos := P.chartN_pos_real
  have hNℓpos : (0:ℝ) < (P.chartN : Real) * P.ell ^ (P.chartN - 1) :=
    mul_pos hNpos (pow_pos hℓpos _)
  have hℓexp : P.ell ^ (P.chartN - 1) * P.ell ^ 2 = P.ell ^ (P.chartN + 1) := by
    rw [← pow_add]; congr 1; have := P.m_ge_nine; unfold chartN; omega
  have h1 : P.chartZeta * ((P.chartN : Real) * P.ell ^ (P.chartN - 1) * (P.tau - P.ell))
      ≤ P.chartZeta * (P.tau ^ P.chartN - P.ell ^ P.chartN) :=
    mul_le_mul_of_nonneg_left hconv hζpos.le
  have h2 : P.chartZeta * ((P.chartN : Real) * P.ell ^ (P.chartN - 1) * P.chartU)
      < P.chartZeta * ((P.chartN : Real) * P.ell ^ (P.chartN - 1) * (P.tau - P.ell)) :=
    mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hstep1 hNℓpos) hζpos
  have h3 : P.chartZeta * ((P.chartN : Real) * P.ell ^ (P.chartN - 1) * P.chartU)
      = (P.chartN : Real) * P.ell ^ (P.chartN + 1) := by
    calc P.chartZeta * ((P.chartN : Real) * P.ell ^ (P.chartN - 1) * P.chartU)
        = (P.chartN : Real) * P.ell ^ (P.chartN - 1) * (P.chartZeta * P.chartU) := by ring
      _ = (P.chartN : Real) * P.ell ^ (P.chartN - 1) * P.ell ^ 2 := by rw [hζu]
      _ = (P.chartN : Real) * P.ell ^ (P.chartN + 1) := by rw [mul_assoc, hℓexp]
  have hkey : (P.chartN : Real) * P.ell ^ (P.chartN + 1)
      < P.chartZeta * (P.tau ^ P.chartN - P.ell ^ P.chartN) := by
    rw [← h3]; exact lt_of_lt_of_le h2 h1
  unfold chartTN
  nlinarith [hkey]

/-! ### `T_N` bound one (paper eq:T-bound-one, 2574)

The paper's real exponent `v^{N/2}` (with `N` odd) is represented here as `(√v)^N` — a Nat power of
`Real.sqrt v` — since `(v^{1/2})^N = v^{N/2}`; this avoids `Real.rpow`. -/

/-- `ℓ² < v` (paper 2590; `ℓ² = ζu`, `v = uHζ`, `ζ < Hζ`). -/
theorem ell_sq_lt_chartV : P.ell ^ 2 < P.chartV := by
  have h1 : P.ell ^ 2 = P.chartZeta * P.chartU := (P.chartZeta_mul_chartU).symm
  have h2 : P.chartV = P.chartU * P.chartH := (P.chartU_mul_chartH).symm
  rw [h1, h2]; unfold chartH
  nlinarith [mul_pos P.chartU_pos (show (0:ℝ) < 1 + P.chartV by linarith [P.chartV_pos])]

/-- Paper eq:T-bound-one (2574): `T_N ≤ N(1+v) − ζ(1 − (√v)^N)`. -/
theorem chartTN_le_one :
    P.chartTN ≤ (P.chartN : Real) * (1 + P.chartV)
      - P.chartZeta * (1 - (Real.sqrt P.chartV) ^ P.chartN) := by
  have hζpos := P.chartZeta_pos
  have hNpos := P.chartN_pos_real
  have hℓ2v := P.ell_sq_lt_chartV
  have hℓsqrt : P.ell < Real.sqrt P.chartV := by
    have h := Real.sqrt_lt_sqrt (sq_nonneg P.ell) hℓ2v
    rwa [Real.sqrt_sq P.ell_pos.le] at h
  have hℓN : P.ell ^ P.chartN < (Real.sqrt P.chartV) ^ P.chartN :=
    pow_lt_pow_left₀ hℓsqrt P.ell_pos.le
      (by have := P.m_ge_nine; unfold chartN; omega)
  have hbern : 1 - (P.chartN : Real) * P.chartU ≤ P.tau ^ P.chartN := by
    have h := one_add_mul_le_pow
      (show (-2:ℝ) ≤ -P.chartU by unfold chartU; linarith [P.tau_pos]) P.chartN
    have heq : (1 + -P.chartU) ^ P.chartN = P.tau ^ P.chartN := by
      congr 1; unfold chartU; ring
    rw [heq] at h; linarith [h]
  have hζuv : P.chartZeta * P.chartU < P.chartV := by
    rw [P.chartZeta_mul_chartU]; exact hℓ2v
  unfold chartTN
  nlinarith [mul_le_mul_of_nonneg_left hbern hζpos.le,
    mul_lt_mul_of_pos_left hℓN hζpos,
    mul_lt_mul_of_pos_left hζuv hNpos]

/-! ### `T_N` tangent bound (paper eq:T-tangent-bound, 2580) — scaffolding

The chain is `ζT_N < N·g(ζ) < N·g(Z) = N²(1+v)/(1−η)·(1−f(η)) ≤ (3N(N+1)/2)(1+v)`, with
`g(t)=t(1−(tv/(t+1+v))^r)`, `r=(N+1)/2` (a Nat since `N` is odd), `Z=N(1+v)/(1−η)`, `η=(√v)^N`. -/

/-- AM–GM in disguise (`r` copies of `1−b`, one of `1+rb`, arithmetic mean `1`): the paper's
`(1−θ)^r(1+rθ) ≤ 1` used to sign `g'`.  Proved by induction, no derivatives. -/
theorem one_sub_pow_mul_one_add_le_one {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (r : ℕ) :
    (1 - b) ^ r * (1 + r * b) ≤ 1 := by
  induction r with
  | zero => simp
  | succ n ih =>
    have h1b : (0:ℝ) ≤ 1 - b := by linarith
    have hpow : (0:ℝ) ≤ (1 - b) ^ n := pow_nonneg h1b n
    have key : (1 - b) ^ (n + 1) * (1 + (↑(n + 1)) * b) ≤ (1 - b) ^ n * (1 + ↑n * b) := by
      have e : (1 - b) ^ (n + 1) * (1 + (↑(n + 1)) * b)
          = (1 - b) ^ n * ((1 - b) * (1 + (↑(n + 1)) * b)) := by rw [pow_succ]; ring
      rw [e]
      apply mul_le_mul_of_nonneg_left _ hpow
      push_cast
      nlinarith [mul_nonneg (show (0:ℝ) ≤ (n:ℝ) + 1 by positivity) (sq_nonneg b)]
    exact le_trans key ih

/-- `r = (N+1)/2` (a Nat, exact since `N` is odd). -/
def chartR : Nat := (P.chartN + 1) / 2

theorem two_mul_chartR : 2 * P.chartR = P.chartN + 1 := by
  obtain ⟨k, hk⟩ := P.m_odd
  have := P.m_ge_nine
  unfold chartR chartN
  omega

/-- `(√v)^N < 1` (the paper's `η = v^{N/2} < 1`). -/
theorem chartVsqrtN_lt_one : (Real.sqrt P.chartV) ^ P.chartN < 1 := by
  have hsqrt1 : Real.sqrt P.chartV < 1 := by
    have h := Real.sqrt_lt_sqrt P.chartV_pos.le P.chartV_lt_one
    rwa [Real.sqrt_one] at h
  exact pow_lt_one₀ (Real.sqrt_nonneg _) hsqrt1
    (by have := P.m_ge_nine; unfold chartN; omega)

/-- `ζ·v = ℓ²·Hζ` (cleared form of `ℓ² = ζv/Hζ`). -/
theorem zeta_mul_chartV : P.chartZeta * P.chartV = P.ell ^ 2 * P.chartH := by
  have h1 : P.chartV = P.chartU * P.chartH := (P.chartU_mul_chartH).symm
  rw [h1]
  linear_combination P.chartH * P.chartZeta_mul_chartU

/-- From `T_N > 0` and eq:T-bound-one: `ζ(1 − η) < N(1+v)` (the cleared form of `ζ < Z`). -/
theorem zeta_mul_one_sub_lt (hT : 0 < P.chartTN) :
    P.chartZeta * (1 - (Real.sqrt P.chartV) ^ P.chartN) < (P.chartN : Real) * (1 + P.chartV) := by
  linarith [P.chartTN_le_one, hT]

/-- The sign of `g'` (paper 2624): `(tv/(t+1+v))^r · (1 + rθ) ≤ 1` with `θ = (1+v)/(t+1+v)`, from the
AM–GM helper via `tv/(t+1+v) = v(1−θ)`.  This makes `g'(t) = 1 − (tv/(t+1+v))^r(1+rθ) ≥ 0`. -/
theorem gderiv_sign {t v : ℝ} (ht : 0 < t) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (r : ℕ) :
    (t * v / (t + 1 + v)) ^ r * (1 + (r : ℝ) * ((1 + v) / (t + 1 + v))) ≤ 1 := by
  have hden : 0 < t + 1 + v := by linarith
  set θ := (1 + v) / (t + 1 + v) with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hden]; linarith
  have hh : t * v / (t + 1 + v) = v * (1 - θ) := by
    rw [hθ]; field_simp; ring
  rw [hh, mul_pow]
  have hamgm := one_sub_pow_mul_one_add_le_one hθ0 hθ1 r
  have hvr : v ^ r ≤ 1 := pow_le_one₀ hv0 hv1
  calc v ^ r * (1 - θ) ^ r * (1 + (r : ℝ) * θ)
      = v ^ r * ((1 - θ) ^ r * (1 + (r : ℝ) * θ)) := by ring
    _ ≤ v ^ r * 1 := mul_le_mul_of_nonneg_left hamgm (pow_nonneg hv0 r)
    _ = v ^ r := mul_one _
    _ ≤ 1 := hvr

/-- `g(t) = t(1 − (tv/(t+1+v))^r)` is monotone on `[0,∞)` (paper 2624: `g' ≥ 0`).  Derivative
computed with `HasDerivAt`; the derivative `1 − (tv/(t+1+v))^r(1+rθ) ≥ 0` is exactly `gderiv_sign`. -/
theorem g_monotoneOn {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) (r : ℕ) (hr : 1 ≤ r) :
    MonotoneOn (fun t => t * (1 - (t * v / (t + 1 + v)) ^ r)) (Set.Ici (0:ℝ)) := by
  have hHD : ∀ x : ℝ, 0 ≤ x →
      HasDerivAt (fun t => t * (1 - (t * v / (t + 1 + v)) ^ r))
        (1 - (x * v / (x + 1 + v)) ^ r
          * (1 + (r : ℝ) * ((1 + v) / (x + 1 + v)))) x := by
    intro x hx
    have hden : x + 1 + v ≠ 0 := by positivity
    have hWnum : HasDerivAt (fun t => t * v) v x := by
      simpa using (hasDerivAt_id x).mul_const v
    have hWden : HasDerivAt (fun t => t + 1 + v) 1 x := by
      simpa using ((hasDerivAt_id x).add_const 1).add_const v
    have hW : HasDerivAt (fun t => t * v / (t + 1 + v))
        ((v * (x + 1 + v) - x * v * 1) / (x + 1 + v) ^ 2) x := hWnum.div hWden hden
    have hg : HasDerivAt (fun t => t * (1 - (t * v / (t + 1 + v)) ^ r))
        (1 * (1 - (x * v / (x + 1 + v)) ^ r) + x *
          (0 - (↑r * (x * v / (x + 1 + v)) ^ (r - 1) *
            ((v * (x + 1 + v) - x * v * 1) / (x + 1 + v) ^ 2)))) x :=
      (hasDerivAt_id x).mul ((hasDerivAt_const x (1 : ℝ)).sub (hW.pow r))
    have hval : 1 * (1 - (x * v / (x + 1 + v)) ^ r) + x *
          (0 - (↑r * (x * v / (x + 1 + v)) ^ (r - 1) *
            ((v * (x + 1 + v) - x * v * 1) / (x + 1 + v) ^ 2)))
        = 1 - (x * v / (x + 1 + v)) ^ r * (1 + (r : ℝ) * ((1 + v) / (x + 1 + v))) := by
      obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [div_pow, div_pow]
      field_simp
      ring
    rw [hval] at hg
    exact hg
  have hcont : ContinuousOn (fun t => t * (1 - (t * v / (t + 1 + v)) ^ r)) (Set.Ici 0) :=
    fun x hx => (hHD x hx).continuousAt.continuousWithinAt
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont
  · intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    exact (hHD x hx.le).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    rw [(hHD x hx.le).deriv]
    linarith [gderiv_sign hx hv0.le hv1.le r]

/-- `Z = N(1+v)/(1−η)` (paper eq:zeta-upper-Z, 2614). -/
def chartZ : Real :=
  (P.chartN : Real) * (1 + P.chartV) / (1 - (Real.sqrt P.chartV) ^ P.chartN)

theorem chartR_pos : 1 ≤ P.chartR := by
  have h1 := P.two_mul_chartR
  have h2 : 7 ≤ P.chartN := by have := P.m_ge_nine; unfold chartN; omega
  omega

theorem chartZ_pos : 0 < P.chartZ := by
  unfold chartZ
  apply div_pos (mul_pos P.chartN_pos_real (by linarith [P.chartV_pos]))
  linarith [P.chartVsqrtN_lt_one]

theorem zeta_lt_chartZ (hT : 0 < P.chartTN) : P.chartZeta < P.chartZ := by
  have h1η : 0 < 1 - (Real.sqrt P.chartV) ^ P.chartN := by linarith [P.chartVsqrtN_lt_one]
  unfold chartZ
  rw [lt_div_iff₀ h1η]
  exact P.zeta_mul_one_sub_lt hT

/-- `ζv/(ζ+1+v) = ℓ²` (cleared `ℓ² = ζv/Hζ`). -/
theorem zeta_v_div_eq_ell_sq :
    P.chartZeta * P.chartV / (P.chartZeta + 1 + P.chartV) = P.ell ^ 2 := by
  have hH : P.chartZeta + 1 + P.chartV = P.chartH := rfl
  rw [hH, div_eq_iff P.chartH_pos.ne']
  exact P.zeta_mul_chartV

/-- `g(ζ) = ζ(1 − ℓ^{N+1})` (paper 2630; `(ζv/Hζ)^r = (ℓ²)^r = ℓ^{N+1}`). -/
theorem g_at_zeta :
    P.chartZeta * (1 - (P.chartZeta * P.chartV / (P.chartZeta + 1 + P.chartV)) ^ P.chartR)
      = P.chartZeta * (1 - P.ell ^ (P.chartN + 1)) := by
  have hpow : (P.chartZeta * P.chartV / (P.chartZeta + 1 + P.chartV)) ^ P.chartR
      = P.ell ^ (P.chartN + 1) := by
    rw [P.zeta_v_div_eq_ell_sq, ← pow_mul, P.two_mul_chartR]
  rw [hpow]

/-- `ζT_N < N·g(ζ)` (paper 2630; from eq:T-bound-two `T_N < N(1−ℓ^{N+1})`). -/
theorem zeta_mul_TN_lt :
    P.chartZeta * P.chartTN < (P.chartN : Real) * (P.chartZeta * (1 - P.ell ^ (P.chartN + 1))) := by
  nlinarith [mul_lt_mul_of_pos_left P.chartTN_lt P.chartZeta_pos]

/-- `g(ζ) ≤ g(Z)` (paper 2630, from monotonicity of `g`). -/
theorem g_zeta_le_g_Z (hT : 0 < P.chartTN) :
    P.chartZeta * (1 - P.ell ^ (P.chartN + 1))
      ≤ P.chartZ * (1 - (P.chartZ * P.chartV / (P.chartZ + 1 + P.chartV)) ^ P.chartR) := by
  have hmono := g_monotoneOn P.chartV_pos P.chartV_lt_one P.chartR P.chartR_pos
  have hle := hmono P.chartZeta_pos.le P.chartZ_pos.le (P.zeta_lt_chartZ hT).le
  simp only at hle
  rw [P.g_at_zeta] at hle
  exact hle

/-- `ω = Nv/(N+1−η)` (paper eq at 2636, `η = (√v)^N`). -/
def chartOmega : Real :=
  (P.chartN : Real) * P.chartV / ((P.chartN : Real) + 1 - (Real.sqrt P.chartV) ^ P.chartN)

/-- The `g(Z)`-base identity `Zv/(Z+1+v) = ω` (paper 2636), reducing `g(Z)` to `Z(1 − ω^r)`. -/
theorem chartZ_v_div_eq_omega :
    P.chartZ * P.chartV / (P.chartZ + 1 + P.chartV) = P.chartOmega := by
  have h1η : (0:ℝ) < 1 - (Real.sqrt P.chartV) ^ P.chartN := by linarith [P.chartVsqrtN_lt_one]
  have hNη : (0:ℝ) < (P.chartN : Real) + 1 - (Real.sqrt P.chartV) ^ P.chartN := by
    have := P.chartVsqrtN_lt_one; have := P.chartN_pos_real; linarith
  have hZ1v : (0:ℝ) < P.chartZ + 1 + P.chartV := by
    have := P.chartZ_pos; linarith [P.chartV_pos]
  unfold chartOmega
  rw [div_eq_div_iff hZ1v.ne' hNη.ne']
  unfold chartZ
  field_simp [h1η.ne']
  ring

/-! ### The f-tangent inequality (paper 2664), the last piece of `T_tangent_bound`

For `f(x) = N^r x^{(N+1)/N} / (N+1−x)^r` (paper `f(η)`), we prove `f(x) ≥ 1 + c(x−1)` on `(0,1]`
(the tangent at `x=1`, `c = 3(N+1)/2N`).  We AVOID the second derivative: bounding the only real
exponent `x^{1/N} ≤ 1` reduces `f'(x) ≤ c` to the Nat-power inequality `ψ(x) ≥ 0`, and `ψ` is
manifestly decreasing (its derivative is a sum of two nonpositive terms). -/

/-- The Nat-power core `ψ(x) ≥ 0` (equivalently `N^r(sD+rx) ≤ c D^{r+1}`, `D = N+1−x`, `s=(N+1)/N`,
`c=3(N+1)/2N`): manifestly-decreasing `ψ` with `ψ(1)=0`. -/
theorem psi_ge {N r : ℕ} (hNr : N + 1 = 2 * r) (hN2 : 2 ≤ N)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (N : ℝ) ^ r * (((N : ℝ) + 1) / (N : ℝ) * ((N : ℝ) + 1 - x) + (r : ℝ) * x)
      ≤ 3 * ((N : ℝ) + 1) / (2 * (N : ℝ)) * ((N : ℝ) + 1 - x) ^ (r + 1) := by
  have hNr : (N : ℝ) + 1 = 2 * (r : ℝ) := by exact_mod_cast hNr
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    linarith
  have hN2r : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hrs : ((N : ℝ) + 1) / (N : ℝ) ≤ (r : ℝ) := by
    rw [div_le_iff₀ hNpos]
    nlinarith [hNr, mul_nonneg (Nat.cast_nonneg r) (show (0 : ℝ) ≤ (N : ℝ) - 2 by linarith)]
  set φ : ℝ → ℝ := fun t =>
    3 * ((N : ℝ) + 1) / (2 * (N : ℝ)) * ((N : ℝ) + 1 - t) ^ (r + 1)
      - (N : ℝ) ^ r * (((N : ℝ) + 1) / (N : ℝ) * ((N : ℝ) + 1 - t) + (r : ℝ) * t) with hφdef
  have hderiv : ∀ t : ℝ, HasDerivAt φ
      (3 * ((N : ℝ) + 1) / (2 * (N : ℝ))
          * ((↑(r + 1) : ℝ) * ((N : ℝ) + 1 - t) ^ (r + 1 - 1) * (0 - 1))
        - (N : ℝ) ^ r * (((N : ℝ) + 1) / (N : ℝ) * (0 - 1) + (r : ℝ) * 1)) t := by
    intro t
    apply HasDerivAt.sub
    · exact (((hasDerivAt_const t ((N : ℝ) + 1)).sub (hasDerivAt_id t)).pow (r + 1)).const_mul _
    · exact ((((hasDerivAt_const t ((N : ℝ) + 1)).sub (hasDerivAt_id t)).const_mul
        (((N : ℝ) + 1) / (N : ℝ))).add ((hasDerivAt_id t).const_mul (r : ℝ))).const_mul ((N : ℝ) ^ r)
  have hanti : AntitoneOn φ (Set.Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc, Set.mem_Ioo] at ht
      rw [(hderiv t).deriv]
      simp only [Nat.add_sub_cancel]
      have hDnn : (0 : ℝ) ≤ ((N : ℝ) + 1 - t) ^ r :=
        pow_nonneg (by linarith [ht.2, hNpos]) r
      have hcnn : (0 : ℝ) ≤ 3 * ((N : ℝ) + 1) / (2 * (N : ℝ)) := by positivity
      have hNrnn : (0 : ℝ) ≤ (N : ℝ) ^ r := pow_nonneg hNpos.le r
      nlinarith [mul_nonneg (mul_nonneg hcnn (by positivity : (0 : ℝ) ≤ (↑(r + 1) : ℝ))) hDnn,
        mul_nonneg hNrnn (sub_nonneg.mpr hrs)]
  have hφ1 : φ 1 = 0 := by
    simp only [hφdef]
    have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
    rw [show (N : ℝ) + 1 - 1 = (N : ℝ) from by ring, pow_succ]
    field_simp
    linear_combination ((N : ℝ) ^ r) * hNr
  have key := hanti (Set.mem_Icc.mpr ⟨hx0, hx1⟩) (Set.mem_Icc.mpr ⟨by norm_num, le_refl 1⟩) hx1
  rw [hφ1] at key
  simp only [hφdef] at key
  linarith [key]

/-- The f-tangent inequality (paper 2664): `f(x) = N^r x^{(N+1)/N}/(N+1−x)^r ≥ 1 + c(x−1)` on `(0,1]`,
`c = 3(N+1)/2N`.  Only one real exponent (`x^{(N+1)/N}`); no second derivative. -/
theorem f_tangent {N r : ℕ} (hNr : N + 1 = 2 * r) (hN2 : 2 ≤ N)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    1 + 3 * ((N : ℝ) + 1) / (2 * (N : ℝ)) * (x - 1)
      ≤ (N : ℝ) ^ r * x ^ (((N : ℝ) + 1) / (N : ℝ)) / ((N : ℝ) + 1 - x) ^ r := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    linarith
  set s : ℝ := ((N : ℝ) + 1) / (N : ℝ) with hsdef
  set c : ℝ := 3 * ((N : ℝ) + 1) / (2 * (N : ℝ)) with hcdef
  set f : ℝ → ℝ := fun t => (N : ℝ) ^ r * t ^ s / ((N : ℝ) + 1 - t) ^ r with hfdef
  have hs1 : (1 : ℝ) ≤ s := by rw [hsdef, le_div_iff₀ hNpos]; linarith
  have hs0 : (0 : ℝ) ≤ s - 1 := by linarith
  have hfderiv : ∀ t : ℝ, 0 < t → t < (N : ℝ) + 1 →
      HasDerivAt f
        ((N : ℝ) ^ r * (s * t ^ (s - 1) * ((N : ℝ) + 1 - t) + (r : ℝ) * t ^ s)
          / ((N : ℝ) + 1 - t) ^ (r + 1)) t := by
    intro t ht0 htN
    have hDne : (N : ℝ) + 1 - t ≠ 0 := by linarith
    have hDpow : ((N : ℝ) + 1 - t) ^ r ≠ 0 := pow_ne_zero r hDne
    have hcomb :=
      (((Real.hasDerivAt_rpow_const (p := s) (Or.inl ht0.ne')).const_mul ((N : ℝ) ^ r)).div
        (((hasDerivAt_const t ((N : ℝ) + 1)).sub (hasDerivAt_id t)).pow r) hDpow)
    convert hcomb using 1
    all_goals try rfl
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Pi.sub_apply, Pi.pow_apply, id_eq]
    field_simp
    ring
  have hfle : ∀ t : ℝ, 0 < t → t ≤ 1 →
      (N : ℝ) ^ r * (s * t ^ (s - 1) * ((N : ℝ) + 1 - t) + (r : ℝ) * t ^ s)
        / ((N : ℝ) + 1 - t) ^ (r + 1) ≤ c := by
    intro t ht0 ht1
    have hD1 : (0 : ℝ) < (N : ℝ) + 1 - t := by linarith
    have hDp : (0 : ℝ) < ((N : ℝ) + 1 - t) ^ (r + 1) := pow_pos hD1 _
    have hts1 : t ^ (s - 1) ≤ 1 := Real.rpow_le_one ht0.le ht1 hs0
    have htss : t ^ s ≤ t := by
      calc t ^ s ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge ht0 ht1 hs1
        _ = t := Real.rpow_one t
    have hspos : (0 : ℝ) ≤ s := by linarith
    have hnum : s * t ^ (s - 1) * ((N : ℝ) + 1 - t) + (r : ℝ) * t ^ s
        ≤ s * ((N : ℝ) + 1 - t) + (r : ℝ) * t := by
      have hA : s * t ^ (s - 1) * ((N : ℝ) + 1 - t) ≤ s * ((N : ℝ) + 1 - t) := by
        nlinarith [mul_nonneg hspos hD1.le, hts1,
          mul_nonneg (mul_nonneg hspos hD1.le) (sub_nonneg.mpr hts1)]
      have hB : (r : ℝ) * t ^ s ≤ (r : ℝ) * t := mul_le_mul_of_nonneg_left htss (Nat.cast_nonneg r)
      linarith
    have hNr0 : (0 : ℝ) ≤ (N : ℝ) ^ r := pow_nonneg hNpos.le r
    have hpsi := psi_ge hNr hN2 ht0.le ht1
    rw [← hsdef, ← hcdef] at hpsi
    rw [div_le_iff₀ hDp]
    nlinarith [mul_le_mul_of_nonneg_left hnum hNr0, hpsi]
  have hderivh : ∀ t : ℝ, 0 < t → t < (N : ℝ) + 1 →
      HasDerivAt (fun u => f u - c * u)
        ((N : ℝ) ^ r * (s * t ^ (s - 1) * ((N : ℝ) + 1 - t) + (r : ℝ) * t ^ s)
          / ((N : ℝ) + 1 - t) ^ (r + 1) - c) t := by
    intro t ht0 htN
    have hc : HasDerivAt (fun u => c * u) c t := by simpa using (hasDerivAt_id t).const_mul c
    exact (hfderiv t ht0 htN).sub hc
  have hanti : AntitoneOn (fun u => f u - c * u) (Set.Icc x 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc x 1)
    · exact fun t ht => (hderivh t (by have := (Set.mem_Icc.mp ht).1; linarith)
        (by have := (Set.mem_Icc.mp ht).2; linarith)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc, Set.mem_Ioo] at ht
      exact (hderivh t (by linarith [ht.1]) (by linarith [ht.2])).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc, Set.mem_Ioo] at ht
      rw [(hderivh t (by linarith [ht.1]) (by linarith [ht.2])).deriv]
      have := hfle t (by linarith [ht.1]) (le_of_lt ht.2)
      linarith
  have hf1 : f 1 = 1 := by
    simp only [hfdef]
    rw [Real.one_rpow, show (N : ℝ) + 1 - 1 = (N : ℝ) from by ring]
    field_simp
  have hres := hanti (Set.mem_Icc.mpr ⟨le_refl x, hx1⟩) (Set.mem_Icc.mpr ⟨hx1, le_refl 1⟩) hx1
  simp only at hres
  rw [hf1] at hres
  simp only [hfdef] at hres ⊢
  linarith [hres]

/-- `g(Z) ≤ (3(N+1)/2)(1+v)` (paper 2664): `g(Z) = Z(1 − ω^r)`, and `f_tangent` at `x = η = (√v)^N`
(using `η^{(N+1)/N} = v^r`) gives `1 − ω^r ≤ (3(N+1)/2N)(1−η)`; the `(1−η)` cancels `Z`'s denominator. -/
theorem g_at_Z_le :
    P.chartZ * (1 - P.chartOmega ^ P.chartR) ≤ 3 * ((P.chartN : ℝ) + 1) / 2 * (1 + P.chartV) := by
  have hηlt : (Real.sqrt P.chartV) ^ P.chartN < 1 := P.chartVsqrtN_lt_one
  have h1η : (0 : ℝ) < 1 - (Real.sqrt P.chartV) ^ P.chartN := by linarith
  have hηpos : 0 < (Real.sqrt P.chartV) ^ P.chartN := pow_pos (Real.sqrt_pos.2 P.chartV_pos) _
  have hNr : P.chartN + 1 = 2 * P.chartR := P.two_mul_chartR.symm
  have hN2 : 2 ≤ P.chartN := by have := P.m_ge_nine; unfold chartN; omega
  have hNpos : (0 : ℝ) < (P.chartN : ℝ) := by
    have : (2 : ℝ) ≤ (P.chartN : ℝ) := by exact_mod_cast hN2
    linarith
  have hN0 : (P.chartN : ℝ) ≠ 0 := hNpos.ne'
  have hsv : (0 : ℝ) ≤ Real.sqrt P.chartV := Real.sqrt_nonneg _
  have hηs : ((Real.sqrt P.chartV) ^ P.chartN) ^ (((P.chartN : ℝ) + 1) / (P.chartN : ℝ))
      = P.chartV ^ P.chartR := by
    have hNs : (P.chartN : ℝ) * (((P.chartN : ℝ) + 1) / (P.chartN : ℝ)) = (P.chartN : ℝ) + 1 := by
      field_simp
    rw [← Real.rpow_natCast (Real.sqrt P.chartV) P.chartN, ← Real.rpow_mul hsv, hNs,
      show (P.chartN : ℝ) + 1 = ((P.chartN + 1 : ℕ) : ℝ) from by push_cast; ring, Real.rpow_natCast,
      ← P.two_mul_chartR, pow_mul, Real.sq_sqrt P.chartV_pos.le]
  have hfeq : (P.chartN : ℝ) ^ P.chartR
        * ((Real.sqrt P.chartV) ^ P.chartN) ^ (((P.chartN : ℝ) + 1) / (P.chartN : ℝ))
        / ((P.chartN : ℝ) + 1 - (Real.sqrt P.chartV) ^ P.chartN) ^ P.chartR
      = P.chartOmega ^ P.chartR := by
    rw [hηs]; unfold chartOmega; rw [div_pow, mul_pow]
  have hft := f_tangent hNr hN2 hηpos hηlt.le
  rw [hfeq] at hft
  have h1 : 1 - P.chartOmega ^ P.chartR
      ≤ 3 * ((P.chartN : ℝ) + 1) / (2 * (P.chartN : ℝ)) * (1 - (Real.sqrt P.chartV) ^ P.chartN) := by
    nlinarith [hft]
  calc P.chartZ * (1 - P.chartOmega ^ P.chartR)
      ≤ P.chartZ * (3 * ((P.chartN : ℝ) + 1) / (2 * (P.chartN : ℝ))
          * (1 - (Real.sqrt P.chartV) ^ P.chartN)) :=
        mul_le_mul_of_nonneg_left h1 P.chartZ_pos.le
    _ = 3 * ((P.chartN : ℝ) + 1) / 2 * (1 + P.chartV) := by
        unfold chartZ
        field_simp

/-- **Paper eq:T-tangent-bound (2580):** if `T_N > 0` then `ζ·T_N < (3N(N+1)/2)(1+v)`. -/
theorem chartZeta_mul_chartTN_lt (hT : 0 < P.chartTN) :
    P.chartZeta * P.chartTN < 3 * (P.chartN : ℝ) * ((P.chartN : ℝ) + 1) / 2 * (1 + P.chartV) := by
  have h2 := P.g_zeta_le_g_Z hT
  rw [P.chartZ_v_div_eq_omega] at h2
  have hchain := le_trans h2 P.g_at_Z_le
  nlinarith [P.zeta_mul_TN_lt, mul_le_mul_of_nonneg_left hchain P.chartN_pos_real.le]

end AdmissibleParams
end OddCycleBound.IntermediateRegion.Scalar
