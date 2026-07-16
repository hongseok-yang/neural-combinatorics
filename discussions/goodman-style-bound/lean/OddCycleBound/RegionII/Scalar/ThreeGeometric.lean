import OddCycleBound.RegionII.Scalar.Elementary
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Three-geometric defect and the secant gate

This is the density-independent analytic reduction used by moderate Zone C
and by the Turan-corner argument.
-/

noncomputable section

namespace OddCycleBound.RegionII.Scalar
namespace AdmissibleParams

variable (P : AdmissibleParams)

def ell : Real := P.L / P.alpha
def y : Real := P.L / P.p
def s : Real := P.q / P.p
def G2 : Real := P.ell ^ 2 * (1 - (P.y / P.s) ^ 13)

theorem ell_nonneg : 0 <= P.ell := div_nonneg P.L_nonneg P.alpha_nonneg
theorem y_nonneg : 0 <= P.y := div_nonneg P.L_nonneg P.p_pos.le
theorem s_pos : 0 < P.s := div_pos P.q_pos P.p_pos
theorem y_lt_s : P.y < P.s :=
  (div_lt_div_iff_of_pos_right P.p_pos).2 P.L_lt_q
theorem s_lt_x : P.s < P.x :=
  (div_lt_div_iff_of_pos_right P.p_pos).2 P.alpha_gt_q
theorem x_lt_one : P.x < 1 := (div_lt_one P.p_pos).2 P.alpha_lt_p

theorem y_div_s_nonneg : 0 <= P.y / P.s :=
  div_nonneg P.y_nonneg P.s_pos.le

theorem y_div_s_lt_one : P.y / P.s < 1 :=
  (div_lt_one P.s_pos).2 P.y_lt_s

theorem G2_nonneg : 0 <= P.G2 := by
  unfold G2
  exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr
    (pow_le_one₀ P.y_div_s_nonneg P.y_div_s_lt_one.le))

/-- Exact normalized three-geometric expansion of the scalar defect. -/
theorem R_three_geometric :
    P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) =
      P.x ^ (P.m - 2) / P.alpha +
      P.ell ^ 2 * P.y ^ (P.m - 2) / P.alpha -
      (P.p * P.q / P.alpha ^ 3) * P.s ^ (P.m - 2) := by
  have hm2 : 2 <= P.m := le_trans (by norm_num) P.m_ge_fifteen
  have hm1 : 1 <= P.m := le_trans (by norm_num) P.m_ge_fifteen
  have haPow : P.alpha ^ P.m =
      P.alpha ^ (P.m - 2) * P.alpha ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hm2]
  have hLPow : P.L ^ P.m = P.L ^ (P.m - 2) * P.L ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hm2]
  have hqPow : P.q ^ (P.m - 1) = P.q ^ (P.m - 2) * P.q := by
    rw [← pow_succ, show P.m - 2 + 1 = P.m - 1 by omega]
  have hpPow : P.p ^ (P.m - 2) ≠ 0 := pow_ne_zero _ P.p_pos.ne'
  have haTerm :
      P.alpha ^ P.m / (P.alpha ^ 3 * P.p ^ (P.m - 2)) =
        P.x ^ (P.m - 2) / P.alpha := by
    rw [haPow]
    unfold x
    rw [div_pow]
    field_simp [P.alpha_pos.ne', P.p_pos.ne', hpPow]
  have hLTerm :
      P.L ^ P.m / (P.alpha ^ 3 * P.p ^ (P.m - 2)) =
        P.ell ^ 2 * P.y ^ (P.m - 2) / P.alpha := by
    rw [hLPow]
    unfold ell y
    rw [div_pow, div_pow]
    field_simp [P.alpha_pos.ne', P.p_pos.ne', hpPow]
  have hqTerm :
      P.p * P.q ^ (P.m - 1) / (P.alpha ^ 3 * P.p ^ (P.m - 2)) =
        (P.p * P.q / P.alpha ^ 3) * P.s ^ (P.m - 2) := by
    rw [hqPow]
    unfold s
    rw [div_pow]
    ring
  unfold R
  calc
    (P.alpha ^ P.m + P.L ^ P.m - P.p * P.q ^ (P.m - 1)) /
        (P.alpha ^ 3 * P.p ^ (P.m - 2)) =
      P.alpha ^ P.m / (P.alpha ^ 3 * P.p ^ (P.m - 2)) +
        P.L ^ P.m / (P.alpha ^ 3 * P.p ^ (P.m - 2)) -
        P.p * P.q ^ (P.m - 1) / (P.alpha ^ 3 * P.p ^ (P.m - 2)) := by ring
    _ = _ := by rw [haTerm, hLTerm, hqTerm]

theorem three_geometric_coefficient :
    P.p * P.q / P.alpha ^ 3 = 1 / P.alpha + P.ell ^ 2 / P.alpha := by
  unfold ell
  rw [div_pow, P.L_sq]
  field_simp [P.alpha_pos.ne']
  ring

/-- Dropping the two nonpositive safe-geometric terms leaves the frontier
geometric.  This is the form used by the `kappa -> 0` bottom-out. -/
theorem normalized_R_le_x_term :
    P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) <=
      P.x ^ (P.m - 2) / P.alpha := by
  let n := P.m - 2
  have hyPow : P.y ^ n <= P.s ^ n :=
    pow_le_pow_left₀ P.y_nonneg P.y_lt_s.le n
  have hellCoeff : 0 <= P.ell ^ 2 / P.alpha :=
    div_nonneg (sq_nonneg P.ell) P.alpha_nonneg
  have honeCoeff : 0 <= 1 / P.alpha := one_div_nonneg.mpr P.alpha_nonneg
  have hsPow : 0 <= P.s ^ n := pow_nonneg P.s_pos.le n
  have hsafe :
      P.ell ^ 2 / P.alpha * P.y ^ n <=
        P.ell ^ 2 / P.alpha * P.s ^ n :=
    mul_le_mul_of_nonneg_left hyPow hellCoeff
  rw [P.R_three_geometric, P.three_geometric_coefficient]
  dsimp [n] at hsafe hsPow ⊢
  have hrewrite : P.ell ^ 2 * P.y ^ (P.m - 2) / P.alpha =
      (P.ell ^ 2 / P.alpha) * P.y ^ (P.m - 2) := by ring
  rw [hrewrite]
  nlinarith [mul_nonneg honeCoeff hsPow]

theorem R_pos_iff_three_geometric :
    0 < P.R ↔
      P.x ^ (P.m - 2) - P.s ^ (P.m - 2) >
        P.ell ^ 2 * (P.s ^ (P.m - 2) - P.y ^ (P.m - 2)) := by
  have hden : 0 < P.alpha ^ 3 * P.p ^ (P.m - 2) :=
    mul_pos (pow_pos P.alpha_pos _) (pow_pos P.p_pos _)
  have hcompact :
      P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) =
        (P.x ^ (P.m - 2) - P.s ^ (P.m - 2) -
          P.ell ^ 2 * (P.s ^ (P.m - 2) - P.y ^ (P.m - 2))) / P.alpha := by
    rw [P.R_three_geometric, P.three_geometric_coefficient]
    field_simp [P.alpha_pos.ne']
    ring
  constructor
  · intro hR
    have hnorm : 0 < P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) := div_pos hR hden
    rw [hcompact, div_pos_iff_of_pos_right P.alpha_pos] at hnorm
    linarith
  · intro hgeo
    have hnorm : 0 < P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) := by
      rw [hcompact, div_pos_iff_of_pos_right P.alpha_pos]
      linarith
    exact (div_pos_iff_of_pos_right hden).mp hnorm

/-- Positive defect implies the exact secant power gate. -/
theorem secant_power_gate (hR : 0 < P.R) :
    1 + P.G2 < (P.x / P.s) ^ (P.m - 2) := by
  let n := P.m - 2
  let r := P.y / P.s
  have hm15 := P.m_ge_fifteen
  have hn13 : 13 <= n := by dsimp [n]; omega
  have hr0 : 0 <= r := by simpa [r] using P.y_div_s_nonneg
  have hr1 : r <= 1 := by exact P.y_div_s_lt_one.le
  have hrpow : r ^ n <= r ^ 13 := pow_le_pow_of_le_one hr0 hr1 hn13
  have hyn : P.y ^ n = P.s ^ n * r ^ n := by
    dsimp [r]
    rw [div_pow]
    field_simp [P.s_pos.ne']
  have hgeo := (P.R_pos_iff_three_geometric).mp hR
  change P.x ^ n - P.s ^ n > P.ell ^ 2 * (P.s ^ n - P.y ^ n) at hgeo
  have hscale :
      P.ell ^ 2 * P.s ^ n * (1 - r ^ 13) <=
        P.ell ^ 2 * P.s ^ n * (1 - r ^ n) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left hrpow 1)
      (mul_nonneg (sq_nonneg _) (pow_nonneg P.s_pos.le _))
  have hmain : P.s ^ n * (1 + P.G2) < P.x ^ n := by
    unfold G2
    change P.s ^ n * (1 + P.ell ^ 2 * (1 - r ^ 13)) < P.x ^ n
    rw [hyn] at hgeo
    nlinarith
  rw [div_pow]
  exact (lt_div_iff₀ (pow_pos P.s_pos n)).2 (by simpa [mul_comm] using hmain)

/-- The logarithmic secant gate in the form used by the interval checker. -/
theorem secant_log_gate (hR : 0 < P.R) :
    Real.log (1 + P.G2) <
      ((P.m - 2 : Nat) : Real) * Real.log (P.alpha / P.q) := by
  have hbase : 0 < 1 + P.G2 := by linarith [P.G2_nonneg]
  have hratio : P.x / P.s = P.alpha / P.q := by
    unfold x s
    field_simp [P.p_pos.ne', P.q_pos.ne']
  have hpow := P.secant_power_gate hR
  have hlog := Real.log_lt_log hbase hpow
  rw [Real.log_pow, hratio] at hlog
  exact hlog

theorem log_alpha_div_q_le_d_div_q :
    Real.log (P.alpha / P.q) <= P.d / P.q := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos P.alpha_pos P.q_pos)
  have hid : P.alpha / P.q - 1 = P.d / P.q := by
    unfold d
    field_simp [P.q_pos.ne']
  linarith

/-- Full secant gate, including the elementary logarithmic upper bound. -/
theorem secant_gate (hR : 0 < P.R) :
    Real.log (1 + P.G2) <
      ((P.m - 2 : Nat) : Real) * Real.log (P.alpha / P.q) ∧
    ((P.m - 2 : Nat) : Real) * Real.log (P.alpha / P.q) <=
      ((P.m - 2 : Nat) : Real) * P.d / P.q := by
  refine ⟨P.secant_log_gate hR, ?_⟩
  have hn : (0 : Real) <= (P.m - 2 : Nat) := by positivity
  calc
    ((P.m - 2 : Nat) : Real) * Real.log (P.alpha / P.q) <=
        ((P.m - 2 : Nat) : Real) * (P.d / P.q) :=
      mul_le_mul_of_nonneg_left P.log_alpha_div_q_le_d_div_q hn
    _ = ((P.m - 2 : Nat) : Real) * P.d / P.q := by ring

end AdmissibleParams
end OddCycleBound.RegionII.Scalar
