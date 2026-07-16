import OddCycleBound.RegionII.Scalar.Coordinates

/-!
# Elementary admissible-domain inequalities

This file records the exact algebraic facts used repeatedly by the three
scalar zones, including the corrected frontier-gap estimate.
-/

noncomputable section

namespace OddCycleBound.RegionII.Scalar

namespace AdmissibleParams

variable (P : AdmissibleParams)

theorem L_lt_q : P.L < P.q := by
  have hpq : P.p * P.q - P.alpha ^ 2 < P.q ^ 2 := by
    have halphaSq : P.q ^ 2 < P.alpha ^ 2 :=
      pow_lt_pow_left₀ P.alpha_gt_q P.q_nonneg (by norm_num)
    have hq3 : P.q < 3 * P.q ^ 2 := by
      have hthree : 0 < 3 * P.q - 1 := by linarith [P.q_gt_third]
      nlinarith [mul_pos P.q_pos hthree]
    dsimp [p]
    nlinarith
  have hsq : P.L ^ 2 < P.q ^ 2 := by
    rw [P.L_sq]
    exact hpq
  by_contra hnot
  have hqle : P.q <= P.L := le_of_not_gt hnot
  have hsquareLe : P.q ^ 2 <= P.L ^ 2 :=
    pow_le_pow_left₀ P.q_nonneg hqle 2
  exact (not_lt_of_ge hsquareLe) hsq

theorem L_nonneg_lt_q : 0 <= P.L ∧ P.L < P.q :=
  ⟨P.L_nonneg, P.L_lt_q⟩

theorem d_lt_delta : P.d < P.alpha - 1 / 3 := by
  unfold d
  linarith [P.q_gt_third]

theorem delta_pos : 0 < P.alpha - 1 / 3 := by
  exact sub_pos.mpr (P.q_gt_third.trans P.alpha_gt_q)

/-- First corrected frontier-gap inequality: `d + L <= 1/3`. -/
theorem d_add_L_le_third : P.d + P.L <= 1 / 3 := by
  let delta := P.alpha - 1 / 3
  have hdelta : 0 < delta := by simpa [delta] using P.delta_pos
  have hdlt : P.d < delta := by simpa [delta] using P.d_lt_delta
  have hrpos : 0 < 1 / 3 - P.d := by
    have hdeltaSixth : delta < 1 / 6 := by
      dsimp [delta]
      linarith [P.alpha_lt_half]
    linarith
  have hid : (1 / 3 - P.d) ^ 2 - P.L ^ 2 =
      2 * (P.d ^ 2 - P.d * delta + delta ^ 2) +
        (delta - P.d) / 3 := by
    rw [P.L_sq]
    unfold p d
    dsimp [delta]
    ring
  have hquad : 0 <= P.d ^ 2 - P.d * delta + delta ^ 2 := by
    nlinarith [sq_nonneg (P.d - delta / 2), sq_nonneg delta]
  have hsq : P.L ^ 2 <= (1 / 3 - P.d) ^ 2 := by
    nlinarith
  have hLle : P.L <= 1 / 3 - P.d := by
    exact (sq_le_sq₀ P.L_nonneg (le_of_lt hrpos)).mp hsq
  linarith

theorem q_sub_L_ge_delta :
    P.alpha - 1 / 3 <= P.q - P.L := by
  have hdL := P.d_add_L_le_third
  unfold d at hdL
  linarith

/-- Corrected Zone-C frontier-gap bound `f >= d + delta`. -/
theorem f_ge_d_add_delta :
    P.d + (P.alpha - 1 / 3) <= P.f := by
  have hqL := P.q_sub_L_ge_delta
  unfold f d
  linarith

/-- The defect in the ratio form used by all three zones. -/
theorem R_defect_form :
    P.R = P.alpha ^ (P.m - 1) *
        (P.alpha - P.p * P.tau ^ (P.m - 1)) + P.L ^ P.m := by
  have halpha : P.alpha ≠ 0 := P.alpha_pos.ne'
  have htau : P.alpha * P.tau = P.q := by
    unfold tau
    field_simp [halpha]
  have hmpos : 0 < P.m :=
    lt_of_lt_of_le (by norm_num : 0 < 15) P.m_ge_fifteen
  have hmindex : P.m - 1 + 1 = P.m := Nat.sub_add_cancel hmpos
  have halphaPow : P.alpha ^ P.m =
      P.alpha ^ (P.m - 1) * P.alpha := by
    rw [← pow_succ, hmindex]
  have hqPow : P.q ^ (P.m - 1) =
      P.alpha ^ (P.m - 1) * P.tau ^ (P.m - 1) := by
    rw [← mul_pow, htau]
  unfold R
  rw [halphaPow, hqPow]
  ring

end AdmissibleParams

end OddCycleBound.RegionII.Scalar
