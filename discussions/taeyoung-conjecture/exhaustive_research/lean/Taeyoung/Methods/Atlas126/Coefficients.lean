import Taeyoung.Methods.Atlas126.Corners

/-!
# Atlas 126: supporting-plane coefficients

This file isolates the coefficient algebra from the large Bernstein
certificates.  In particular, the high-density interval has polynomial
coefficients, so all of its sign and endpoint obligations can be discharged
without loading any generated certificate table.
-/

namespace Taeyoung.Methods.Atlas126

/-- The chromatic target for Atlas 126. -/
def target (p : ℝ) : ℝ :=
  p ^ 2 * (2 * p - 1) * (p ^ 3 + (1 - p) ^ 3)

/-- Fisher's coordinate for the low-density interval. -/
noncomputable def lowDensity (x : ℝ) : ℝ :=
  (3 + 2 * x - x ^ 2) / 6

/-- The sharp triangle profile in Fisher's coordinate. -/
noncomputable def lowTriangle (x : ℝ) : ℝ :=
  x * (3 - x) ^ 2 / 18

/-- The positive denominator used by the low supporting plane. -/
def densitySquare (p : ℝ) : ℝ := p ^ 2 + (1 - p) ^ 2

/-- The contact degree of the low supporting plane. -/
noncomputable def lowContact (p : ℝ) : ℝ := p ^ 2 / densitySquare p

/-- The low-density `γ` coefficient. -/
noncomputable def gammaLow (p : ℝ) : ℝ :=
  1 / 16 + (2 * p - 1) / 2 + (2 * p - 1) ^ 2

/-- The low-density `β` coefficient. -/
noncomputable def betaLow (p : ℝ) : ℝ := 2 * gammaLow p * lowContact p

lemma lowDensity_sub_half (x : ℝ) :
    lowDensity x - 1 / 2 = x * (2 - x) / 6 := by
  simp only [lowDensity]
  ring

lemma two_thirds_sub_lowDensity (x : ℝ) :
    2 / 3 - lowDensity x = (1 - x) ^ 2 / 6 := by
  simp only [lowDensity]
  ring

/-- `x ∈ [0,1]` parametrizes exactly the low-density interval. -/
theorem lowDensity_mem {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 : ℝ) / 2 ≤ lowDensity x ∧ lowDensity x ≤ (2 : ℝ) / 3 := by
  have hx2 : 0 ≤ 2 - x := by linarith
  constructor
  · have hprod : 0 ≤ x * (2 - x) := mul_nonneg hx0 hx2
    rw [← sub_nonneg, lowDensity_sub_half]
    positivity
  · rw [← sub_nonneg, two_thirds_sub_lowDensity]
    positivity

theorem lowTriangle_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ lowTriangle x := by
  simp only [lowTriangle]
  positivity

lemma densitySquare_identity (p : ℝ) :
    2 * densitySquare p = (2 * p - 1) ^ 2 + 1 := by
  simp only [densitySquare]
  ring

theorem densitySquare_pos (p : ℝ) : 0 < densitySquare p := by
  have hs : 0 ≤ (2 * p - 1) ^ 2 := sq_nonneg _
  have hid := densitySquare_identity p
  nlinarith

theorem lowContact_nonneg (p : ℝ) : 0 ≤ lowContact p := by
  exact div_nonneg (sq_nonneg _) (densitySquare_pos p).le

theorem lowContact_le_one (p : ℝ) : lowContact p ≤ 1 := by
  rw [lowContact, div_le_one (densitySquare_pos p)]
  simp only [densitySquare]
  nlinarith [sq_nonneg (1 - p)]

theorem gammaLow_nonneg {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) :
    0 ≤ gammaLow p := by
  have hc : 0 ≤ 2 * p - 1 := by linarith
  simp only [gammaLow]
  positivity

theorem betaLow_nonneg {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) :
    0 ≤ betaLow p := by
  exact mul_nonneg (mul_nonneg (by norm_num) (gammaLow_nonneg hp))
    (lowContact_nonneg p)

/-- The low coefficients are tangent at `ρ`. -/
lemma betaLow_eq (p : ℝ) :
    betaLow p = 2 * gammaLow p * lowContact p := rfl

lemma lowDensity_fisher (y : ℝ) :
    lowDensity (3 * y) = (1 + 2 * y - 3 * y ^ 2) / 2 := by
  simp only [lowDensity]
  ring

lemma lowTriangle_fisher (y : ℝ) :
    lowTriangle (3 * y) = 3 / 2 * y * (1 - y) ^ 2 := by
  simp only [lowTriangle]
  ring

/-- The Atlas 126 target is nonnegative on its chromatic interval. -/
theorem target_nonneg {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) : 0 ≤ target p := by
  have hp0 : 0 ≤ p := by linarith
  have hc : 0 ≤ 2 * p - 1 := by linarith
  have hsq : 0 ≤ (p - 1 / 2) ^ 2 := sq_nonneg _
  have hsum : 0 ≤ p ^ 3 + (1 - p) ^ 3 := by nlinarith
  simp only [target]
  positivity

/-! ### The two polynomial low-density planes used by the Lean certificate -/

/-- The contact coordinate used by certificate A. -/
noncomputable def contactA (x : ℝ) : ℝ := 1 / 2 + 5 * x / 12

/-- Certificate A reuses the elementary low `γ`. -/
noncomputable def gammaA (x : ℝ) : ℝ := gammaLow (lowDensity x)

noncomputable def betaA (x : ℝ) : ℝ := 2 * gammaA x * contactA x

noncomputable def lambdaA (x : ℝ) : ℝ := 1 / 16 + x / 50

/-- The transition plane used on `5/8 ≤ x ≤ 15/16`. -/
noncomputable def betaC (x : ℝ) : ℝ :=
  2 / 3 + (1 - x) * (-467 / 32 + 40 * x - 461 / 16 * x ^ 2)

noncomputable def gammaC (x : ℝ) : ℝ :=
  4 / 9 + (1 - x) * (-357 / 32 + 987 / 32 * x - 89 / 4 * x ^ 2)

noncomputable def lambdaC (x : ℝ) : ℝ :=
  (1 - x) * (65 / 16 - 187 / 16 * x + 285 / 32 * x ^ 2)

noncomputable def gapZeroA (x : ℝ) : ℝ :=
  betaA x * lowDensity x + lambdaA x * lowTriangle x -
    target (lowDensity x)

noncomputable def gapOneA (x : ℝ) : ℝ :=
  lowDensity x ^ 3 - target (lowDensity x) -
    betaA x * (1 - lowDensity x) -
    gammaA x * (lowDensity x - 1) -
    lambdaA x * (lowDensity x - lowTriangle x)

noncomputable def gapZeroC (x : ℝ) : ℝ :=
  betaC x * lowDensity x + lambdaC x * lowTriangle x -
    target (lowDensity x)

noncomputable def gapOneC (x : ℝ) : ℝ :=
  lowDensity x ^ 3 - target (lowDensity x) -
    betaC x * (1 - lowDensity x) -
    gammaC x * (lowDensity x - 1) -
    lambdaC x * (lowDensity x - lowTriangle x)

theorem contactA_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ contactA x := by
  simp only [contactA]
  positivity

theorem gammaA_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ gammaA x := by
  exact gammaLow_nonneg (lowDensity_mem hx0 hx1).1

theorem betaA_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ betaA x := by
  exact mul_nonneg (mul_nonneg (by norm_num) (gammaA_nonneg hx0 hx1))
    (contactA_nonneg hx0)

theorem lambdaA_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ lambdaA x := by
  simp only [lambdaA]
  positivity

theorem transition_join_coefficients :
    betaC 1 = (2 : ℝ) / 3 ∧ gammaC 1 = (4 : ℝ) / 9 ∧ lambdaC 1 = 0 := by
  constructor
  · norm_num [betaC]
  · constructor <;> norm_num [gammaC, lambdaC]

/-- The `γ` coefficient on the high-density interval `2/3 ≤ p ≤ 1`. -/
def gammaHigh (p : ℝ) : ℝ :=
  2 * p * (9 * p ^ 2 - 10 * p + 3)

/-- The `β` coefficient on the high-density interval `2/3 ≤ p ≤ 1`. -/
def betaHigh (p : ℝ) : ℝ :=
  p * (30 * p ^ 3 - 29 * p ^ 2 + 6 * p + 1)

/-! The original linear approach to the high-density plane is not valid
arbitrarily close to `x = 1`.  On the junction interval we instead perturb
the high-density coefficients only to second order in `1-x`. -/

noncomputable def betaJ (x : ℝ) : ℝ :=
  betaHigh (lowDensity x) - 38 * (1 - x) ^ 2

noncomputable def gammaJ (x : ℝ) : ℝ :=
  gammaHigh (lowDensity x) - 29 * (1 - x) ^ 2

noncomputable def lambdaJ (x : ℝ) : ℝ :=
  15 * (1 - x) ^ 2

noncomputable def gapZeroJ (x : ℝ) : ℝ :=
  betaJ x * lowDensity x + lambdaJ x * lowTriangle x -
    target (lowDensity x)

noncomputable def gapOneJ (x : ℝ) : ℝ :=
  lowDensity x ^ 3 - target (lowDensity x) -
    betaJ x * (1 - lowDensity x) -
    gammaJ x * (lowDensity x - 1) -
    lambdaJ x * (lowDensity x - lowTriangle x)

/-- The coordinate taking `[2/3,1]` to `[0,1]`. -/
def highParam (p : ℝ) : ℝ := 3 * p - 2

lemma highParam_nonneg {p : ℝ} (hp : (2 : ℝ) / 3 ≤ p) :
    0 ≤ highParam p := by
  simp only [highParam]
  linarith

lemma highParam_le_one {p : ℝ} (hp : p ≤ 1) :
    highParam p ≤ 1 := by
  simp only [highParam]
  linarith

/-- A positive-coordinate form of the quadratic occurring in `γ_H`. -/
lemma gammaHigh_inner (p : ℝ) :
    3 * (9 * p ^ 2 - 10 * p + 3)
      = 3 * highParam p ^ 2 + 2 * highParam p + 1 := by
  simp only [highParam]
  ring

/-- `γ_H` is nonnegative on the full high-density interval. -/
theorem gammaHigh_nonneg {p : ℝ} (hp : (2 : ℝ) / 3 ≤ p) :
    0 ≤ gammaHigh p := by
  have hx : 0 ≤ highParam p := highParam_nonneg hp
  have hp0 : 0 ≤ p := by linarith
  have hinner : 0 ≤ 9 * p ^ 2 - 10 * p + 3 := by
    have hsq : 0 ≤ highParam p ^ 2 := sq_nonneg _
    have hlin : 0 ≤ 2 * highParam p := mul_nonneg (by norm_num) hx
    have hid := gammaHigh_inner p
    nlinarith
  exact mul_nonneg (mul_nonneg (by norm_num) hp0) hinner

/-- A positive-coordinate form of the polynomial occurring in `β_H`. -/
lemma betaHigh_inner (p : ℝ) :
    9 * (30 * p ^ 3 - 29 * p ^ 2 + 6 * p + 1)
      = 10 * highParam p ^ 3 + 31 * highParam p ^ 2
          + 22 * highParam p + 9 := by
  simp only [highParam]
  ring

/-- `β_H` is nonnegative on the full high-density interval. -/
theorem betaHigh_nonneg {p : ℝ} (hp : (2 : ℝ) / 3 ≤ p) :
    0 ≤ betaHigh p := by
  have hx : 0 ≤ highParam p := highParam_nonneg hp
  have hp0 : 0 ≤ p := by linarith
  have hx2 : 0 ≤ highParam p ^ 2 := sq_nonneg _
  have hx3 : 0 ≤ highParam p ^ 3 := pow_nonneg hx _
  have hinner : 0 ≤ 30 * p ^ 3 - 29 * p ^ 2 + 6 * p + 1 := by
    have hid := betaHigh_inner p
    nlinarith
  exact mul_nonneg hp0 hinner

/-- The endpoint gap used when the rooted degree is zero. -/
def gapZeroHigh (p : ℝ) : ℝ := betaHigh p * p - target p

/-- The endpoint gap used when the rooted degree is one. -/
def gapOneHigh (p : ℝ) : ℝ :=
  p ^ 3 - target p - betaHigh p * (1 - p) - gammaHigh p * (p - 1)

lemma gapZeroHigh_identity (p : ℝ) :
    9 * gapZeroHigh p = p ^ 2 *
      (8 * highParam p ^ 3 + 28 * highParam p ^ 2
        + 19 * highParam p + 8) := by
  simp only [gapZeroHigh, betaHigh, target, highParam]
  ring

/-- The degree-zero endpoint gap is nonnegative in region H. -/
theorem gapZeroHigh_nonneg {p : ℝ} (hp : (2 : ℝ) / 3 ≤ p) :
    0 ≤ gapZeroHigh p := by
  have hx : 0 ≤ highParam p := highParam_nonneg hp
  have hp0 : 0 ≤ p := by linarith
  have hpoly : 0 ≤ 8 * highParam p ^ 3 + 28 * highParam p ^ 2
      + 19 * highParam p + 8 := by positivity
  have hid := gapZeroHigh_identity p
  have hp2 : 0 ≤ p ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hp2 hpoly]

lemma gapOneHigh_identity (p : ℝ) :
    81 * gapOneHigh p =
      (highParam p - 1) ^ 2 * (highParam p + 2) *
        (8 * highParam p ^ 2 + 12 * highParam p + 7) := by
  simp only [gapOneHigh, betaHigh, gammaHigh, target, highParam]
  ring

/-- The degree-one endpoint gap is nonnegative in region H. -/
theorem gapOneHigh_nonneg {p : ℝ} (hp : (2 : ℝ) / 3 ≤ p) :
    0 ≤ gapOneHigh p := by
  have hx : 0 ≤ highParam p := highParam_nonneg hp
  have hfirst : 0 ≤ (highParam p - 1) ^ 2 := sq_nonneg _
  have hsecond : 0 ≤ highParam p + 2 := by linarith
  have hthird : 0 ≤ 8 * highParam p ^ 2 + 12 * highParam p + 7 := by
    positivity
  have hprod : 0 ≤ (highParam p - 1) ^ 2 * (highParam p + 2) *
      (8 * highParam p ^ 2 + 12 * highParam p + 7) := by positivity
  have hid := gapOneHigh_identity p
  nlinarith

/-- At the low endpoint of region H the coefficients agree with the transition
certificate. -/
theorem high_join_coefficients :
    betaHigh ((2 : ℝ) / 3) = (2 : ℝ) / 3 ∧
      gammaHigh ((2 : ℝ) / 3) = (4 : ℝ) / 9 := by
  constructor <;> norm_num [betaHigh, gammaHigh]

end Taeyoung.Methods.Atlas126
