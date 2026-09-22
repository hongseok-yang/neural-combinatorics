import Taeyoung.Methods.Atlas126.Coefficients
import Taeyoung.Methods.Atlas126.Corners
import Taeyoung.Methods.Bernstein.Box
import Taeyoung.Methods.Bernstein.Univariate

/-!
# Atlas 126: the region-A upper-face equality box

The residual has its only zero in this box at `(x,d,u) = (0,1/2,0)`.
At `u=0` it is a positive factor times a binary quadratic form in
`d-1/2` and `x`.  The quotient in the nonnegative `u` direction is
certified on the whole exceptional box by one small Bernstein table.
-/

set_option maxHeartbeats 2000000

open Finset

namespace Taeyoung.Methods.Atlas126

open Taeyoung.Methods.Bernstein

/-- The cleared residual on the first upper-`t` face of plane A. -/
noncomputable def upperTargetA (x d u : ℝ) : ℝ :=
  let t := d ^ 2 * u
  let a := (t + lowDensity x) / 2
  (1 - d) * t ^ 3 + d * t * (a - t) ^ 2 -
    d * (1 - d) *
      (target (lowDensity x) + betaA x * (d - lowDensity x) +
        gammaA x * (a - d ^ 2) + lambdaA x * (t - lowTriangle x))

private def qCoeff : ℕ → ℕ → ℕ → ℚ
  | 4, 4, 0 => 1/18
  | 4, 3, 0 => -7/144
  | 3, 4, 0 => -2/9
  | 3, 3, 0 => 7/36
  | 2, 5, 1 => 1/12
  | 2, 4, 0 => 5/36
  | 2, 3, 0 => -11/72
  | 1, 5, 1 => -1/6
  | 1, 4, 0 => 14/75
  | 1, 3, 0 => -31/300
  | 0, 7, 2 => -3/4
  | 0, 6, 2 => 1
  | 0, 5, 1 => -1/4
  | 0, 4, 0 => 3/32
  | 0, 3, 0 => -1/32
  | _, _, _ => 0

private theorem qCertificate :
    ∀ i ∈ range 5, ∀ j ∈ range 8, ∀ k ∈ range 3,
      0 ≤ trans3 qCoeff 4 7 2
        (0 : ℚ) (1/16 : ℚ) (15/32 : ℚ) (15/256 : ℚ)
        (0 : ℚ) (1/16 : ℚ) i j k := by
  decide +kernel

private theorem q_nonneg {x d u : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/16)
    (hd0 : 15/32 ≤ d) (hd1 : d ≤ 135/256)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/16) :
    0 ≤ msum qCoeff 4 7 2 x d u :=
  msum_nonneg_on_box qCoeff 4 7 2
    (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith) qCertificate

private noncomputable def aLocal (x : ℝ) : ℝ :=
  14400 * x ^ 4 - 57600 * x ^ 3 + 36000 * x ^ 2 + 43200 * x + 8100

private noncomputable def bLocal (x : ℝ) : ℝ :=
  -12000 * x ^ 4 + 48000 * x ^ 3 - 30000 * x ^ 2 - 36000 * x - 6750

private noncomputable def cLocal (x : ℝ) : ℝ :=
  100 * x ^ 8 - 1000 * x ^ 7 + 3400 * x ^ 6 - 5200 * x ^ 5 +
    5600 * x ^ 4 - 5000 * x ^ 3 - 5456 * x ^ 2 + 10461 * x + 2871

private def coeffAt (xs : List ℚ) (i : ℕ) : ℚ := xs.getD i 0

private def cCoeff : List ℚ :=
  [(2871 : ℚ), 10461, -5456, -5000, 5600, -5200, 3400, -1000, 100]

private theorem cCertificate :
    ∀ k ∈ range 9,
      0 ≤ trans (coeffAt cCoeff) 8 (0 : ℚ) (1/16 : ℚ) k := by
  decide +kernel

private theorem c_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1/16) :
    0 ≤ cLocal x := by
  have h := nonneg_on_interval_rat (coeffAt cCoeff) 8
    (l := (0 : ℚ)) (W := (1/16 : ℚ)) (x := x)
    (by norm_num) (by push_cast; linarith) (by push_cast; linarith) cCertificate
  simp only [coeffAt, cCoeff, Finset.sum_range_succ, Finset.sum_range_zero,
    List.getD_cons_zero, List.getD_cons_succ] at h
  push_cast at h
  simp only [cLocal]
  nlinarith

private def detCoeff : List ℚ :=
  [(47457900 : ℚ), 349045200, 343310400, -1771891200, -1319068800,
    3954816000, -2168265600, -619920000, 1696680000, -1209600000,
    440640000, -80640000, 5760000]

private theorem detCertificate :
    ∀ k ∈ range 13,
      0 ≤ trans (coeffAt detCoeff) 12 (0 : ℚ) (1/16 : ℚ) k := by
  decide +kernel

private theorem det_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1/16) :
    0 ≤ 4 * aLocal x * cLocal x - bLocal x ^ 2 := by
  have h := nonneg_on_interval_rat (coeffAt detCoeff) 12
    (l := (0 : ℚ)) (W := (1/16 : ℚ)) (x := x)
    (by norm_num) (by push_cast; linarith) (by push_cast; linarith) detCertificate
  simp only [coeffAt, detCoeff, Finset.sum_range_succ, Finset.sum_range_zero,
    List.getD_cons_zero, List.getD_cons_succ] at h
  push_cast at h
  simp only [aLocal, bLocal, cLocal]
  nlinarith

private theorem a_nonneg (x : ℝ) : 0 ≤ aLocal x := by
  have hs : 0 ≤ (4 * x ^ 2 - 8 * x - 3) ^ 2 := sq_nonneg _
  simp only [aLocal]
  nlinarith

private theorem target_zero_identity (x d : ℝ) :
    upperTargetA x d 0 = d * (1 - d) / 129600 *
      (aLocal x * (d - 1/2) ^ 2 +
        bLocal x * (d - 1/2) * x + cLocal x * x ^ 2) := by
  simp only [upperTargetA, target, lowDensity, lowTriangle, betaA, gammaA,
    gammaLow, contactA, lambdaA, aLocal, bLocal, cLocal]
  ring

private theorem target_decomposition (x d u : ℝ) :
    upperTargetA x d u = upperTargetA x d 0 + u * msum qCoeff 4 7 2 x d u := by
  simp only [upperTargetA, target, lowDensity, lowTriangle, betaA, gammaA,
    gammaLow, contactA, lambdaA, msum, qCoeff, Finset.sum_range_succ,
    Finset.sum_range_zero]
  push_cast
  ring

/-- The local theorem discharging the exceptional region-A upper-face box. -/
theorem upperTargetA_nonneg {x d u : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/16)
    (hd0 : 15/32 ≤ d) (hd1 : d ≤ 135/256)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/16) :
    0 ≤ upperTargetA x d u := by
  have hA := a_nonneg x
  have hC := c_nonneg hx0 hx1
  have hdetRaw := det_nonneg hx0 hx1
  have hdet : bLocal x ^ 2 ≤ 4 * aLocal x * cLocal x := by linarith
  have hquad := quadratic_nonneg hA hC hdet (d := d - 1/2) (t := x)
  have hzero : 0 ≤ upperTargetA x d 0 := by
    rw [target_zero_identity]
    have hd : 0 ≤ d := by linarith
    have hd' : 0 ≤ 1 - d := by linarith
    exact mul_nonneg (div_nonneg (mul_nonneg hd hd') (by norm_num)) hquad
  have hq := q_nonneg hx0 hx1 hd0 hd1 hu0 hu1
  rw [target_decomposition]
  exact add_nonneg hzero (mul_nonneg hu0 hq)

end Taeyoung.Methods.Atlas126
