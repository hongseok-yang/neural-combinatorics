import Taeyoung.Methods.Atlas126.Signs

/-! The junction interior can only be feasible for degree at least `5/8`.
This removes an entire interval before any finite certificate is generated. -/

namespace Taeyoung.Methods.Atlas126

theorem gammaJ_lower {x : ℝ} (hx0 : (15/16 : ℝ) ≤ x) (hx1 : x ≤ 1) :
    (5/16 : ℝ) ≤ gammaJ x := by
  let r := 1-x
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hr1 : r ≤ (1/16 : ℝ) := by dsimp [r]; linarith
  have hr2 : r^2 ≤ (1/256 : ℝ) := by nlinarith
  have hr4 : 0 ≤ r^4 := pow_nonneg hr0 4
  have hr6 : r^6 ≤ r^4 := by
    have := mul_le_mul_of_nonneg_left (show r^2 ≤ 1 by linarith) hr4
    nlinarith only [this]
  have heq : gammaJ x = 4/9 - (266/9)*r^2 + (4/9)*r^4 - r^6/12 := by
    dsimp [gammaJ, gammaHigh, lowDensity, r]
    ring
  nlinarith only [heq, hr2, hr4, hr6]

theorem junctionInterior_degree_lower {x d t : ℝ}
    (hx0 : (15/16 : ℝ) ≤ x) (hx1 : x ≤ 1) (hd1 : d ≤ 1)
    (hc : 0 ≤ t*(lowDensity x-t)-(1-d)*gammaJ x) :
    (5/8 : ℝ) ≤ d := by
  have hg := gammaJ_lower hx0 hx1
  have hp := lowDensity_mem (by linarith : 0 ≤ x) hx1
  have hp2 : (lowDensity x)^2 ≤ (4/9 : ℝ) := by nlinarith [hp.1, hp.2]
  have ht : t*(lowDensity x-t) ≤ (lowDensity x)^2/4 := by
    nlinarith only [sq_nonneg (t-lowDensity x/2)]
  have hmul := mul_le_mul_of_nonneg_right hg (show 0 ≤ 1-d by linarith)
  nlinarith only [hp2, ht, hc, hmul]

end Taeyoung.Methods.Atlas126
