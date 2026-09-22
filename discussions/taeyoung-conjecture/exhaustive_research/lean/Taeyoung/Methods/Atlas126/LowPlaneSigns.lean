import Taeyoung.Methods.Atlas126.Signs

namespace Taeyoung.Methods.Atlas126

theorem lowDensity_sq_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (lowDensity x)^2 ≤ (4/9 : ℝ) := by
  have hp := lowDensity_mem hx0 hx1
  nlinarith [hp.1,hp.2]

theorem gammaA_pos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 < gammaA x := by
  have hp := (lowDensity_mem hx0 hx1).1
  dsimp only [gammaA,gammaLow]
  nlinarith [sq_nonneg (2*lowDensity x-1)]

theorem gammaC_lower {x : ℝ} (hx0 : (5/8 : ℝ) ≤ x) (hx1 : x ≤ (15/16 : ℝ)) :
    (1/8 : ℝ) ≤ gammaC x := by
  let v := (16*x-10)/5
  have hv0 : 0 ≤ v := by dsimp [v]; linarith
  have hv1 : 0 ≤ 1-v := by dsimp [v]; linarith
  have he : gammaC x-1/8 =
      (973/9216 : ℝ)*(1-v)^3+3*(10447/36864 : ℝ)*v*(1-v)^2+
      3*(419/4608 : ℝ)*v^2*(1-v)+(30553/147456 : ℝ)*v^3 := by
    dsimp only [gammaC,v]
    ring
  have hn : 0 ≤ gammaC x-1/8 := by rw [he]; positivity
  linarith

end Taeyoung.Methods.Atlas126
