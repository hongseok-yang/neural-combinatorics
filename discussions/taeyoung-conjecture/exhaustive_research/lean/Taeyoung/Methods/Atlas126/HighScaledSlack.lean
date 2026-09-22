import Taeyoung.Methods.Atlas126.JunctionPlane
import Taeyoung.Methods.Atlas126.Corners

namespace Taeyoung.Methods.Atlas126

noncomputable def highDensityParameter (x : ℝ) : ℝ := (2+x)/3

noncomputable def highGammaReduced (p : ℝ) : ℝ := 2*(9*p^2-10*p+3)

theorem highGammaReduced_pos (p : ℝ) : 0 < highGammaReduced p := by
  have h := quad_pos p
  dsimp only [highGammaReduced]
  linarith

theorem gammaHigh_reduced (p : ℝ) : gammaHigh p = p*highGammaReduced p := by
  dsimp only [gammaHigh,highGammaReduced]
  ring

noncomputable def highSlackPolynomial (p s u : ℝ) : ℝ :=
  let g := highGammaReduced p
  let b := 30*p^3-29*p^2+6*p+1
  let c := (2*p-1)*(p^3+(1-p)^3)
  let l := g-p*u*(1-u)
  let q := c-b+g*u
  4*p^2*g^2*u^4-(l+s)*(g-l-s)*g^2-
    4*p*g*u*(l+s)*q-4*b*u*(l+s)^2+4*u*(l+s)^3

noncomputable def highScaledSlackTarget (x s u : ℝ) : ℝ :=
  highSlackPolynomial (highDensityParameter x) s u

theorem highSlackPolynomial_identity (p d u : ℝ) :
    p^2*highSlackPolynomial p (p*u*(1-u)-(1-d)*highGammaReduced p) u =
      (highGammaReduced p)^2*
        interiorPolynomial p (target p) (betaHigh p) (gammaHigh p) 0 0 d (p*u) := by
  dsimp only [highSlackPolynomial,highGammaReduced,interiorPolynomial,target,betaHigh,gammaHigh]
  ring

/-- Scaling both the triangle coordinate and the feasibility slack by `p`
keeps the complete high-density certificate inside one fixed box. -/
theorem highInterior_of_slack
    (h : ∀ {x s u : ℝ}, 0 ≤ x → x ≤ 1 → 0 ≤ s → s ≤ (1/4 : ℝ) →
      0 ≤ u → u ≤ 1 → 0 ≤ highScaledSlackTarget x s u)
    {x d t : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hd1 : d ≤ 1)
    (ht0 : 0 ≤ t) (htp : t ≤ highDensityParameter x)
    (hc : 0 ≤ t*(highDensityParameter x-t)-(1-d)*gammaHigh (highDensityParameter x)) :
    0 ≤ interiorPolynomial (highDensityParameter x) (target (highDensityParameter x))
      (betaHigh (highDensityParameter x)) (gammaHigh (highDensityParameter x)) 0 0 d t := by
  let p := highDensityParameter x
  have hp0 : 0 < p := by dsimp [p,highDensityParameter]; linarith
  have hp1 : p ≤ 1 := by dsimp [p,highDensityParameter]; linarith
  have hg := highGammaReduced_pos p
  obtain ⟨u,hu0,hu1,hu⟩ := exists_unit_scale hp0.le ht0 htp
  let s := p*u*(1-u)-(1-d)*highGammaReduced p
  have hid : p*s = t*(p-t)-(1-d)*gammaHigh p := by
    rw [← hu,gammaHigh_reduced]
    dsimp only [s]
    ring
  have hs0 : 0 ≤ s := nonneg_of_mul_nonneg_right (by rw [hid]; exact hc) hp0
  have hgap : 0 ≤ (1-d)*highGammaReduced p := mul_nonneg (by linarith) hg.le
  have hunit : u*(1-u) ≤ (1/4 : ℝ) := by nlinarith only [sq_nonneg (u-1/2)]
  have hm := mul_le_mul_of_nonneg_left hunit hp0.le
  have hs1 : s ≤ (1/4 : ℝ) := by dsimp only [s]; nlinarith only [hm,hgap,hp1]
  have hb := mul_nonneg (sq_nonneg p) (h hx0 hx1 hs0 hs1 hu0 hu1)
  change 0 ≤ p^2*highSlackPolynomial p s u at hb
  dsimp only [s] at hb
  rw [highSlackPolynomial_identity,hu] at hb
  exact nonneg_of_mul_nonneg_right hb (sq_pos_of_pos hg)

end Taeyoung.Methods.Atlas126
