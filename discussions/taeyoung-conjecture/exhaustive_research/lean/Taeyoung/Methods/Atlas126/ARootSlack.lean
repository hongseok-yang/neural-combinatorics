import Taeyoung.Methods.Atlas126.JunctionPlane

namespace Taeyoung.Methods.Atlas126

noncomputable def aGammaRoot (x : ℝ) : ℝ := (-4*x^2+8*x+3)/12

theorem gammaA_eq_root_sq (x : ℝ) : gammaA x = (aGammaRoot x)^2 := by
  dsimp only [gammaA,gammaLow,lowDensity,aGammaRoot]
  ring

theorem lowDensity_le_two_aGammaRoot {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    lowDensity x ≤ 2*aGammaRoot x := by
  have hs := mul_nonneg hx0 (show 0 ≤ 2-x by linarith)
  have he : 2*aGammaRoot x-lowDensity x = x*(2-x)/2 := by
    dsimp only [aGammaRoot,lowDensity]
    ring
  nlinarith only [hs,he]

theorem aGammaRoot_pos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 < aGammaRoot x := by
  have hp := (lowDensity_mem hx0 hx1).1
  have h := lowDensity_le_two_aGammaRoot hx0 hx1
  linarith

noncomputable def aRootSlackTarget (x s u : ℝ) : ℝ :=
  let p := lowDensity x
  let r := aGammaRoot x
  let rho := contactA x
  let v := 2*u
  let n := r*(1+s+v^2)-p*v
  4*r^4*v^4-n*(r-n)*r^2-
    4*n*v*(target p-2*r^2*rho*p-lambdaA x*lowTriangle x+
      (r^3+lambdaA x*r)*v+2*r*rho*n-n^2)

theorem aRootSlack_identity (x d s u : ℝ)
    (hn : aGammaRoot x*d = aGammaRoot x*(1+s+(2*u)^2)-lowDensity x*(2*u)) :
    aRootSlackTarget x s u =
      interiorPolynomial (lowDensity x) (target (lowDensity x))
        (betaA x) (gammaA x) (lambdaA x) (lowTriangle x) d (2*aGammaRoot x*u) := by
  dsimp only [aRootSlackTarget]
  rw [← hn]
  simp only [interiorPolynomial,betaA,gammaA_eq_root_sq]
  ring

/-- Since gammaA is a polynomial square, scaling the triangle coordinate by
its square root reduces the certificate degree from 18 to 12. -/
theorem aInterior_of_root_slack
    (h : ∀ {x s u : ℝ}, 0 ≤ x → x ≤ (5/8 : ℝ) → 0 ≤ s → s ≤ 1 →
      0 ≤ u → u ≤ 1 → 0 ≤ aRootSlackTarget x s u)
    {x d t : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ (5/8 : ℝ)) (hd1 : d ≤ 1)
    (ht0 : 0 ≤ t) (htp : t ≤ lowDensity x)
    (hc : 0 ≤ t*(lowDensity x-t)-(1-d)*gammaA x) :
    0 ≤ interiorPolynomial (lowDensity x) (target (lowDensity x))
      (betaA x) (gammaA x) (lambdaA x) (lowTriangle x) d t := by
  have hxOne : x ≤ 1 := by linarith
  let p := lowDensity x
  let r := aGammaRoot x
  have hr := aGammaRoot_pos hx0 hxOne
  have hpr := lowDensity_le_two_aGammaRoot hx0 hxOne
  have hp := lowDensity_mem hx0 hxOne
  have hp0 : 0 ≤ p := by dsimp only [p]; linarith only [hp.1]
  have hg : 0 < gammaA x := by rw [gammaA_eq_root_sq]; positivity
  have hpSq : p^2 ≤ 4*gammaA x := by
    have hpow := pow_le_pow_left₀ hp0 hpr 2
    rw [gammaA_eq_root_sq]
    nlinarith only [hpow]
  obtain ⟨u,hu0,hu1,hu⟩ := exists_unit_scale (show 0 ≤ 2*r by positivity) ht0 (htp.trans hpr)
  let s := t*(p-t)-(1-d)*gammaA x
  have hs0 : 0 ≤ s := hc
  have hgap : 0 ≤ (1-d)*gammaA x := mul_nonneg (by linarith) hg.le
  have hs1 : s ≤ gammaA x := by
    dsimp only [s]
    nlinarith only [hpSq,hgap,sq_nonneg (t-p/2)]
  obtain ⟨v,hv0,hv1,hv⟩ := exists_unit_scale hg.le hs0 hs1
  have hv' : r^2*v = (2*r*u)*(p-2*r*u)-(1-d)*r^2 := by
    dsimp only [s] at hv
    rw [gammaA_eq_root_sq,← hu] at hv
    exact hv
  have hn : r*d = r*(1+v+(2*u)^2)-p*(2*u) := by
    apply mul_left_cancel₀ (show r ≠ 0 from ne_of_gt hr)
    nlinarith only [hv']
  have hid := aRootSlack_identity x d v u hn
  rw [hu] at hid
  rw [← hid]
  exact h hx0 hx1 hv0 hv1 hu0 hu1

end Taeyoung.Methods.Atlas126
