import Taeyoung.Methods.Atlas126.Junction
import Taeyoung.Methods.Atlas126.Plane
import Taeyoung.Methods.Atlas126.InteriorCutoff

/-! Parameterize the interior by the slack in the upper-vertex constraint.
This removes the curved feasible boundary from the numerical certificate. -/

namespace Taeyoung.Methods.Atlas126

noncomputable def slackPolynomial (p C beta gamma lam g s t : ℝ) : ℝ :=
  let l := gamma-t*(p-t)
  let q := C-beta*p+(gamma+lam)*t-lam*g
  4*gamma^2*t^4-(l+s)*(gamma-l-s)*gamma^2-
    4*gamma*t*(l+s)*q-4*beta*t*(l+s)^2+4*t*(l+s)^3

theorem slackPolynomial_identity (p C beta gamma lam g d t : ℝ) :
    slackPolynomial p C beta gamma lam g (t*(p-t)-(1-d)*gamma) t =
      gamma^2*interiorPolynomial p C beta gamma lam g d t := by
  dsimp only [slackPolynomial,interiorPolynomial]
  ring

noncomputable def junctionSlackTarget (r s t : ℝ) : ℝ :=
  slackPolynomial (lowDensity (1-r)) (target (lowDensity (1-r)))
    (betaJ (1-r)) (gammaJ (1-r)) (lambdaJ (1-r)) (lowTriangle (1-r)) s t

theorem junctionInterior_of_slack
    (h : ∀ {r s t : ℝ}, 0 ≤ r → r ≤ (1/16 : ℝ) →
      0 ≤ s → s ≤ (1/9 : ℝ) → 0 ≤ t → t ≤ 1 → 0 ≤ junctionSlackTarget r s t)
    {x d u : ℝ} (hx0 : (15/16 : ℝ) ≤ x) (hx1 : x ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hc : 0 ≤ junctionInteriorConstraint1 x d u) :
    0 ≤ junctionInteriorTarget x d u := by
  let t := d^2*u
  let s := t*(lowDensity x-t)-(1-d)*gammaJ x
  have hg := gammaJ_lower hx0 hx1
  have hp := lowDensity_mem (by linarith : 0 ≤ x) hx1
  have hp2 : (lowDensity x)^2 ≤ (4/9 : ℝ) := by nlinarith [hp.1,hp.2]
  have hd2 : d^2 ≤ 1 := by nlinarith
  have ht0 : 0 ≤ t := mul_nonneg (sq_nonneg d) hu0
  have ht1 : t ≤ 1 := (mul_le_of_le_one_right (sq_nonneg d) hu1).trans hd2
  have hs0 : 0 ≤ s := hc
  have hgap : 0 ≤ (1-d)*gammaJ x := mul_nonneg (by linarith) (by linarith)
  have hs1 : s ≤ (1/9 : ℝ) := by
    dsimp only [s]
    nlinarith only [hp2,hgap,sq_nonneg (t-lowDensity x/2)]
  have hb := h (by linarith : 0 ≤ 1-x) (by linarith : 1-x ≤ (1/16 : ℝ))
    hs0 hs1 ht0 ht1
  have hid : junctionSlackTarget (1-x) s t = (gammaJ x)^2*junctionInteriorTarget x d u := by
    dsimp only [junctionSlackTarget]
    rw [show 1-(1-x) = x by ring]
    dsimp only [s]
    rw [slackPolynomial_identity]
    rfl
  rw [hid] at hb
  exact nonneg_of_mul_nonneg_right hb (sq_pos_of_pos (by linarith : 0 < gammaJ x))

end Taeyoung.Methods.Atlas126
