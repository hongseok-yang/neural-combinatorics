import Taeyoung.Methods.Atlas126.SlackPlane
import Taeyoung.Methods.Atlas126.LowPlaneSigns
import Taeyoung.Methods.Atlas126.Cert.Junction1
import Taeyoung.Methods.Atlas126.Cert.Junction2
import Taeyoung.Methods.Atlas126.Cert.JunctionSlack

/-! The complete scalar supporting plane on the junction interval.
This is a component of Atlas126, not the full graphon/catalogue theorem. -/

namespace Taeyoung.Methods.Atlas126

theorem polynomialPlaneJ {x : ℝ} (hx0 : (15/16 : ℝ) ≤ x) (hx1 : x ≤ 1) :
    PolynomialPlane (lowDensity x) (target (lowDensity x))
      (betaJ x) (gammaJ x) (lambdaJ x) (lowTriangle x) := by
  have hp2 := lowDensity_sq_le (by linarith : 0 ≤ x) hx1
  have hg : 0 < gammaJ x := by have h := gammaJ_lower hx0 hx1; linarith
  apply polynomialPlane_of_upper_and_slack (lowDensity x) (target (lowDensity x))
    (betaJ x) (gammaJ x) (lambdaJ x) (lowTriangle x) hp2 hg
  · intro d u hd0 hd1 hu0 hu1 hc0 hc1 _hc2
    exact junctionFace1 hx0 hx1 hd0 hd1 hu0 hu1 hc0 hc1
  · intro d u hd0 hd1 hu0 hu1 hc0 _hc1
    exact junctionFace2 hx0 hx1 hd0 hd1 hu0 hu1 hc0
  · intro s t hs0 hs1 ht0 ht1
    have h := junctionSlack_nonneg (by linarith : 0 ≤ 1-x)
      (by linarith : 1-x ≤ (1/16 : ℝ)) hs0 hs1 ht0 ht1
    simpa only [junctionSlackTarget,sub_sub_cancel] using h
  · intro d a t hd0 hd1 haLower htLower htA
    exact scalarResidual_highDegreeJ hx0 hx1 hd0 hd1 haLower htLower htA

end Taeyoung.Methods.Atlas126
