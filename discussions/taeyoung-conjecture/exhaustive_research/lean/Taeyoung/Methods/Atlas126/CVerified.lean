import Taeyoung.Methods.Atlas126.SlackPlane
import Taeyoung.Methods.Atlas126.LowPlaneSigns
import Taeyoung.Methods.Atlas126.Cert.LowC1
import Taeyoung.Methods.Atlas126.Cert.LowC2
import Taeyoung.Methods.Atlas126.Cert.LowCS

namespace Taeyoung.Methods.Atlas126

theorem polynomialPlaneC {x : ℝ} (hx0 : (5/8 : ℝ) ≤ x) (hx1 : x ≤ (15/16 : ℝ)) :
    PolynomialPlane (lowDensity x) (target (lowDensity x))
      (betaC x) (gammaC x) (lambdaC x) (lowTriangle x) := by
  have hp2 := lowDensity_sq_le (by linarith : 0 ≤ x) (by linarith : x ≤ 1)
  have hg : 0 < gammaC x := by have h := gammaC_lower hx0 hx1; linarith
  apply polynomialPlane_of_upper_and_slack (lowDensity x) (target (lowDensity x))
    (betaC x) (gammaC x) (lambdaC x) (lowTriangle x) hp2 hg
  · exact junctionFaceC1 hx0 hx1
  · exact junctionFaceC2 hx0 hx1
  · exact junctionFaceCS hx0 hx1
  · intro d a t hd0 hd1 haLower htLower htA
    exact scalarResidual_highDegreeC hx0 hx1 hd0 hd1 haLower htLower htA

end Taeyoung.Methods.Atlas126
