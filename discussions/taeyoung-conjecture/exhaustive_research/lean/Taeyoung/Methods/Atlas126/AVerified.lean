import Taeyoung.Methods.Atlas126.SlackPlane
import Taeyoung.Methods.Atlas126.LowPlaneSigns
import Taeyoung.Methods.Atlas126.Cert.LowA1
import Taeyoung.Methods.Atlas126.Cert.LowA2
import Taeyoung.Methods.Atlas126.Cert.LowARootSlack

namespace Taeyoung.Methods.Atlas126

theorem polynomialPlaneA {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ (5/8 : ℝ)) :
    PolynomialPlane (lowDensity x) (target (lowDensity x))
      (betaA x) (gammaA x) (lambdaA x) (lowTriangle x) := by
  have hxOne : x ≤ 1 := by linarith
  apply polynomialPlane_of_upper_and_interior (lowDensity x) (target (lowDensity x))
    (betaA x) (gammaA x) (lambdaA x) (lowTriangle x) (15/16) (gammaA_pos hx0 hxOne).le
  · intro d t hd0 hd1 ht0 htD _htp hdUpper hSelected
    obtain ⟨u,hu0,hu1,hu⟩ := exists_unit_scale (sq_nonneg d) ht0 htD
    have hc0 : 0 ≤ aFace2Constraint0 x d u := by
      dsimp only [aFace2Constraint0]
      rw [hu]
      linarith only [hdUpper]
    have hc1 : 0 ≤ aFace2Constraint1 x d u := by
      dsimp only [aFace2Constraint1]
      rw [hu]
      nlinarith only [hSelected]
    simpa only [aFace2Target,hu] using junctionFaceA2 hx0 hx1 hd0 hd1 hu0 hu1 hc0 hc1
  · intro d t hd0 hd1 ht0 htD _htp hUpperD hLowerUpper hSelected
    obtain ⟨u,hu0,hu1,hu⟩ := exists_unit_scale (sq_nonneg d) ht0 htD
    have hc0 : 0 ≤ aFace1Constraint0 x d u := by
      dsimp only [aFace1Constraint0]
      rw [hu]
      linarith only [hUpperD]
    have hc1 : 0 ≤ aFace1Constraint1 x d u := by
      dsimp only [aFace1Constraint1]
      rw [hu]
      linarith only [hLowerUpper]
    have hc2 : 0 ≤ aFace1Constraint2 x d u := by
      dsimp only [aFace1Constraint2]
      rw [hu]
      nlinarith only [hSelected]
    simpa only [aFace1Target,hu] using junctionFaceA1 hx0 hx1 hd0 hd1 hu0 hu1 hc0 hc1 hc2
  · intro d t _hd0 _hdLimit hd1 ht0 _htD htp hc
    exact aInterior_of_root_slack (fun hx0 hx1 hs0 hs1 hu0 hu1 =>
      junctionFaceARS hx0 hx1 hs0 hs1 hu0 hu1) hx0 hx1 hd1 ht0.le htp hc
  · intro d a t hd0 hd1 _ha0 haLower _haD _ht0 htLower htA _htD
    exact scalarResidual_highDegreeA hx0 hx1 hd0 hd1 haLower htLower htA

end Taeyoung.Methods.Atlas126
