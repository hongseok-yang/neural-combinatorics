import Taeyoung.Methods.Atlas126.HighCoverage
import Taeyoung.Methods.Atlas126.SlackPlane
import Taeyoung.Methods.Atlas126.Cert.HighD1
import Taeyoung.Methods.Atlas126.Cert.HighD2
import Taeyoung.Methods.Atlas126.Cert.HighTL
import Taeyoung.Methods.Atlas126.Cert.HighTH
import Taeyoung.Methods.Atlas126.Cert.HighLL
import Taeyoung.Methods.Atlas126.Cert.HighLH
import Taeyoung.Methods.Atlas126.Cert.HighRL
import Taeyoung.Methods.Atlas126.Cert.HighRH
import Taeyoung.Methods.Atlas126.Cert.HighSlack

set_option maxHeartbeats 2000000

namespace Taeyoung.Methods.Atlas126

theorem highUpperD_nonneg {p d t : ℝ} (hp0 : (2/3 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (ht0 : 0 ≤ t) (htD : t ≤ d^2)
    (hdT : d ≤ (t+p)/2) :
    0 ≤ scalarResidual p (target p) (betaHigh p) (gammaHigh p) 0 0 d d t := by
  apply highUpperD_cover (fun p d t =>
    0 ≤ scalarResidual p (target p) (betaHigh p) (gammaHigh p) 0 0 d d t) ?_ ?_
    hp0 hp1 hd0 hd1 ht0 htD hdT
  · intro x y z hx0 hx1 hy0 hy1 hz0 hz1
    have h := junctionFaceHD1 hx0 hx1 hy0 hy1 hz0 hz1
    have hn : 0 ≤ 1*highD1Target x y z := by simpa only [one_mul] using h
    rw [← highD1Identity] at hn
    convert hn using 1 <;> first | rfl | (dsimp only [scalarResidual,target,betaHigh,gammaHigh]; ring)
  · intro x y z hx0 hx1 hy0 hy1 hz0 hz1
    have h := junctionFaceHD2 hx0 hx1 hy0 hy1 hz0 hz1
    have hn := mul_nonneg (pow_nonneg hx0 3) h
    rw [← highD2Identity] at hn
    convert hn using 1 <;> first | rfl | (dsimp only [scalarResidual,target,betaHigh,gammaHigh]; ring)

theorem highUpperT_nonneg {p d t : ℝ} (hp0 : (2/3 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hd1 : d ≤ 1) (ht0 : 0 ≤ t) (htp : t ≤ p)
    (hTd : (t+p)/2 ≤ d) (hLower : d+p-1 ≤ (t+p)/2) :
    0 ≤ scalarResidual p (target p) (betaHigh p) (gammaHigh p) 0 0 d ((t+p)/2) t := by
  apply highUpperT_cover (fun p d t =>
    0 ≤ scalarResidual p (target p) (betaHigh p) (gammaHigh p) 0 0 d ((t+p)/2) t)
    ?_ ?_ ?_ ?_ ?_ ?_ hp0 hp1 hd1 ht0 htp hTd hLower
  · intro x y z hx0 hx1 hy0 hy1 hz0 hz1
    have h := junctionFaceHTL hx0 hx1 hy0 hy1 hz0 hz1
    have hn : 0 ≤ 1*highTLTarget x y z := by simpa only [one_mul] using h
    rw [← highTLIdentity] at hn
    convert hn using 1 <;> first | rfl | (dsimp only [scalarResidual,target,betaHigh,gammaHigh]; ring)
  · intro x y z hx0 hx1 hy0 hy1 hz0 hz1
    have h := junctionFaceHTH hx0 hx1 hy0 hy1 hz0 hz1
    have hn : 0 ≤ 1*highTHTarget x y z := by simpa only [one_mul] using h
    rw [← highTHIdentity] at hn
    convert hn using 1 <;> first | rfl | (dsimp only [scalarResidual,target,betaHigh,gammaHigh]; ring)
  · intro x y z hx0 hx1 hy0 hy1 hz0 hz1
    have h := junctionFaceHLL hx0 hx1 hy0 hy1 hz0 hz1
    have hn := mul_nonneg (pow_nonneg hx0 3) h
    rw [← highLLIdentity] at hn
    convert hn using 1 <;> first | rfl | (dsimp only [scalarResidual,target,betaHigh,gammaHigh]; ring)
  · intro x y z hx0 hx1 hy0 hy1 hz0 hz1
    have h := junctionFaceHLH hx0 hx1 hy0 hy1 hz0 hz1
    have hn := mul_nonneg (sq_nonneg x) h
    rw [← highLHIdentity] at hn
    convert hn using 1 <;> first | rfl | (dsimp only [scalarResidual,target,betaHigh,gammaHigh]; ring)
  · intro x y z hx0 hx1 hy0 hy1 hz0 hz1
    have h := junctionFaceHRL hx0 hx1 hy0 hy1 hz0 hz1
    have hn : 0 ≤ 1*highRLTarget x y z := by simpa only [one_mul] using h
    rw [← highRLIdentity] at hn
    convert hn using 1 <;> first | rfl | (dsimp only [scalarResidual,target,betaHigh,gammaHigh]; ring)
  · intro x y z hx0 hx1 hy0 hy1 hz0 hz1
    exact junctionFaceHR hx0 hx1 hy0 hy1 hz0 hz1

theorem polynomialPlaneHigh {p : ℝ} (hp0 : (2/3 : ℝ) ≤ p) (hp1 : p ≤ 1) :
    PolynomialPlane p (target p) (betaHigh p) (gammaHigh p) 0 0 := by
  apply polynomialPlane_of_upper_and_interior p (target p) (betaHigh p) (gammaHigh p) 0 0 1
    (gammaHigh_nonneg hp0)
  · intro d t hd0 hd1 ht0 htD _htp hdT _hSelected
    exact highUpperD_nonneg hp0 hp1 hd0 hd1 ht0 htD hdT
  · intro d t _hd0 hd1 ht0 _htD htp hTd hLower _hSelected
    exact highUpperT_nonneg hp0 hp1 hd1 ht0 htp hTd hLower
  · intro d t _hd0 _hdLimit hd1 ht0 _htD htp hc
    have hx0 : 0 ≤ 3*p-2 := by linarith
    have hx1 : 3*p-2 ≤ 1 := by linarith
    have hpx : highDensityParameter (3*p-2) = p := by dsimp only [highDensityParameter]; ring
    have h := highInterior_of_slack (fun hx0 hx1 hs0 hs1 hu0 hu1 =>
      junctionFaceHS hx0 hx1 hs0 hs1 hu0 hu1) hx0 hx1 hd1 ht0.le
      (by rwa [hpx]) (by rwa [hpx])
    rwa [hpx] at h
  · intro d a t hd0 hd1 _ha0 _haLower _haD ht0 _htLower _htA _htD
    have hd : d = 1 := le_antisymm hd1 hd0
    rw [hd]
    simp only [scalarResidual,sub_self,zero_mul,one_mul,mul_zero,zero_add,sub_zero]
    positivity

end Taeyoung.Methods.Atlas126
