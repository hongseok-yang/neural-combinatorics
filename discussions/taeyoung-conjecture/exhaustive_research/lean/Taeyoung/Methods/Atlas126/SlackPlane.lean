import Taeyoung.Methods.Atlas126.JunctionPlane
import Taeyoung.Methods.Atlas126.JunctionSlack

namespace Taeyoung.Methods.Atlas126

theorem interiorPolynomial_nonneg_of_slack
    (p C beta gamma lam g d t : ℝ) (hp : p^2 ≤ (4/9 : ℝ)) (hg : 0 < gamma)
    (hd : d ≤ 1) (hc : 0 ≤ t*(p-t)-(1-d)*gamma)
    (h : ∀ s : ℝ, 0 ≤ s → s ≤ (1/9 : ℝ) →
      0 ≤ slackPolynomial p C beta gamma lam g s t) :
    0 ≤ interiorPolynomial p C beta gamma lam g d t := by
  have hgap : 0 ≤ (1-d)*gamma := mul_nonneg (by linarith) hg.le
  have hs1 : t*(p-t)-(1-d)*gamma ≤ (1/9 : ℝ) := by
    nlinarith only [hp,hgap,sq_nonneg (t-p/2)]
  have hb := h _ hc hs1
  rw [slackPolynomial_identity] at hb
  exact nonneg_of_mul_nonneg_right hb (sq_pos_of_pos hg)

/-- The compact certificate interface: selected boundary faces and a box in
interior slack coordinates. All zero cases are included. -/
theorem polynomialPlane_of_scaled_certificates
    (p C beta gamma lam g : ℝ) (hp : p^2 ≤ (4/9 : ℝ)) (hg : 0 < gamma)
    (h1 : ∀ {d u : ℝ}, 0 ≤ d → d ≤ (15/16 : ℝ) → 0 ≤ u → u ≤ 1 →
      0 ≤ d-(d^2*u+p)/2 → 0 ≤ (d^2*u+p)/2-(d+p-1) →
      0 ≤ (1-d)*gamma-(d^2*u)*(p-d^2*u) →
      0 ≤ scalarResidual p C beta gamma lam g d ((d^2*u+p)/2) (d^2*u))
    (h2 : ∀ {d u : ℝ}, 0 ≤ d → d ≤ (15/16 : ℝ) → 0 ≤ u → u ≤ 1 →
      0 ≤ (d^2*u+p)/2-d → 0 ≤ (1-d)*gamma-2*(d^2*u)*(d-d^2*u) →
      0 ≤ scalarResidual p C beta gamma lam g d d (d^2*u))
    (h4 : ∀ {d u : ℝ}, 0 ≤ d → d ≤ (15/16 : ℝ) → 0 ≤ u → u ≤ 1 →
      0 ≤ d+p-1 → 0 ≤ d^2-(d+p-1)*u → 0 ≤ ((d+p-1)*u+p)/2-(d+p-1) →
      0 ≤ 2*((d+p-1)*u)*(d+p-1-(d+p-1)*u)-(1-d)*gamma →
      0 ≤ scalarResidual p C beta gamma lam g d (d+p-1) ((d+p-1)*u))
    (hS : ∀ {s t : ℝ}, 0 ≤ s → s ≤ (1/9 : ℝ) → 0 ≤ t → t ≤ 1 →
      0 ≤ slackPolynomial p C beta gamma lam g s t)
    (hHigh : ∀ d a t : ℝ, (15/16 : ℝ) ≤ d → d ≤ 1 →
      d+p-1 ≤ a → 2*a-p ≤ t → t ≤ a → 0 ≤ scalarResidual p C beta gamma lam g d a t) :
    PolynomialPlane p C beta gamma lam g := by
  apply scalarPlane_of_four_candidates p C beta gamma lam g (15/16) hg.le
  · intro d t hd0 hd1 ht0 htD hdUpper hSelected
    obtain ⟨u,hu0,hu1,hu⟩ := exists_unit_scale (sq_nonneg d) ht0 htD
    have hc0 : 0 ≤ (d^2*u+p)/2-d := by rw [hu]; linarith only [hdUpper]
    have hc1 : 0 ≤ (1-d)*gamma-2*(d^2*u)*(d-d^2*u) := by
      rw [hu]
      nlinarith only [hSelected]
    simpa only [hu] using h2 hd0 hd1 hu0 hu1 hc0 hc1
  · intro d t hd0 hd1 ht0 htD hUpperD hLowerUpper hSelected
    obtain ⟨u,hu0,hu1,hu⟩ := exists_unit_scale (sq_nonneg d) ht0 htD
    have hc0 : 0 ≤ d-(d^2*u+p)/2 := by rw [hu]; linarith only [hUpperD]
    have hc1 : 0 ≤ (d^2*u+p)/2-(d+p-1) := by rw [hu]; linarith only [hLowerUpper]
    have hc2 : 0 ≤ (1-d)*gamma-(d^2*u)*(p-d^2*u) := by
      rw [hu]
      nlinarith only [hSelected]
    simpa only [hu] using h1 hd0 hd1 hu0 hu1 hc0 hc1 hc2
  · intro d t hd0 hd1 ht0 htD htLower hLowerD hLowerUpper hSelected
    obtain ⟨u,hu0,hu1,hu⟩ := exists_unit_scale (ht0.trans htLower) ht0 htLower
    have hc0 : 0 ≤ d+p-1 := ht0.trans htLower
    have hc1 : 0 ≤ d^2-(d+p-1)*u := by rw [hu]; linarith only [htD]
    have hc2 : 0 ≤ ((d+p-1)*u+p)/2-(d+p-1) := by rw [hu]; linarith only [hLowerUpper]
    have hc3 : 0 ≤ 2*((d+p-1)*u)*(d+p-1-(d+p-1)*u)-(1-d)*gamma := by
      simpa only [hu] using hSelected
    simpa only [hu] using h4 hd0 hd1 hu0 hu1 hc0 hc1 hc2 hc3
  · intro d t hd0 hd1 htPos htD _hi0 hi1 _hi2
    have hdOne : d ≤ 1 := by linarith
    have hd2 : d^2 ≤ 1 := by nlinarith only [hd0,hdOne]
    apply interiorPolynomial_nonneg_of_slack p C beta gamma lam g d t hp hg hdOne hi1
    intro s hs0 hs1
    exact hS hs0 hs1 htPos.le (htD.trans hd2)
  · intro d a t hd0 hd1 _ha0 haLower _haD _ht0 htLower htA _htD
    exact hHigh d a t hd0 hd1 haLower htLower htA

theorem scalarResidual_nonneg_of_interiorPolynomial
    (p C beta gamma lam g d a t : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (ht : 0 < t)
    (h : 0 ≤ interiorPolynomial p C beta gamma lam g d t) :
    0 ≤ scalarResidual p C beta gamma lam g d a t := by
  have hv : 0 ≤ scalarResidual p C beta gamma lam g d (scalarVertex gamma d t) t := by
    have hm : 0 ≤ 4*t*scalarResidual p C beta gamma lam g d (scalarVertex gamma d t) t := by
      rw [interiorPolynomial_identity p C beta gamma lam g d t ht.ne']
      exact mul_nonneg (by linarith) h
    exact nonneg_of_mul_nonneg_right hm (by positivity : 0 < 4*t)
  rw [scalarResidual_vertex_identity p C beta gamma lam g d a t ht.ne']
  exact add_nonneg hv (by positivity)

/-- The slack estimate is stronger than the interior candidate requires. On
the selected lower boundary the upper-vertex slack is nonnegative too, so
no separate lower-boundary numerical certificate is needed. -/
theorem polynomialPlane_of_upper_and_slack
    (p C beta gamma lam g : ℝ) (hp : p^2 ≤ (4/9 : ℝ)) (hg : 0 < gamma)
    (h1 : ∀ {d u : ℝ}, 0 ≤ d → d ≤ (15/16 : ℝ) → 0 ≤ u → u ≤ 1 →
      0 ≤ d-(d^2*u+p)/2 → 0 ≤ (d^2*u+p)/2-(d+p-1) →
      0 ≤ (1-d)*gamma-(d^2*u)*(p-d^2*u) →
      0 ≤ scalarResidual p C beta gamma lam g d ((d^2*u+p)/2) (d^2*u))
    (h2 : ∀ {d u : ℝ}, 0 ≤ d → d ≤ (15/16 : ℝ) → 0 ≤ u → u ≤ 1 →
      0 ≤ (d^2*u+p)/2-d → 0 ≤ (1-d)*gamma-2*(d^2*u)*(d-d^2*u) →
      0 ≤ scalarResidual p C beta gamma lam g d d (d^2*u))
    (hS : ∀ {s t : ℝ}, 0 ≤ s → s ≤ (1/9 : ℝ) → 0 ≤ t → t ≤ 1 →
      0 ≤ slackPolynomial p C beta gamma lam g s t)
    (hHigh : ∀ d a t : ℝ, (15/16 : ℝ) ≤ d → d ≤ 1 →
      d+p-1 ≤ a → 2*a-p ≤ t → t ≤ a → 0 ≤ scalarResidual p C beta gamma lam g d a t) :
    PolynomialPlane p C beta gamma lam g := by
  apply polynomialPlane_of_scaled_certificates p C beta gamma lam g hp hg h1 h2 ?_ hS hHigh
  intro d u hd0 hd1 hu0 hu1 hc0 hc1 hc2 hc3
  let a := d+p-1
  let t := a*u
  have hdOne : d ≤ 1 := by linarith
  have hd2 : d^2 ≤ 1 := by nlinarith only [hd0,hdOne]
  have ht0 : 0 ≤ t := mul_nonneg hc0 hu0
  have ht1 : t ≤ 1 := by dsimp only [t,a]; linarith only [hc1,hd2]
  change 0 ≤ (t+p)/2-a at hc2
  change 0 ≤ 2*t*(a-t)-(1-d)*gamma at hc3
  have hgap : 0 < (1-d)*gamma := mul_pos (by linarith) hg
  have ht : 0 < t := by
    by_contra hn
    have hz : t = 0 := le_antisymm (le_of_not_gt hn) ht0
    rw [hz] at hc3
    nlinarith only [hc3,hgap]
  have hprod := mul_nonneg ht0 (show 0 ≤ t+p-2*a by linarith only [hc2])
  have hs : 0 ≤ t*(p-t)-(1-d)*gamma := by nlinarith only [hc3,hprod]
  have hpoly := interiorPolynomial_nonneg_of_slack p C beta gamma lam g d t hp hg hdOne hs
    (fun s hs0 hs1 => hS hs0 hs1 ht0 ht1)
  exact scalarResidual_nonneg_of_interiorPolynomial p C beta gamma lam g d a t hd0 hdOne ht hpoly

/-- A strong interior estimate eliminates the lower face altogether. Keeping
`t ≤ p` in the boundary interfaces permits compact exact parameterizations. -/
theorem polynomialPlane_of_upper_and_interior
    (p C beta gamma lam g limit : ℝ) (hgamma : 0 ≤ gamma)
    (hD : ∀ d t : ℝ, 0 ≤ d → d ≤ limit → 0 ≤ t → t ≤ d^2 → t ≤ p →
      d ≤ (t+p)/2 → 0 ≤ gamma*(1-d)-2*t*(d-t) →
      0 ≤ scalarResidual p C beta gamma lam g d d t)
    (hUpper : ∀ d t : ℝ, 0 ≤ d → d ≤ limit → 0 ≤ t → t ≤ d^2 → t ≤ p →
      (t+p)/2 ≤ d → d+p-1 ≤ (t+p)/2 →
      0 ≤ gamma*(1-d)-t*(p-t) →
      0 ≤ scalarResidual p C beta gamma lam g d ((t+p)/2) t)
    (hInterior : ∀ d t : ℝ, 0 ≤ d → d ≤ limit → d ≤ 1 → 0 < t → t ≤ d^2 → t ≤ p →
      0 ≤ t*(p-t)-(1-d)*gamma → 0 ≤ interiorPolynomial p C beta gamma lam g d t)
    (hHigh : ∀ d a t : ℝ, limit ≤ d → d ≤ 1 →
      0 ≤ a → d+p-1 ≤ a → a ≤ d →
      0 ≤ t → 2*a-p ≤ t → t ≤ a → t ≤ d^2 →
      0 ≤ scalarResidual p C beta gamma lam g d a t) :
    PolynomialPlane p C beta gamma lam g := by
  rw [scalarPlane_iff_residual]
  intro d a t hd0 hd1 ha0 haLower haD ht0 htLower htA htD
  have htp : t ≤ p := by linarith only [htLower,htA]
  have haT : a ≤ (t+p)/2 := by linarith only [htLower]
  rcases le_total d limit with hdLimit | hLimitD
  · by_cases ht : t = 0
    · subst t
      have hSelected : 0 ≤ gamma*(1-d) := mul_nonneg hgamma (by linarith)
      rcases le_total d ((0+p)/2) with hdP | hPd
      · exact (hD d 0 hd0 hdLimit le_rfl htD htp hdP (by simpa using hSelected)).trans
          (scalarResidual_zero_mono p C beta gamma lam g d a d hd0 hd1 hgamma haD)
      · exact (hUpper d 0 hd0 hdLimit le_rfl htD htp hPd (haLower.trans haT)
          (by simpa using hSelected)).trans
          (scalarResidual_zero_mono p C beta gamma lam g d a ((0+p)/2) hd0 hd1 hgamma haT)
    · have htPos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
      by_cases hs : 0 ≤ t*(p-t)-(1-d)*gamma
      · exact scalarResidual_nonneg_of_interiorPolynomial p C beta gamma lam g d a t
          hd0 hd1 htPos (hInterior d t hd0 hdLimit hd1 htPos htD htp hs)
      · have hSel : 0 ≤ gamma*(1-d)-t*(p-t) := by linarith only [hs]
        have hv : (t+p)/2 ≤ scalarVertex gamma d t := by
          have hdiv : (t+p)/2-t ≤ gamma*(1-d)/(2*t) := by
            apply (le_div_iff₀ (show 0 < 2*t by positivity)).mpr
            nlinarith only [hSel]
          dsimp only [scalarVertex]
          linarith only [hdiv]
        rcases le_total d ((t+p)/2) with hdT | hTd
        · have hm := mul_le_mul_of_nonneg_left hdT ht0
          have hDsel : 0 ≤ gamma*(1-d)-2*t*(d-t) := by nlinarith only [hSel,hm]
          exact (hD d t hd0 hdLimit ht0 htD htp hdT hDsel).trans
            (scalarResidual_mono_left p C beta gamma lam g d t a d hd0 htPos haD (hdT.trans hv))
        · exact (hUpper d t hd0 hdLimit ht0 htD htp hTd (haLower.trans haT) hSel).trans
            (scalarResidual_mono_left p C beta gamma lam g d t a ((t+p)/2) hd0 htPos haT hv)
  · exact hHigh d a t hLimitD hd1 ha0 haLower haD ht0 htLower htA htD

end Taeyoung.Methods.Atlas126
