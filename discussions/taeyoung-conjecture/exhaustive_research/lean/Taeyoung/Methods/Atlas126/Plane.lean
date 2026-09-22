import Taeyoung.Methods.Atlas126.Convex

/-! Assemble a scalar plane from three feasible boundary faces and one
interior polynomial. The face `a=t` is redundant when `gamma` is nonnegative.
All generated certificates can use this common interface. -/

namespace Taeyoung.Methods.Atlas126

noncomputable def interiorPolynomial
    (p C beta gamma lam g d t : ℝ) : ℝ :=
  4*t^4 - d*(1-d)*gamma^2 -
    4*d*t*(C + beta*(d-p) + gamma*(t-d^2) + lam*(t-g))

theorem interiorPolynomial_identity
    (p C beta gamma lam g d t : ℝ) (ht : t ≠ 0) :
    4*t*scalarResidual p C beta gamma lam g d (scalarVertex gamma d t) t =
      (1-d)*interiorPolynomial p C beta gamma lam g d t := by
  simp only [scalarResidual, scalarVertex, interiorPolynomial]
  field_simp
  ring

theorem scalarResidual_zero_mono
    (p C beta gamma lam g d a b : ℝ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hgamma : 0 ≤ gamma) (hab : a ≤ b) :
    scalarResidual p C beta gamma lam g d b 0 ≤
      scalarResidual p C beta gamma lam g d a 0 := by
  have h : 0 ≤ d*(1-d)*gamma*(b-a) :=
    mul_nonneg (mul_nonneg (mul_nonneg hd0 (by linarith)) hgamma) (sub_nonneg.mpr hab)
  dsimp [scalarResidual]
  nlinarith only [h]

/-- `limit` separates the finite box certificates from a separate estimate
near degree one. No certificate for the lower face `a=t` is required. -/
theorem scalarPlane_of_four_candidates
    (p C beta gamma lam g limit : ℝ) (hgamma : 0 ≤ gamma)
    (hD : ∀ d t : ℝ, 0 ≤ d → d ≤ limit → 0 ≤ t → t ≤ d^2 →
      d ≤ (t+p)/2 → 0 ≤ gamma*(1-d)-2*t*(d-t) →
      0 ≤ scalarResidual p C beta gamma lam g d d t)
    (hUpper : ∀ d t : ℝ, 0 ≤ d → d ≤ limit → 0 ≤ t → t ≤ d^2 →
      (t+p)/2 ≤ d → d+p-1 ≤ (t+p)/2 →
      0 ≤ gamma*(1-d)-t*(p-t) →
      0 ≤ scalarResidual p C beta gamma lam g d ((t+p)/2) t)
    (hLower : ∀ d t : ℝ, 0 ≤ d → d ≤ limit → 0 ≤ t → t ≤ d^2 →
      t ≤ d+p-1 → d+p-1 ≤ d → d+p-1 ≤ (t+p)/2 →
      0 ≤ 2*t*(d+p-1-t)-(1-d)*gamma →
      0 ≤ scalarResidual p C beta gamma lam g d (d+p-1) t)
    (hInterior : ∀ d t : ℝ, 0 ≤ d → d ≤ limit → 0 < t → t ≤ d^2 →
      0 ≤ 2*t*(d-t)-(1-d)*gamma →
      0 ≤ t*(p-t)-(1-d)*gamma →
      0 ≤ (1-d)*gamma-2*t*(d+p-1-t) →
      0 ≤ interiorPolynomial p C beta gamma lam g d t)
    (hHigh : ∀ d a t : ℝ, limit ≤ d → d ≤ 1 →
      0 ≤ a → d+p-1 ≤ a → a ≤ d →
      0 ≤ t → 2*a-p ≤ t → t ≤ a → t ≤ d^2 →
      0 ≤ scalarResidual p C beta gamma lam g d a t) :
    PolynomialPlane p C beta gamma lam g := by
  rw [scalarPlane_iff_residual]
  intro d a t hd0 hd1 ha0 haLower haD ht0 htLower htA htD
  rcases le_total d limit with hdLimit | hLimitD
  · by_cases ht : t = 0
    · subst t
      have hSelected : 0 ≤ gamma*(1-d) := mul_nonneg hgamma (by linarith)
      rcases le_total d ((0+p)/2) with hdP | hPd
      · exact (hD d 0 hd0 hdLimit le_rfl htD hdP (by simpa using hSelected)).trans
          (scalarResidual_zero_mono p C beta gamma lam g d a d hd0 hd1 hgamma haD)
      · have haP : a ≤ (0+p)/2 := by linarith
        exact (hUpper d 0 hd0 hdLimit le_rfl htD hPd (haLower.trans haP)
          (by simpa using hSelected)).trans
          (scalarResidual_zero_mono p C beta gamma lam g d a ((0+p)/2)
            hd0 hd1 hgamma haP)
    · have htPos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
      apply scalarResidual_nonneg_of_feasible_candidates
        p C beta gamma lam g d a t hd0 hd1 htPos hgamma haLower haD htLower htA
      · intro htL hLD hLU hvL
        have hv' : gamma*(1-d)/(2*t) ≤ d+p-1-t := by
          dsimp only [scalarVertex] at hvL
          linarith only [hvL]
        have hc := (div_le_iff₀ (show 0 < 2*t by positivity)).mp hv'
        exact hLower d t hd0 hdLimit ht0 htD htL hLD hLU (by nlinarith only [hc])
      · intro hdUpper hv
        have hv' : d-t ≤ gamma*(1-d)/(2*t) := by
          dsimp only [scalarVertex] at hv
          linarith only [hv]
        have hc := (le_div_iff₀ (show 0 < 2*t by positivity)).mp hv'
        exact hD d t hd0 hdLimit ht0 htD hdUpper (by nlinarith only [hc])
      · intro hUpperD hLowerUpper hv
        have hv' : (t+p)/2-t ≤ gamma*(1-d)/(2*t) := by
          dsimp only [scalarVertex] at hv
          linarith only [hv]
        have hc := (le_div_iff₀ (show 0 < 2*t by positivity)).mp hv'
        exact hUpper d t hd0 hdLimit ht0 htD hUpperD hLowerUpper (by nlinarith only [hc])
      · intro hvLower hvD hvP
        have hden : 0 < 2*t := by positivity
        have hvD' : gamma*(1-d)/(2*t) ≤ d-t := by
          dsimp only [scalarVertex] at hvD
          linarith only [hvD]
        have hvP' : gamma*(1-d)/(2*t) ≤ (t+p)/2-t := by
          dsimp only [scalarVertex] at hvP
          linarith only [hvP]
        have hvL' : d+p-1-t ≤ gamma*(1-d)/(2*t) := by
          simpa only [scalarVertex, sub_le_iff_le_add'] using hvLower
        have h0 := (div_le_iff₀ hden).mp hvD'
        have h1 := (div_le_iff₀ hden).mp hvP'
        have h2 := (le_div_iff₀ hden).mp hvL'
        have hpoly := hInterior d t hd0 hdLimit htPos htD
          (by nlinarith only [h0]) (by nlinarith only [h1]) (by nlinarith only [h2])
        have hmul : 0 ≤ 4*t*scalarResidual p C beta gamma lam g d
            (scalarVertex gamma d t) t := by
          rw [interiorPolynomial_identity p C beta gamma lam g d t ht]
          exact mul_nonneg (by linarith) hpoly
        exact nonneg_of_mul_nonneg_right hmul (by positivity : 0 < 4*t)
  · exact hHigh d a t hLimitD hd1 ha0 haLower haD ht0 htLower htA htD

end Taeyoung.Methods.Atlas126
