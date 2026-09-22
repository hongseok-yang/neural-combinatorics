import Taeyoung.Methods.Atlas126.Junction
import Taeyoung.Methods.Atlas126.Plane
import Taeyoung.Methods.Atlas126.HighDegree
import Taeyoung.Methods.Atlas126.InteriorCutoff

/-! Assembly of the corrected junction plane from its four certificate
families. The zero parameter cases are included by a closed interval scaling
lemma, so no division-by-zero cases are delegated to generated certificates. -/

namespace Taeyoung.Methods.Atlas126

theorem exists_unit_scale {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (hta : t ≤ a) :
    ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ a*u = t := by
  by_cases hz : a = 0
  · have ht0 : t = 0 := by linarith
    exact ⟨0, le_rfl, zero_le_one, by simp [hz, ht0]⟩
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    refine ⟨t/a, div_nonneg ht ha, (div_le_one hapos).mpr hta, ?_⟩
    field_simp

theorem polynomialPlaneJ_of_certificates {x : ℝ}
    (hx0 : (15/16 : ℝ) ≤ x) (hx1 : x ≤ 1)
    (h1 : ∀ {d u : ℝ}, 0 ≤ d → d ≤ (15/16 : ℝ) → 0 ≤ u → u ≤ 1 →
      0 ≤ junctionFace1Constraint0 x d u → 0 ≤ junctionFace1Constraint1 x d u →
      0 ≤ junctionFace1Target x d u)
    (h2 : ∀ {d u : ℝ}, 0 ≤ d → d ≤ (15/16 : ℝ) → 0 ≤ u → u ≤ 1 →
      0 ≤ junctionFace2Constraint x d u → 0 ≤ junctionFace2Target x d u)
    (h4 : ∀ {d u : ℝ}, 0 ≤ d → d ≤ (15/16 : ℝ) → 0 ≤ u → u ≤ 1 →
      0 ≤ junctionFace4Constraint0 x d u → 0 ≤ junctionFace4Constraint1 x d u →
      0 ≤ junctionFace4Constraint2 x d u → 0 ≤ junctionFace4Constraint3 x d u →
      0 ≤ junctionFace4Target x d u)
    (hI : ∀ {d u : ℝ}, (5/8 : ℝ) ≤ d → d ≤ (15/16 : ℝ) → 0 ≤ u → u ≤ 1 →
      0 ≤ junctionInteriorConstraint0 x d u → 0 ≤ junctionInteriorConstraint1 x d u →
      0 ≤ junctionInteriorConstraint2 x d u → 0 ≤ junctionInteriorTarget x d u) :
    PolynomialPlane (lowDensity x) (target (lowDensity x))
      (betaJ x) (gammaJ x) (lambdaJ x) (lowTriangle x) := by
  apply scalarPlane_of_four_candidates (lowDensity x) (target (lowDensity x))
    (betaJ x) (gammaJ x) (lambdaJ x) (lowTriangle x) (15/16) (gammaJ_nonneg hx0 hx1)
  · intro d t hd0 hd1 ht0 htD hdUpper _hSelected
    obtain ⟨u, hu0, hu1, hu⟩ := exists_unit_scale (sq_nonneg d) ht0 htD
    have hc : 0 ≤ junctionFace2Constraint x d u := by
      dsimp only [junctionFace2Constraint]
      rw [hu]
      linarith
    simpa only [junctionFace2Target, hu] using h2 hd0 hd1 hu0 hu1 hc
  · intro d t hd0 hd1 ht0 htD hUpperD hLowerUpper _hSelected
    obtain ⟨u, hu0, hu1, hu⟩ := exists_unit_scale (sq_nonneg d) ht0 htD
    have hc0 : 0 ≤ junctionFace1Constraint0 x d u := by
      dsimp only [junctionFace1Constraint0]
      rw [hu]
      linarith
    have hc1 : 0 ≤ junctionFace1Constraint1 x d u := by
      dsimp only [junctionFace1Constraint1]
      rw [hu]
      linarith
    simpa only [junctionFace1Target, hu] using h1 hd0 hd1 hu0 hu1 hc0 hc1
  · intro d t hd0 hd1 ht0 htD htLower hLowerD hLowerUpper hSelected
    obtain ⟨u, hu0, hu1, hu⟩ := exists_unit_scale (ht0.trans htLower) ht0 htLower
    have hc0 : 0 ≤ junctionFace4Constraint0 x d u := ht0.trans htLower
    have hc1 : 0 ≤ junctionFace4Constraint1 x d u := by
      dsimp only [junctionFace4Constraint1]
      rw [hu]
      linarith
    have hc2 : 0 ≤ junctionFace4Constraint2 x d u := by
      dsimp only [junctionFace4Constraint2]
      rw [hu]
      linarith
    have hc3 : 0 ≤ junctionFace4Constraint3 x d u := by
      simpa only [junctionFace4Constraint3, hu] using hSelected
    simpa only [junctionFace4Target, hu] using h4 hd0 hd1 hu0 hu1 hc0 hc1 hc2 hc3
  · intro d t hd0 hd1 htPos htD hi0 hi1 hi2
    have hdCut := junctionInterior_degree_lower hx0 hx1 (by linarith : d ≤ 1) hi1
    obtain ⟨u, hu0, hu1, hu⟩ := exists_unit_scale (sq_nonneg d) htPos.le htD
    have hc0 : 0 ≤ junctionInteriorConstraint0 x d u := by
      simpa only [junctionInteriorConstraint0, hu] using hi0
    have hc1 : 0 ≤ junctionInteriorConstraint1 x d u := by
      simpa only [junctionInteriorConstraint1, hu] using hi1
    have hc2 : 0 ≤ junctionInteriorConstraint2 x d u := by
      simpa only [junctionInteriorConstraint2, hu] using hi2
    simpa only [junctionInteriorTarget, interiorPolynomial, hu] using
      hI hdCut hd1 hu0 hu1 hc0 hc1 hc2
  · intro d a t hd0 hd1 ha0 haLower haD ht0 htLower htA htD
    exact scalarResidual_highDegreeJ hx0 hx1 hd0 hd1 haLower htLower htA

end Taeyoung.Methods.Atlas126
