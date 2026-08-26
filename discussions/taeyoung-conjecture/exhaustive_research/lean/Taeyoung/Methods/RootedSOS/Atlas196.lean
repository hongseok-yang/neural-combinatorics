import Taeyoung.Methods.BaseCone
import Taeyoung.Methods.Link.ConeChromatic
import Taeyoung.Methods.RootedSOS.Atlas43

/-!
# Atlas 196 from the verified house certificate

Atlas 196 is the cone over Atlas 43.  This module applies the general
normalized-link cone bound to the exact house theorem and packages the result
as the common catalogue proposition.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedSOS.Atlas196

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link Taeyoung.Methods.Negative
  Taeyoung.Methods.RootedSOS.House

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- The derivative of the house target polynomial. -/
def houseTargetDeriv (z : ℝ) : ℝ :=
  24 * z ^ 3 - 27 * z ^ 2 + 10 * z - 1

lemma houseTarget_half : houseTarget (1 / 2) = 0 := by
  norm_num [houseTarget]

@[simp] lemma houseTarget_one : houseTarget 1 = 1 := by
  norm_num [houseTarget]

lemma houseTarget_nonneg {z : ℝ} (hz : 1 / 2 ≤ z) : 0 ≤ houseTarget z := by
  have hz0 : 0 ≤ z := by linarith
  have hlin : 0 ≤ 2 * z - 1 := by linarith
  have hquad : 0 ≤ 3 * z ^ 2 - 3 * z + 1 := by
    nlinarith [sq_nonneg (2 * z - 1)]
  exact mul_nonneg (mul_nonneg hz0 hlin) hquad

lemma houseTargetDeriv_nonneg {z : ℝ} (hz : 1 / 2 ≤ z) :
    0 ≤ houseTargetDeriv z := by
  have ht : 0 ≤ z - 1 / 2 := by linarith
  rw [houseTargetDeriv]
  nlinarith [mul_nonneg (mul_nonneg ht ht) ht, mul_nonneg ht ht]

/-- The tangent line to the house target at any point of `[1/2,1]` is a
global minorant on that interval. -/
lemma houseTarget_tangent {c : ℝ} (hc : 1 / 2 ≤ c) (w : ℝ)
    (hw : 1 / 2 ≤ w) (_hw1 : w ≤ 1) :
    houseTarget c + houseTargetDeriv c * (w - c) ≤ houseTarget w := by
  have hs : 0 ≤ w - 1 / 2 := by linarith
  have ht : 0 ≤ c - 1 / 2 := by linarith
  have hinner : 0 ≤
      18 * c ^ 2 + 12 * c * w - 18 * c + 6 * w ^ 2 - 9 * w + 5 := by
    nlinarith [sq_nonneg (w - 1 / 2), sq_nonneg (c - 1 / 2),
      mul_nonneg hs ht]
  rw [houseTarget, houseTarget, houseTargetDeriv]
  nlinarith [mul_nonneg (sq_nonneg (w - c)) hinner]

/-- The already checked Atlas 43 theorem in the form required by the cone
machinery. -/
theorem base_house {Ω' : Type} [MeasurableSpace Ω'] {ν : Measure Ω'}
    [IsProbabilityMeasure ν] (V : Graphon Ω' ν)
    (hz : 1 / 2 ≤ cliqueDensity 2 V) :
    houseTarget (cliqueDensity 2 V) ≤ homDensity houseGraph V :=
  Atlas43.house_bound_of_certificateIdentity Atlas43.certificateIdentity V hz

/-- The normalized-link transfer from the house to its cone. -/
theorem coneHouse_bound (W : Graphon Ω μ)
    (hp : 2 / 3 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 5 *
        houseTarget (2 - 1 / cliqueDensity 2 W) ≤
      homDensity (coneGraph houseGraph) W := by
  have hppos : 0 < cliqueDensity 2 W := by linarith
  have hinv : 1 / cliqueDensity 2 W ≤ 3 / 2 := by
    rw [div_le_iff₀ hppos]
    linarith
  have hc : (1 : ℝ) / 2 ≤ 2 - 1 / cliqueDensity 2 W := by linarith
  exact BaseCone.coneGraph_pow_bound (h := 3) houseGraph W
    (φ := houseTarget) (a := 1 / 2)
    (lam := houseTargetDeriv (2 - 1 / cliqueDensity 2 W))
    houseTarget_half (houseTargetDeriv_nonneg hc) (by norm_num) hppos
    (houseTarget_tangent hc) (houseTarget_nonneg hc) base_house

/-! ## Chromatic data and catalogue packaging -/

/-- The surjective-colouring expression used for the checked house
chromatic polynomial. -/
noncomputable def housePolynomial : Polynomial ℝ :=
  ∑ j ∈ range (Fintype.card (Fin 5) + 1),
    C ((surjCount houseGraph j : ℝ) / (j).factorial) *
      ∏ i ∈ range j, (X - C (i : ℝ))

theorem housePolynomial_spec : IsChromaticPolynomial houseGraph housePolynomial := by
  exact houseChromaticPolynomial

theorem chrom196 : IsChromaticPolynomial (coneGraph houseGraph)
    (X * housePolynomial.comp (X - 1)) :=
  isChromaticPolynomial_coneGraph houseGraph housePolynomial_spec

theorem num196 : IsChromaticNumber (coneGraph houseGraph) 4 := by
  simpa using isChromaticNumber_coneGraph houseGraph houseChromaticNumber

lemma chromaticTarget_196 {p : ℝ} (hp : p ≠ 1) (hp0 : p ≠ 0) :
    chromaticTarget (V := Fin 6) (X * housePolynomial.comp (X - 1)) p =
      p ^ 5 * houseTarget (2 - 1 / p) := by
  have hq : 1 - p ≠ 0 := fun h => hp (by linarith)
  rw [chromaticTarget_of_ne_one _ hp]
  simp only [Fintype.card_fin, eval_mul, eval_comp, eval_sub, eval_X, eval_one,
    housePolynomial, eval_finset_sum, eval_C]
  simp only [House.surj_house_0, House.surj_house_1, House.surj_house_2,
    House.surj_house_3, House.surj_house_4, House.surj_house_5,
    Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_range_succ,
    Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
    zero_div, zero_mul, zero_add, eval_add, eval_mul, eval_sub, eval_pow,
    eval_C, eval_X, eval_one, eval_zero]
  rw [houseTarget]
  field_simp
  ring

/-- The cone over the verified house satisfies the full catalogue bound. -/
theorem satisfiesLowerBound_coneHouse :
    SatisfiesLowerBound (coneGraph houseGraph) := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = X * housePolynomial.comp (X - 1) :=
    IsChromaticPolynomial.unique (H := coneGraph houseGraph) hP chrom196
  have hreq : r = 4 :=
    IsChromaticNumber.unique (H := coneGraph houseGraph) hr num196
  subst hPeq
  subst hreq
  have hp : (2 : ℝ) / 3 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hppos : 0 < cliqueDensity 2 W := by linarith
  have hkey := coneHouse_bound W hp
  change chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num [houseTarget] at hkey
    exact hkey
  · rw [chromaticTarget_196 hone (ne_of_gt hppos)]
    exact hkey

end Taeyoung.Methods.RootedSOS.Atlas196
