import Taeyoung.Methods.Negative.Chromatic

/-! The finite coloring counts and catalogue conversion for Atlas153.
Keeping these computations independent of rooted graphon integration lowers
peak memory during kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas153

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Negative

/-! ### The graph -/

/-- Atlas153, with exactly the catalogue edge list. -/
def graph153 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 4), (0, 5), (1, 2), (1, 5), (2, 3), (2, 5), (3, 4)]

instance : DecidableRel graph153.Adj := graphFromEdges_decidableAdj _ _

/-! ### Chromatic data, checked by surjective coloring counts. -/

/-- Check the catalogue edges directly, avoiding a graph adjacency computation for
all 36 ordered vertex pairs in every candidate coloring. -/
private def fastProper153 {j : ℕ} (y : Fin 6 → Fin j) : Prop :=
  y 0 ≠ y 1 ∧ y 0 ≠ y 4 ∧ y 0 ≠ y 5 ∧ y 1 ≠ y 2 ∧ y 1 ≠ y 5 ∧ y 2 ≠ y 3 ∧ y 2 ≠ y 5 ∧ y 3 ≠ y 4

private instance {j : ℕ} (y : Fin 6 → Fin j) : Decidable (fastProper153 y) := by
  unfold fastProper153
  infer_instance

private theorem isProper153_iff_fast {j : ℕ} (y : Fin 6 → Fin j) :
    IsProper graph153 y ↔ fastProper153 y := by
  constructor
  · intro h
    exact ⟨h 0 1 (by decide),h 0 4 (by decide),h 0 5 (by decide),h 1 2 (by decide),h 1 5 (by decide),h 2 3 (by decide),h 2 5 (by decide),h 3 4 (by decide)⟩
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [graph153,graphFromEdges,fastProper153,ne_comm]
    all_goals aesop

private def fastSurj153 (j : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin j)).filter
    (fun y => fastProper153 y ∧ Function.Surjective y)).card

private theorem surjCount153_eq_fast (j : ℕ) : surjCount graph153 j = fastSurj153 j := by
  unfold surjCount fastSurj153
  congr 1
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,isProper153_iff_fast]

theorem s153_0 : surjCount graph153 0 = 0 := by rw [surjCount153_eq_fast]; decide +kernel
theorem s153_1 : surjCount graph153 1 = 0 := by rw [surjCount153_eq_fast]; decide +kernel
theorem s153_2 : surjCount graph153 2 = 0 := by rw [surjCount153_eq_fast]; decide +kernel
theorem s153_3 : surjCount graph153 3 = 12 := by rw [surjCount153_eq_fast]; decide +kernel
theorem s153_4 : surjCount graph153 4 = 264 := by rw [surjCount153_eq_fast]; decide +kernel
theorem s153_5 : surjCount graph153 5 = 840 := by rw [surjCount153_eq_fast]; decide +kernel

theorem s153_6 : surjCount graph153 6 = 720 := by
  rw [surjCount_card graph153]
  decide

theorem count153 (k : ℕ) :
    properAssignmentCount graph153 k
      = 12 * k.choose 3 + 264 * k.choose 4 + 840 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph153 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s153_0, s153_1, s153_2, s153_3, s153_4, s153_5, s153_6]
  ring

theorem num153 : IsChromaticNumber graph153 3 where
  positive := by rw [count153]; decide
  zero_below k hk := by
    rw [count153]
    interval_cases k <;> decide

theorem chrom153 : IsChromaticPolynomial graph153
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph153 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph153

/-! ### The catalogue proposition -/

/-- The exact catalogue target polynomial. -/
noncomputable def target153 (p : ℝ) : ℝ :=
  (0)*p^0 + (2)*p^1 + (-12)*p^2 + (28)*p^3 + (-31)*p^4 + (14)*p^5

set_option maxHeartbeats 1000000 in
/-- **Atlas 153 satisfies the catalogue proposition, given the graphon bound.**
The graphon inequality is supplied separately by the interval SOS certificate. -/
theorem satisfiesLowerBound_153_of_bound
    (hbound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (1 : ℝ) / 2 ≤ cliqueDensity 2 W →
          target153 (cliqueDensity 2 W) ≤ homDensity graph153 W) :
    Taeyoung.SatisfiesLowerBound graph153 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph153 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph153) hP chrom153
  have hreq : r = 3 := IsChromaticNumber.unique (H := graph153) hr num153
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := hbound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    simp only [target153] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph153 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = target153 (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s153_0, s153_1, s153_2, s153_3, s153_4, s153_5, s153_6, target153,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

theorem target153_interval (s : Real) :
    target153 ((2+s)/3) = ((4)*s^0 + (34)*s^1 + (76)*s^2 + (68)*s^3 + (47)*s^4 + (14)*s^5)/243 := by
  unfold target153
  ring

#print axioms satisfiesLowerBound_153_of_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas153
