import Taeyoung.Methods.Negative.Chromatic

/-! The finite coloring counts and catalogue conversion for Atlas174.
Keeping these computations independent of rooted graphon integration lowers
peak memory during kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas174

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Negative

/-! ### The graph -/

/-- Atlas174, with exactly the catalogue edge list. -/
def graph174 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4), (4, 5)]

instance : DecidableRel graph174.Adj := graphFromEdges_decidableAdj _ _

/-! ### Chromatic data, checked by surjective coloring counts. -/

/-- Check the catalogue edges directly, avoiding a graph adjacency computation for
all 36 ordered vertex pairs in every candidate coloring. -/
private def fastProper174 {j : ℕ} (y : Fin 6 → Fin j) : Prop :=
  y 0 ≠ y 1 ∧ y 0 ≠ y 2 ∧ y 0 ≠ y 3 ∧ y 1 ≠ y 4 ∧ y 1 ≠ y 5 ∧ y 2 ≠ y 3 ∧ y 2 ≠ y 5 ∧ y 3 ≠ y 4 ∧ y 4 ≠ y 5

private instance {j : ℕ} (y : Fin 6 → Fin j) : Decidable (fastProper174 y) := by
  unfold fastProper174
  infer_instance

private theorem isProper174_iff_fast {j : ℕ} (y : Fin 6 → Fin j) :
    IsProper graph174 y ↔ fastProper174 y := by
  constructor
  · intro h
    exact ⟨h 0 1 (by decide),h 0 2 (by decide),h 0 3 (by decide),h 1 4 (by decide),h 1 5 (by decide),h 2 3 (by decide),h 2 5 (by decide),h 3 4 (by decide),h 4 5 (by decide)⟩
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [graph174,graphFromEdges,fastProper174,ne_comm]
    all_goals aesop

private def fastSurj174 (j : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin j)).filter
    (fun y => fastProper174 y ∧ Function.Surjective y)).card

private theorem surjCount174_eq_fast (j : ℕ) : surjCount graph174 j = fastSurj174 j := by
  unfold surjCount fastSurj174
  congr 1
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,isProper174_iff_fast]

theorem s174_0 : surjCount graph174 0 = 0 := by rw [surjCount174_eq_fast]; decide +kernel
theorem s174_1 : surjCount graph174 1 = 0 := by rw [surjCount174_eq_fast]; decide +kernel
theorem s174_2 : surjCount graph174 2 = 0 := by rw [surjCount174_eq_fast]; decide +kernel
theorem s174_3 : surjCount graph174 3 = 12 := by rw [surjCount174_eq_fast]; decide +kernel
theorem s174_4 : surjCount graph174 4 = 216 := by rw [surjCount174_eq_fast]; decide +kernel
theorem s174_5 : surjCount graph174 5 = 720 := by rw [surjCount174_eq_fast]; decide +kernel

theorem s174_6 : surjCount graph174 6 = 720 := by
  rw [surjCount_card graph174]
  decide

theorem count174 (k : ℕ) :
    properAssignmentCount graph174 k
      = 12 * k.choose 3 + 216 * k.choose 4 + 720 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph174 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s174_0, s174_1, s174_2, s174_3, s174_4, s174_5, s174_6]
  ring

theorem num174 : IsChromaticNumber graph174 3 where
  positive := by rw [count174]; decide
  zero_below k hk := by
    rw [count174]
    interval_cases k <;> decide

theorem chrom174 : IsChromaticPolynomial graph174
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph174 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph174

/-! ### The catalogue proposition -/

/-- The exact catalogue target polynomial. -/
noncomputable def target174 (p : ℝ) : ℝ :=
  (0)*p^0 + (4)*p^1 + (-25)*p^2 + (59)*p^3 + (-63)*p^4 + (26)*p^5

set_option maxHeartbeats 1000000 in
/-- **Atlas 174 satisfies the catalogue proposition, given the graphon bound.**
The graphon inequality is supplied separately by the interval SOS certificate. -/
theorem satisfiesLowerBound_174_of_bound
    (hbound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (1 : ℝ) / 2 ≤ cliqueDensity 2 W →
          target174 (cliqueDensity 2 W) ≤ homDensity graph174 W) :
    Taeyoung.SatisfiesLowerBound graph174 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph174 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph174) hP chrom174
  have hreq : r = 3 := IsChromaticNumber.unique (H := graph174) hr num174
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
    simp only [target174] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph174 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = target174 (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s174_0, s174_1, s174_2, s174_3, s174_4, s174_5, s174_6, target174,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

theorem target174_interval (s : Real) :
    target174 ((2+s)/3) = ((4)*s^0 + (28)*s^1 + (55)*s^2 + (59)*s^3 + (71)*s^4 + (26)*s^5)/243 := by
  unfold target174
  ring

#print axioms satisfiesLowerBound_174_of_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas174
