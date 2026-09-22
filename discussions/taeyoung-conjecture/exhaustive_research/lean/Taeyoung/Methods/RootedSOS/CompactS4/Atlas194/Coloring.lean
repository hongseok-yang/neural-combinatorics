import Taeyoung.Methods.Negative.Chromatic

/-! The finite coloring counts and catalogue conversion for Atlas194.
Keeping these computations independent of rooted graphon integration lowers
peak memory during kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas194

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Negative

/-! ### The graph -/

/-- Atlas194, with exactly the catalogue edge list. -/
def graph194 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 5), (4, 5)]

instance : DecidableRel graph194.Adj := graphFromEdges_decidableAdj _ _

/-! ### Chromatic data, checked by surjective coloring counts. -/

/-- Check the catalogue edges directly, avoiding a graph adjacency computation for
all 36 ordered vertex pairs in every candidate coloring. -/
private def fastProper194 {j : ℕ} (y : Fin 6 → Fin j) : Prop :=
  y 0 ≠ y 1 ∧ y 0 ≠ y 2 ∧ y 0 ≠ y 3 ∧ y 0 ≠ y 4 ∧ y 1 ≠ y 2 ∧ y 1 ≠ y 3 ∧ y 1 ≠ y 4 ∧ y 2 ≠ y 3 ∧ y 2 ≠ y 4 ∧ y 3 ≠ y 5 ∧ y 4 ≠ y 5

private instance {j : ℕ} (y : Fin 6 → Fin j) : Decidable (fastProper194 y) := by
  unfold fastProper194
  infer_instance

private theorem isProper194_iff_fast {j : ℕ} (y : Fin 6 → Fin j) :
    IsProper graph194 y ↔ fastProper194 y := by
  constructor
  · intro h
    exact ⟨h 0 1 (by decide),h 0 2 (by decide),h 0 3 (by decide),h 0 4 (by decide),h 1 2 (by decide),h 1 3 (by decide),h 1 4 (by decide),h 2 3 (by decide),h 2 4 (by decide),h 3 5 (by decide),h 4 5 (by decide)⟩
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [graph194,graphFromEdges,fastProper194,ne_comm]
    all_goals aesop

private def fastSurj194 (j : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin j)).filter
    (fun y => fastProper194 y ∧ Function.Surjective y)).card

private theorem surjCount194_eq_fast (j : ℕ) : surjCount graph194 j = fastSurj194 j := by
  unfold surjCount fastSurj194
  congr 1
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,isProper194_iff_fast]

theorem s194_0 : surjCount graph194 0 = 0 := by rw [surjCount194_eq_fast]; decide +kernel
theorem s194_1 : surjCount graph194 1 = 0 := by rw [surjCount194_eq_fast]; decide +kernel
theorem s194_2 : surjCount graph194 2 = 0 := by rw [surjCount194_eq_fast]; decide +kernel
theorem s194_3 : surjCount graph194 3 = 0 := by rw [surjCount194_eq_fast]; decide +kernel
theorem s194_4 : surjCount graph194 4 = 72 := by rw [surjCount194_eq_fast]; decide +kernel
theorem s194_5 : surjCount graph194 5 = 480 := by rw [surjCount194_eq_fast]; decide +kernel

theorem s194_6 : surjCount graph194 6 = 720 := by
  rw [surjCount_card graph194]
  decide

theorem count194 (k : ℕ) :
    properAssignmentCount graph194 k
      = 72 * k.choose 4 + 480 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph194 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s194_0, s194_1, s194_2, s194_3, s194_4, s194_5, s194_6]
  ring

theorem num194 : IsChromaticNumber graph194 4 where
  positive := by rw [count194]; decide
  zero_below k hk := by
    rw [count194]
    interval_cases k <;> decide

theorem chrom194 : IsChromaticPolynomial graph194
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph194 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph194

/-! ### The catalogue proposition -/

/-- The exact catalogue target polynomial. -/
noncomputable def target194 (p : ℝ) : ℝ :=
  (0)*p^0 + (6)*p^1 + (-39)*p^2 + (95)*p^3 + (-103)*p^4 + (42)*p^5

set_option maxHeartbeats 1000000 in
/-- **Atlas 194 satisfies the catalogue proposition, given the graphon bound.**
The graphon inequality is supplied separately by the interval SOS certificate. -/
theorem satisfiesLowerBound_194_of_bound
    (hbound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (2 : ℝ) / 3 ≤ cliqueDensity 2 W →
          target194 (cliqueDensity 2 W) ≤ homDensity graph194 W) :
    Taeyoung.SatisfiesLowerBound graph194 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph194 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph194) hP chrom194
  have hreq : r = 4 := IsChromaticNumber.unique (H := graph194) hr num194
  subst hPeq
  subst hreq
  have hp : (2 : ℝ) / 3 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := hbound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    simp only [target194] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph194 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = target194 (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s194_0, s194_1, s194_2, s194_3, s194_4, s194_5, s194_6, target194,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

theorem target194_interval (s : Real) :
    target194 ((2+s)/3) = ((0)*s^0 + (2)*s^1 + (7)*s^2 + (21)*s^3 + (37)*s^4 + (14)*s^5)/81 := by
  unfold target194
  ring

#print axioms satisfiesLowerBound_194_of_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas194
