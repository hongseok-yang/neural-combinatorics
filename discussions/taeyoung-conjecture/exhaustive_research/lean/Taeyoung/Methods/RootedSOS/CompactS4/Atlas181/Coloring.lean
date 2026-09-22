import Taeyoung.Methods.Negative.Chromatic

/-! The finite coloring counts and catalogue conversion for Atlas181.
Keeping these computations independent of rooted graphon integration lowers
peak memory during kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas181

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Negative

/-! ### The graph -/

/-- Atlas181, with exactly the catalogue edge list. -/
def graph181 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (2, 3), (2, 4), (3, 4), (4, 5)]

instance : DecidableRel graph181.Adj := graphFromEdges_decidableAdj _ _

/-! ### Chromatic data, checked by surjective coloring counts. -/

/-- Check the catalogue edges directly, avoiding a graph adjacency computation for
all 36 ordered vertex pairs in every candidate coloring. -/
private def fastProper181 {j : ℕ} (y : Fin 6 → Fin j) : Prop :=
  y 0 ≠ y 2 ∧ y 0 ≠ y 3 ∧ y 0 ≠ y 4 ∧ y 0 ≠ y 5 ∧ y 1 ≠ y 2 ∧ y 1 ≠ y 3 ∧ y 2 ≠ y 3 ∧ y 2 ≠ y 4 ∧ y 3 ≠ y 4 ∧ y 4 ≠ y 5

private instance {j : ℕ} (y : Fin 6 → Fin j) : Decidable (fastProper181 y) := by
  unfold fastProper181
  infer_instance

private theorem isProper181_iff_fast {j : ℕ} (y : Fin 6 → Fin j) :
    IsProper graph181 y ↔ fastProper181 y := by
  constructor
  · intro h
    exact ⟨h 0 2 (by decide),h 0 3 (by decide),h 0 4 (by decide),h 0 5 (by decide),h 1 2 (by decide),h 1 3 (by decide),h 2 3 (by decide),h 2 4 (by decide),h 3 4 (by decide),h 4 5 (by decide)⟩
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [graph181,graphFromEdges,fastProper181,ne_comm]
    all_goals aesop

private def fastSurj181 (j : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin j)).filter
    (fun y => fastProper181 y ∧ Function.Surjective y)).card

private theorem surjCount181_eq_fast (j : ℕ) : surjCount graph181 j = fastSurj181 j := by
  unfold surjCount fastSurj181
  congr 1
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,isProper181_iff_fast]

theorem s181_0 : surjCount graph181 0 = 0 := by rw [surjCount181_eq_fast]; decide +kernel
theorem s181_1 : surjCount graph181 1 = 0 := by rw [surjCount181_eq_fast]; decide +kernel
theorem s181_2 : surjCount graph181 2 = 0 := by rw [surjCount181_eq_fast]; decide +kernel
theorem s181_3 : surjCount graph181 3 = 0 := by rw [surjCount181_eq_fast]; decide +kernel
theorem s181_4 : surjCount graph181 4 = 96 := by rw [surjCount181_eq_fast]; decide +kernel
theorem s181_5 : surjCount graph181 5 = 600 := by rw [surjCount181_eq_fast]; decide +kernel

theorem s181_6 : surjCount graph181 6 = 720 := by
  rw [surjCount_card graph181]
  decide

theorem count181 (k : ℕ) :
    properAssignmentCount graph181 k
      = 96 * k.choose 4 + 600 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph181 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s181_0, s181_1, s181_2, s181_3, s181_4, s181_5, s181_6]
  ring

theorem num181 : IsChromaticNumber graph181 4 where
  positive := by rw [count181]; decide
  zero_below k hk := by
    rw [count181]
    interval_cases k <;> decide

theorem chrom181 : IsChromaticPolynomial graph181
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph181 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph181

/-! ### The catalogue proposition -/

/-- The exact catalogue target polynomial. -/
noncomputable def target181 (p : ℝ) : ℝ :=
  (0)*p^0 + (2)*p^1 + (-15)*p^2 + (42)*p^3 + (-52)*p^4 + (24)*p^5

set_option maxHeartbeats 1000000 in
/-- **Atlas 181 satisfies the catalogue proposition, given the graphon bound.**
The graphon inequality is supplied separately by the interval SOS certificate. -/
theorem satisfiesLowerBound_181_of_bound
    (hbound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (2 : ℝ) / 3 ≤ cliqueDensity 2 W →
          target181 (cliqueDensity 2 W) ≤ homDensity graph181 W) :
    Taeyoung.SatisfiesLowerBound graph181 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph181 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph181) hP chrom181
  have hreq : r = 4 := IsChromaticNumber.unique (H := graph181) hr num181
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
    simp only [target181] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph181 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = target181 (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s181_0, s181_1, s181_2, s181_3, s181_4, s181_5, s181_6, target181,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

theorem target181_interval (s : Real) :
    target181 ((2+s)/3) = ((0)*s^0 + (2)*s^1 + (13)*s^2 + (30)*s^3 + (28)*s^4 + (8)*s^5)/81 := by
  unfold target181
  ring

#print axioms satisfiesLowerBound_181_of_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas181
