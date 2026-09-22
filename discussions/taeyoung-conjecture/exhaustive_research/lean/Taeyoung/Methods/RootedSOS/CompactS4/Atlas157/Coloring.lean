import Taeyoung.Methods.Negative.Chromatic

/-! The finite coloring counts and catalogue conversion for Atlas157.
Keeping these computations independent of rooted graphon integration lowers
peak memory during kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas157

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Negative

/-! ### The graph -/

/-- Atlas157, with exactly the catalogue edge list. -/
def graph157 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 5), (2, 3), (2, 5)]

instance : DecidableRel graph157.Adj := graphFromEdges_decidableAdj _ _

/-! ### Chromatic data, checked by surjective coloring counts. -/

/-- Check the catalogue edges directly, avoiding a graph adjacency computation for
all 36 ordered vertex pairs in every candidate coloring. -/
private def fastProper157 {j : ℕ} (y : Fin 6 → Fin j) : Prop :=
  y 0 ≠ y 1 ∧ y 0 ≠ y 2 ∧ y 0 ≠ y 3 ∧ y 0 ≠ y 4 ∧ y 1 ≠ y 2 ∧ y 1 ≠ y 3 ∧ y 1 ≠ y 5 ∧ y 2 ≠ y 3 ∧ y 2 ≠ y 5

private instance {j : ℕ} (y : Fin 6 → Fin j) : Decidable (fastProper157 y) := by
  unfold fastProper157
  infer_instance

private theorem isProper157_iff_fast {j : ℕ} (y : Fin 6 → Fin j) :
    IsProper graph157 y ↔ fastProper157 y := by
  constructor
  · intro h
    exact ⟨h 0 1 (by decide),h 0 2 (by decide),h 0 3 (by decide),h 0 4 (by decide),h 1 2 (by decide),h 1 3 (by decide),h 1 5 (by decide),h 2 3 (by decide),h 2 5 (by decide)⟩
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [graph157,graphFromEdges,fastProper157,ne_comm]
    all_goals aesop

private def fastSurj157 (j : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin j)).filter
    (fun y => fastProper157 y ∧ Function.Surjective y)).card

private theorem surjCount157_eq_fast (j : ℕ) : surjCount graph157 j = fastSurj157 j := by
  unfold surjCount fastSurj157
  congr 1
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,isProper157_iff_fast]

theorem s157_0 : surjCount graph157 0 = 0 := by rw [surjCount157_eq_fast]; decide +kernel
theorem s157_1 : surjCount graph157 1 = 0 := by rw [surjCount157_eq_fast]; decide +kernel
theorem s157_2 : surjCount graph157 2 = 0 := by rw [surjCount157_eq_fast]; decide +kernel
theorem s157_3 : surjCount graph157 3 = 0 := by rw [surjCount157_eq_fast]; decide +kernel
theorem s157_4 : surjCount graph157 4 = 144 := by rw [surjCount157_eq_fast]; decide +kernel
theorem s157_5 : surjCount graph157 5 = 720 := by rw [surjCount157_eq_fast]; decide +kernel

theorem s157_6 : surjCount graph157 6 = 720 := by
  rw [surjCount_card graph157]
  decide

theorem count157 (k : ℕ) :
    properAssignmentCount graph157 k
      = 144 * k.choose 4 + 720 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph157 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s157_0, s157_1, s157_2, s157_3, s157_4, s157_5, s157_6]
  ring

theorem num157 : IsChromaticNumber graph157 4 where
  positive := by rw [count157]; decide
  zero_below k hk := by
    rw [count157]
    interval_cases k <;> decide

theorem chrom157 : IsChromaticPolynomial graph157
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph157 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph157

/-! ### The catalogue proposition -/

/-- The exact catalogue target polynomial. -/
noncomputable def target157 (p : ℝ) : ℝ :=
  (0)*p^0 + (0)*p^1 + (-2)*p^2 + (11)*p^3 + (-20)*p^4 + (12)*p^5

set_option maxHeartbeats 1000000 in
/-- **Atlas 157 satisfies the catalogue proposition, given the graphon bound.**
The graphon inequality is supplied separately by the interval SOS certificate. -/
theorem satisfiesLowerBound_157_of_bound
    (hbound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (2 : ℝ) / 3 ≤ cliqueDensity 2 W →
          target157 (cliqueDensity 2 W) ≤ homDensity graph157 W) :
    Taeyoung.SatisfiesLowerBound graph157 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph157 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph157) hP chrom157
  have hreq : r = 4 := IsChromaticNumber.unique (H := graph157) hr num157
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
    simp only [target157] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph157 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = target157 (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s157_0, s157_1, s157_2, s157_3, s157_4, s157_5, s157_6, target157,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

theorem target157_interval (s : Real) :
    target157 ((2+s)/3) = ((0)*s^0 + (4)*s^1 + (20)*s^2 + (33)*s^3 + (20)*s^4 + (4)*s^5)/81 := by
  unfold target157
  ring

#print axioms satisfiesLowerBound_157_of_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas157
