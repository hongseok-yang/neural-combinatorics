import Taeyoung.Methods.Negative.Chromatic

/-! The finite coloring counts and catalogue conversion for Atlas147.
Keeping these computations independent of rooted graphon integration lowers
peak memory during kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas147

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Negative

/-! ### The graph -/

/-- Atlas147, with exactly the catalogue edge list. -/
def graph147 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 5), (1, 2), (2, 3), (2, 4), (2, 5), (3, 4), (4, 5)]

instance : DecidableRel graph147.Adj := graphFromEdges_decidableAdj _ _

/-! ### Chromatic data, checked by surjective coloring counts. -/

/-- Check the catalogue edges directly, avoiding a graph adjacency computation for
all 36 ordered vertex pairs in every candidate coloring. -/
private def fastProper147 {j : ℕ} (y : Fin 6 → Fin j) : Prop :=
  y 0 ≠ y 1 ∧ y 0 ≠ y 5 ∧ y 1 ≠ y 2 ∧ y 2 ≠ y 3 ∧ y 2 ≠ y 4 ∧ y 2 ≠ y 5 ∧ y 3 ≠ y 4 ∧ y 4 ≠ y 5

private instance {j : ℕ} (y : Fin 6 → Fin j) : Decidable (fastProper147 y) := by
  unfold fastProper147
  infer_instance

private theorem isProper147_iff_fast {j : ℕ} (y : Fin 6 → Fin j) :
    IsProper graph147 y ↔ fastProper147 y := by
  constructor
  · intro h
    exact ⟨h 0 1 (by decide),h 0 5 (by decide),h 1 2 (by decide),h 2 3 (by decide),h 2 4 (by decide),h 2 5 (by decide),h 3 4 (by decide),h 4 5 (by decide)⟩
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [graph147,graphFromEdges,fastProper147,ne_comm]
    all_goals aesop

private def fastSurj147 (j : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin j)).filter
    (fun y => fastProper147 y ∧ Function.Surjective y)).card

private theorem surjCount147_eq_fast (j : ℕ) : surjCount graph147 j = fastSurj147 j := by
  unfold surjCount fastSurj147
  congr 1
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,isProper147_iff_fast]

theorem s147_0 : surjCount graph147 0 = 0 := by rw [surjCount147_eq_fast]; decide +kernel
theorem s147_1 : surjCount graph147 1 = 0 := by rw [surjCount147_eq_fast]; decide +kernel
theorem s147_2 : surjCount graph147 2 = 0 := by rw [surjCount147_eq_fast]; decide +kernel
theorem s147_3 : surjCount graph147 3 = 18 := by rw [surjCount147_eq_fast]; decide +kernel
theorem s147_4 : surjCount graph147 4 = 264 := by rw [surjCount147_eq_fast]; decide +kernel
theorem s147_5 : surjCount graph147 5 = 840 := by rw [surjCount147_eq_fast]; decide +kernel

theorem s147_6 : surjCount graph147 6 = 720 := by
  rw [surjCount_card graph147]
  decide

theorem count147 (k : ℕ) :
    properAssignmentCount graph147 k
      = 18 * k.choose 3 + 264 * k.choose 4 + 840 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph147 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s147_0, s147_1, s147_2, s147_3, s147_4, s147_5, s147_6]
  ring

theorem num147 : IsChromaticNumber graph147 3 where
  positive := by rw [count147]; decide
  zero_below k hk := by
    rw [count147]
    interval_cases k <;> decide

theorem chrom147 : IsChromaticPolynomial graph147
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph147 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph147

/-! ### The catalogue proposition -/

/-- The exact catalogue target polynomial. -/
noncomputable def target147 (p : ℝ) : ℝ :=
  (0)*p^0 + (1)*p^1 + (-7)*p^2 + (19)*p^3 + (-24)*p^4 + (12)*p^5

set_option maxHeartbeats 1000000 in
/-- **Atlas 147 satisfies the catalogue proposition, given the graphon bound.**
The graphon inequality is supplied separately by the interval SOS certificate. -/
theorem satisfiesLowerBound_147_of_bound
    (hbound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (1 : ℝ) / 2 ≤ cliqueDensity 2 W →
          target147 (cliqueDensity 2 W) ≤ homDensity graph147 W) :
    Taeyoung.SatisfiesLowerBound graph147 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph147 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph147) hP chrom147
  have hreq : r = 3 := IsChromaticNumber.unique (H := graph147) hr num147
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
    simp only [target147] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph147 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = target147 (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s147_0, s147_1, s147_2, s147_3, s147_4, s147_5, s147_6, target147,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

theorem target147_interval (s : Real) :
    target147 ((2+s)/3) = ((2)*s^0 + (11)*s^1 + (23)*s^2 + (25)*s^3 + (16)*s^4 + (4)*s^5)/81 := by
  unfold target147
  ring

#print axioms satisfiesLowerBound_147_of_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas147
