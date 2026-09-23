import Taeyoung.Methods.Negative.Chromatic

/-! The finite coloring counts and catalogue conversion for Atlas171.
Keeping these computations independent of rooted graphon integration lowers
peak memory during kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas171

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Negative

/-! ### The graph -/

/-- Atlas171, with exactly the catalogue edge list. -/
def graph171 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 4), (0, 5), (1, 2), (2, 3), (2, 5), (3, 4), (3, 5), (4, 5)]

instance : DecidableRel graph171.Adj := graphFromEdges_decidableAdj _ _

/-! ### Chromatic data, checked by surjective coloring counts. -/

/-- Check the catalogue edges directly, avoiding a graph adjacency computation for
all 36 ordered vertex pairs in every candidate coloring. -/
private def fastProper171 {j : ℕ} (y : Fin 6 → Fin j) : Prop :=
  y 0 ≠ y 1 ∧ y 0 ≠ y 4 ∧ y 0 ≠ y 5 ∧ y 1 ≠ y 2 ∧ y 2 ≠ y 3 ∧ y 2 ≠ y 5 ∧ y 3 ≠ y 4 ∧ y 3 ≠ y 5 ∧ y 4 ≠ y 5

private instance {j : ℕ} (y : Fin 6 → Fin j) : Decidable (fastProper171 y) := by
  unfold fastProper171
  infer_instance

private theorem isProper171_iff_fast {j : ℕ} (y : Fin 6 → Fin j) :
    IsProper graph171 y ↔ fastProper171 y := by
  constructor
  · intro h
    exact ⟨h 0 1 (by decide),h 0 4 (by decide),h 0 5 (by decide),h 1 2 (by decide),h 2 3 (by decide),h 2 5 (by decide),h 3 4 (by decide),h 3 5 (by decide),h 4 5 (by decide)⟩
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [graph171,graphFromEdges,fastProper171,ne_comm]
    all_goals aesop

private def fastSurj171 (j : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin j)).filter
    (fun y => fastProper171 y ∧ Function.Surjective y)).card

private theorem surjCount171_eq_fast (j : ℕ) : surjCount graph171 j = fastSurj171 j := by
  unfold surjCount fastSurj171
  congr 1
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,isProper171_iff_fast]

theorem s171_0 : surjCount graph171 0 = 0 := by rw [surjCount171_eq_fast]; decide +kernel
theorem s171_1 : surjCount graph171 1 = 0 := by rw [surjCount171_eq_fast]; decide +kernel
theorem s171_2 : surjCount graph171 2 = 0 := by rw [surjCount171_eq_fast]; decide +kernel
theorem s171_3 : surjCount graph171 3 = 6 := by rw [surjCount171_eq_fast]; decide +kernel
theorem s171_4 : surjCount graph171 4 = 192 := by rw [surjCount171_eq_fast]; decide +kernel
theorem s171_5 : surjCount graph171 5 = 720 := by rw [surjCount171_eq_fast]; decide +kernel

theorem s171_6 : surjCount graph171 6 = 720 := by
  rw [surjCount_card graph171]
  decide

theorem count171 (k : ℕ) :
    properAssignmentCount graph171 k
      = 6 * k.choose 3 + 192 * k.choose 4 + 720 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph171 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s171_0, s171_1, s171_2, s171_3, s171_4, s171_5, s171_6]
  ring

theorem num171 : IsChromaticNumber graph171 3 where
  positive := by rw [count171]; decide
  zero_below k hk := by
    rw [count171]
    interval_cases k <;> decide

theorem chrom171 : IsChromaticPolynomial graph171
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph171 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph171

/-! ### The catalogue proposition -/

/-- The exact catalogue target polynomial. -/
noncomputable def target171 (p : ℝ) : ℝ :=
  (0)*p^0 + (3)*p^1 + (-19)*p^2 + (46)*p^3 + (-51)*p^4 + (22)*p^5

set_option maxHeartbeats 1000000 in
/-- **Atlas 171 satisfies the catalogue proposition, given the graphon bound.**
The graphon inequality is supplied separately by the interval SOS certificate. -/
theorem satisfiesLowerBound_171_of_bound
    (hbound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (1 : ℝ) / 2 ≤ cliqueDensity 2 W →
          target171 (cliqueDensity 2 W) ≤ homDensity graph171 W) :
    Taeyoung.SatisfiesLowerBound graph171 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph171 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph171) hP chrom171
  have hreq : r = 3 := IsChromaticNumber.unique (H := graph171) hr num171
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
    simp only [target171] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph171 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = target171 (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s171_0, s171_1, s171_2, s171_3, s171_4, s171_5, s171_6, target171,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

theorem target171_interval (s : Real) :
    target171 ((2+s)/3) = ((2)*s^0 + (23)*s^1 + (59)*s^2 + (70)*s^3 + (67)*s^4 + (22)*s^5)/243 := by
  unfold target171
  ring

#print axioms satisfiesLowerBound_171_of_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas171
