import Taeyoung.Methods.Negative.Chromatic

/-! The finite coloring counts and catalogue conversion for Atlas185.
Keeping these computations independent of rooted graphon integration lowers
peak memory during kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas185

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Negative

/-! ### The graph -/

/-- Atlas185, with exactly the catalogue edge list. -/
def graph185 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4)]

instance : DecidableRel graph185.Adj := graphFromEdges_decidableAdj _ _

/-! ### Chromatic data, checked by surjective coloring counts. -/

/-- Check the catalogue edges directly, avoiding a graph adjacency computation for
all 36 ordered vertex pairs in every candidate coloring. -/
private def fastProper185 {j : ℕ} (y : Fin 6 → Fin j) : Prop :=
  y 0 ≠ y 1 ∧ y 0 ≠ y 2 ∧ y 0 ≠ y 4 ∧ y 0 ≠ y 5 ∧ y 1 ≠ y 2 ∧ y 1 ≠ y 4 ∧ y 1 ≠ y 5 ∧ y 2 ≠ y 3 ∧ y 2 ≠ y 5 ∧ y 3 ≠ y 4

private instance {j : ℕ} (y : Fin 6 → Fin j) : Decidable (fastProper185 y) := by
  unfold fastProper185
  infer_instance

private theorem isProper185_iff_fast {j : ℕ} (y : Fin 6 → Fin j) :
    IsProper graph185 y ↔ fastProper185 y := by
  constructor
  · intro h
    exact ⟨h 0 1 (by decide),h 0 2 (by decide),h 0 4 (by decide),h 0 5 (by decide),h 1 2 (by decide),h 1 4 (by decide),h 1 5 (by decide),h 2 3 (by decide),h 2 5 (by decide),h 3 4 (by decide)⟩
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [graph185,graphFromEdges,fastProper185,ne_comm]
    all_goals aesop

private def fastSurj185 (j : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin j)).filter
    (fun y => fastProper185 y ∧ Function.Surjective y)).card

private theorem surjCount185_eq_fast (j : ℕ) : surjCount graph185 j = fastSurj185 j := by
  unfold surjCount fastSurj185
  congr 1
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,isProper185_iff_fast]

theorem s185_0 : surjCount graph185 0 = 0 := by rw [surjCount185_eq_fast]; decide +kernel
theorem s185_1 : surjCount graph185 1 = 0 := by rw [surjCount185_eq_fast]; decide +kernel
theorem s185_2 : surjCount graph185 2 = 0 := by rw [surjCount185_eq_fast]; decide +kernel
theorem s185_3 : surjCount graph185 3 = 0 := by rw [surjCount185_eq_fast]; decide +kernel
theorem s185_4 : surjCount graph185 4 = 120 := by rw [surjCount185_eq_fast]; decide +kernel
theorem s185_5 : surjCount graph185 5 = 600 := by rw [surjCount185_eq_fast]; decide +kernel

theorem s185_6 : surjCount graph185 6 = 720 := by
  rw [surjCount_card graph185]
  decide

theorem count185 (k : ℕ) :
    properAssignmentCount graph185 k
      = 120 * k.choose 4 + 600 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph185 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s185_0, s185_1, s185_2, s185_3, s185_4, s185_5, s185_6]
  ring

theorem num185 : IsChromaticNumber graph185 4 where
  positive := by rw [count185]; decide
  zero_below k hk := by
    rw [count185]
    interval_cases k <;> decide

theorem chrom185 : IsChromaticPolynomial graph185
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph185 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph185

/-! ### The catalogue proposition -/

/-- The exact catalogue target polynomial. -/
noncomputable def target185 (p : ℝ) : ℝ :=
  (0)*p^0 + (4)*p^1 + (-26)*p^2 + (64)*p^3 + (-71)*p^4 + (30)*p^5

set_option maxHeartbeats 1000000 in
/-- **Atlas 185 satisfies the catalogue proposition, given the graphon bound.**
The graphon inequality is supplied separately by the interval SOS certificate. -/
theorem satisfiesLowerBound_185_of_bound
    (hbound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (2 : ℝ) / 3 ≤ cliqueDensity 2 W →
          target185 (cliqueDensity 2 W) ≤ homDensity graph185 W) :
    Taeyoung.SatisfiesLowerBound graph185 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph185 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph185) hP chrom185
  have hreq : r = 4 := IsChromaticNumber.unique (H := graph185) hr num185
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
    simp only [target185] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph185 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = target185 (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s185_0, s185_1, s185_2, s185_3, s185_4, s185_5, s185_6, target185,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

theorem target185_interval (s : Real) :
    target185 ((2+s)/3) = ((0)*s^0 + (4)*s^1 + (14)*s^2 + (24)*s^3 + (29)*s^4 + (10)*s^5)/81 := by
  unfold target185
  ring

#print axioms satisfiesLowerBound_185_of_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas185
