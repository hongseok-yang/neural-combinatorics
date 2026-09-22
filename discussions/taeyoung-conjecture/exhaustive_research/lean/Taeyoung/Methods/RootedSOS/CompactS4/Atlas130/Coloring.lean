import Taeyoung.Methods.Negative.Chromatic

/-! The finite coloring counts and catalogue conversion for Atlas130.
Keeping these computations independent of rooted graphon integration lowers
peak memory during kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas130

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Negative

/-! ### The graph -/

/-- Atlas130, with exactly the catalogue edge list. -/
def graph130 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 5)]

instance : DecidableRel graph130.Adj := graphFromEdges_decidableAdj _ _

/-! ### Chromatic data, checked by surjective coloring counts. -/

/-- Check the catalogue edges directly, avoiding a graph adjacency computation for
all 36 ordered vertex pairs in every candidate coloring. -/
private def fastProper130 {j : ℕ} (y : Fin 6 → Fin j) : Prop :=
  y 0 ≠ y 1 ∧ y 0 ≠ y 2 ∧ y 0 ≠ y 3 ∧ y 1 ≠ y 2 ∧ y 3 ≠ y 4 ∧ y 3 ≠ y 5 ∧ y 4 ≠ y 5

private instance {j : ℕ} (y : Fin 6 → Fin j) : Decidable (fastProper130 y) := by
  unfold fastProper130
  infer_instance

private theorem isProper130_iff_fast {j : ℕ} (y : Fin 6 → Fin j) :
    IsProper graph130 y ↔ fastProper130 y := by
  constructor
  · intro h
    exact ⟨h 0 1 (by decide),h 0 2 (by decide),h 0 3 (by decide),h 1 2 (by decide),h 3 4 (by decide),h 3 5 (by decide),h 4 5 (by decide)⟩
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [graph130,graphFromEdges,fastProper130,ne_comm]
    all_goals aesop

private def fastSurj130 (j : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin j)).filter
    (fun y => fastProper130 y ∧ Function.Surjective y)).card

private theorem surjCount130_eq_fast (j : ℕ) : surjCount graph130 j = fastSurj130 j := by
  unfold surjCount fastSurj130
  congr 1
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,isProper130_iff_fast]

theorem s130_0 : surjCount graph130 0 = 0 := by rw [surjCount130_eq_fast]; decide +kernel
theorem s130_1 : surjCount graph130 1 = 0 := by rw [surjCount130_eq_fast]; decide +kernel
theorem s130_2 : surjCount graph130 2 = 0 := by rw [surjCount130_eq_fast]; decide +kernel
theorem s130_3 : surjCount graph130 3 = 24 := by rw [surjCount130_eq_fast]; decide +kernel
theorem s130_4 : surjCount graph130 4 = 336 := by rw [surjCount130_eq_fast]; decide +kernel
theorem s130_5 : surjCount graph130 5 = 960 := by rw [surjCount130_eq_fast]; decide +kernel

theorem s130_6 : surjCount graph130 6 = 720 := by
  rw [surjCount_card graph130]
  decide

theorem count130 (k : ℕ) :
    properAssignmentCount graph130 k
      = 24 * k.choose 3 + 336 * k.choose 4 + 960 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph130 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s130_0, s130_1, s130_2, s130_3, s130_4, s130_5, s130_6]
  ring

theorem num130 : IsChromaticNumber graph130 3 where
  positive := by rw [count130]; decide
  zero_below k hk := by
    rw [count130]
    interval_cases k <;> decide

theorem chrom130 : IsChromaticPolynomial graph130
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph130 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph130

/-! ### The catalogue proposition -/

/-- The exact catalogue target polynomial. -/
noncomputable def target130 (p : ℝ) : ℝ :=
  (0)*p^0 + (0)*p^1 + (0)*p^2 + (1)*p^3 + (-4)*p^4 + (4)*p^5

set_option maxHeartbeats 1000000 in
/-- **Atlas 130 satisfies the catalogue proposition, given the graphon bound.**
The graphon inequality is supplied separately by the interval SOS certificate. -/
theorem satisfiesLowerBound_130_of_bound
    (hbound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (1 : ℝ) / 2 ≤ cliqueDensity 2 W →
          target130 (cliqueDensity 2 W) ≤ homDensity graph130 W) :
    Taeyoung.SatisfiesLowerBound graph130 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph130 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph130) hP chrom130
  have hreq : r = 3 := IsChromaticNumber.unique (H := graph130) hr num130
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
    simp only [target130] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph130 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = target130 (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s130_0, s130_1, s130_2, s130_3, s130_4, s130_5, s130_6, target130,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

theorem target130_interval (s : Real) :
    target130 ((2+s)/3) = ((8)*s^0 + (44)*s^1 + (86)*s^2 + (73)*s^3 + (28)*s^4 + (4)*s^5)/243 := by
  unfold target130
  ring

#print axioms satisfiesLowerBound_130_of_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas130
