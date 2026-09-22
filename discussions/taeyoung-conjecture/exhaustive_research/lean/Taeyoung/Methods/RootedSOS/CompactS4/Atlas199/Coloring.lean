import Taeyoung.Methods.Negative.Chromatic

/-! The finite coloring counts and catalogue conversion for Atlas199.
Keeping these computations independent of rooted graphon integration lowers
peak memory during kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas199

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Negative

/-! ### The graph -/

/-- Atlas199, with exactly the catalogue edge list. -/
def graph199 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 3), (0, 5), (1, 2), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (4, 5)]

instance : DecidableRel graph199.Adj := graphFromEdges_decidableAdj _ _

/-! ### Chromatic data, checked by surjective coloring counts. -/

/-- Check the catalogue edges directly, avoiding a graph adjacency computation for
all 36 ordered vertex pairs in every candidate coloring. -/
private def fastProper199 {j : ℕ} (y : Fin 6 → Fin j) : Prop :=
  y 0 ≠ y 1 ∧ y 0 ≠ y 3 ∧ y 0 ≠ y 5 ∧ y 1 ≠ y 2 ∧ y 1 ≠ y 4 ∧ y 1 ≠ y 5 ∧ y 2 ≠ y 3 ∧ y 2 ≠ y 4 ∧ y 2 ≠ y 5 ∧ y 3 ≠ y 4 ∧ y 4 ≠ y 5

private instance {j : ℕ} (y : Fin 6 → Fin j) : Decidable (fastProper199 y) := by
  unfold fastProper199
  infer_instance

private theorem isProper199_iff_fast {j : ℕ} (y : Fin 6 → Fin j) :
    IsProper graph199 y ↔ fastProper199 y := by
  constructor
  · intro h
    exact ⟨h 0 1 (by decide),h 0 3 (by decide),h 0 5 (by decide),h 1 2 (by decide),h 1 4 (by decide),h 1 5 (by decide),h 2 3 (by decide),h 2 4 (by decide),h 2 5 (by decide),h 3 4 (by decide),h 4 5 (by decide)⟩
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [graph199,graphFromEdges,fastProper199,ne_comm]
    all_goals aesop

private def fastSurj199 (j : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin j)).filter
    (fun y => fastProper199 y ∧ Function.Surjective y)).card

private theorem surjCount199_eq_fast (j : ℕ) : surjCount graph199 j = fastSurj199 j := by
  unfold surjCount fastSurj199
  congr 1
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,isProper199_iff_fast]

theorem s199_0 : surjCount graph199 0 = 0 := by rw [surjCount199_eq_fast]; decide +kernel
theorem s199_1 : surjCount graph199 1 = 0 := by rw [surjCount199_eq_fast]; decide +kernel
theorem s199_2 : surjCount graph199 2 = 0 := by rw [surjCount199_eq_fast]; decide +kernel
theorem s199_3 : surjCount graph199 3 = 0 := by rw [surjCount199_eq_fast]; decide +kernel
theorem s199_4 : surjCount graph199 4 = 96 := by rw [surjCount199_eq_fast]; decide +kernel
theorem s199_5 : surjCount graph199 5 = 480 := by rw [surjCount199_eq_fast]; decide +kernel

theorem s199_6 : surjCount graph199 6 = 720 := by
  rw [surjCount_card graph199]
  decide

theorem count199 (k : ℕ) :
    properAssignmentCount graph199 k
      = 96 * k.choose 4 + 480 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph199 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s199_0, s199_1, s199_2, s199_3, s199_4, s199_5, s199_6]
  ring

theorem num199 : IsChromaticNumber graph199 4 where
  positive := by rw [count199]; decide
  zero_below k hk := by
    rw [count199]
    interval_cases k <;> decide

theorem chrom199 : IsChromaticPolynomial graph199
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph199 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph199

/-! ### The catalogue proposition -/

/-- The exact catalogue target polynomial. -/
noncomputable def target199 (p : ℝ) : ℝ :=
  (0)*p^0 + (8)*p^1 + (-50)*p^2 + (117)*p^3 + (-122)*p^4 + (48)*p^5

set_option maxHeartbeats 1000000 in
/-- **Atlas 199 satisfies the catalogue proposition, given the graphon bound.**
The graphon inequality is supplied separately by the interval SOS certificate. -/
theorem satisfiesLowerBound_199_of_bound
    (hbound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (2 : ℝ) / 3 ≤ cliqueDensity 2 W →
          target199 (cliqueDensity 2 W) ≤ homDensity graph199 W) :
    Taeyoung.SatisfiesLowerBound graph199 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph199 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph199) hP chrom199
  have hreq : r = 4 := IsChromaticNumber.unique (H := graph199) hr num199
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
    simp only [target199] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph199 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = target199 (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s199_0, s199_1, s199_2, s199_3, s199_4, s199_5, s199_6, target199,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

theorem target199_interval (s : Real) :
    target199 ((2+s)/3) = ((0)*s^0 + (4)*s^1 + (8)*s^2 + (15)*s^3 + (38)*s^4 + (16)*s^5)/81 := by
  unfold target199
  ring

#print axioms satisfiesLowerBound_199_of_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas199
