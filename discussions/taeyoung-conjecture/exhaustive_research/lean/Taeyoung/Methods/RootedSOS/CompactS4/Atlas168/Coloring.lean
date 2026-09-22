import Taeyoung.Methods.Negative.Chromatic

/-! The finite coloring counts and catalogue conversion for Atlas168.
Keeping these computations independent of rooted graphon integration lowers
peak memory during kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas168

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Negative

/-! ### The graph -/

/-- Atlas168, with exactly the catalogue edge list. -/
def graph168 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 2), (0, 3), (0, 5), (1, 2), (1, 3), (2, 3), (2, 4), (3, 4), (4, 5)]

instance : DecidableRel graph168.Adj := graphFromEdges_decidableAdj _ _

/-! ### Chromatic data, checked by surjective coloring counts. -/

/-- Check the catalogue edges directly, avoiding a graph adjacency computation for
all 36 ordered vertex pairs in every candidate coloring. -/
private def fastProper168 {j : ℕ} (y : Fin 6 → Fin j) : Prop :=
  y 0 ≠ y 2 ∧ y 0 ≠ y 3 ∧ y 0 ≠ y 5 ∧ y 1 ≠ y 2 ∧ y 1 ≠ y 3 ∧ y 2 ≠ y 3 ∧ y 2 ≠ y 4 ∧ y 3 ≠ y 4 ∧ y 4 ≠ y 5

private instance {j : ℕ} (y : Fin 6 → Fin j) : Decidable (fastProper168 y) := by
  unfold fastProper168
  infer_instance

private theorem isProper168_iff_fast {j : ℕ} (y : Fin 6 → Fin j) :
    IsProper graph168 y ↔ fastProper168 y := by
  constructor
  · intro h
    exact ⟨h 0 2 (by decide),h 0 3 (by decide),h 0 5 (by decide),h 1 2 (by decide),h 1 3 (by decide),h 2 3 (by decide),h 2 4 (by decide),h 3 4 (by decide),h 4 5 (by decide)⟩
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [graph168,graphFromEdges,fastProper168,ne_comm]
    all_goals aesop

private def fastSurj168 (j : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin j)).filter
    (fun y => fastProper168 y ∧ Function.Surjective y)).card

private theorem surjCount168_eq_fast (j : ℕ) : surjCount graph168 j = fastSurj168 j := by
  unfold surjCount fastSurj168
  congr 1
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,isProper168_iff_fast]

theorem s168_0 : surjCount graph168 0 = 0 := by rw [surjCount168_eq_fast]; decide +kernel
theorem s168_1 : surjCount graph168 1 = 0 := by rw [surjCount168_eq_fast]; decide +kernel
theorem s168_2 : surjCount graph168 2 = 0 := by rw [surjCount168_eq_fast]; decide +kernel
theorem s168_3 : surjCount graph168 3 = 12 := by rw [surjCount168_eq_fast]; decide +kernel
theorem s168_4 : surjCount graph168 4 = 192 := by rw [surjCount168_eq_fast]; decide +kernel
theorem s168_5 : surjCount graph168 5 = 720 := by rw [surjCount168_eq_fast]; decide +kernel

theorem s168_6 : surjCount graph168 6 = 720 := by
  rw [surjCount_card graph168]
  decide

theorem count168 (k : ℕ) :
    properAssignmentCount graph168 k
      = 12 * k.choose 3 + 192 * k.choose 4 + 720 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph168 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s168_0, s168_1, s168_2, s168_3, s168_4, s168_5, s168_6]
  ring

theorem num168 : IsChromaticNumber graph168 3 where
  positive := by rw [count168]; decide
  zero_below k hk := by
    rw [count168]
    interval_cases k <;> decide

theorem chrom168 : IsChromaticPolynomial graph168
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph168 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph168

/-! ### The catalogue proposition -/

/-- The exact catalogue target polynomial. -/
noncomputable def target168 (p : ℝ) : ℝ :=
  (0)*p^0 + (2)*p^1 + (-14)*p^2 + (37)*p^3 + (-44)*p^4 + (20)*p^5

set_option maxHeartbeats 1000000 in
/-- **Atlas 168 satisfies the catalogue proposition, given the graphon bound.**
The graphon inequality is supplied separately by the interval SOS certificate. -/
theorem satisfiesLowerBound_168_of_bound
    (hbound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (1 : ℝ) / 2 ≤ cliqueDensity 2 W →
          target168 (cliqueDensity 2 W) ≤ homDensity graph168 W) :
    Taeyoung.SatisfiesLowerBound graph168 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph168 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph168) hP chrom168
  have hreq : r = 3 := IsChromaticNumber.unique (H := graph168) hr num168
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
    simp only [target168] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph168 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = target168 (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s168_0, s168_1, s168_2, s168_3, s168_4, s168_5, s168_6, target168,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

theorem target168_interval (s : Real) :
    target168 ((2+s)/3) = ((4)*s^0 + (22)*s^1 + (52)*s^2 + (77)*s^3 + (68)*s^4 + (20)*s^5)/243 := by
  unfold target168
  ring

#print axioms satisfiesLowerBound_168_of_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas168
