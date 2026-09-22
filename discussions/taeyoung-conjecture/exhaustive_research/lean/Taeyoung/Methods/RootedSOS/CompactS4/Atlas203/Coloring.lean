import Taeyoung.Methods.Negative.Chromatic

/-! The finite coloring counts and catalogue conversion for Atlas203.
Keeping these computations independent of rooted graphon integration lowers
peak memory during kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas203

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Negative

/-! ### The graph -/

/-- Atlas203, with exactly the catalogue edge list. -/
def graph203 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4), (4, 5)]

instance : DecidableRel graph203.Adj := graphFromEdges_decidableAdj _ _

/-! ### Chromatic data, checked by surjective coloring counts. -/

/-- Check the catalogue edges directly, avoiding a graph adjacency computation for
all 36 ordered vertex pairs in every candidate coloring. -/
private def fastProper203 {j : ℕ} (y : Fin 6 → Fin j) : Prop :=
  y 0 ≠ y 1 ∧ y 0 ≠ y 2 ∧ y 0 ≠ y 3 ∧ y 0 ≠ y 5 ∧ y 1 ≠ y 2 ∧ y 1 ≠ y 3 ∧ y 1 ≠ y 4 ∧ y 1 ≠ y 5 ∧ y 2 ≠ y 3 ∧ y 2 ≠ y 4 ∧ y 3 ≠ y 4 ∧ y 4 ≠ y 5

private instance {j : ℕ} (y : Fin 6 → Fin j) : Decidable (fastProper203 y) := by
  unfold fastProper203
  infer_instance

private theorem isProper203_iff_fast {j : ℕ} (y : Fin 6 → Fin j) :
    IsProper graph203 y ↔ fastProper203 y := by
  constructor
  · intro h
    exact ⟨h 0 1 (by decide),h 0 2 (by decide),h 0 3 (by decide),h 0 5 (by decide),h 1 2 (by decide),h 1 3 (by decide),h 1 4 (by decide),h 1 5 (by decide),h 2 3 (by decide),h 2 4 (by decide),h 3 4 (by decide),h 4 5 (by decide)⟩
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [graph203,graphFromEdges,fastProper203,ne_comm]
    all_goals aesop

private def fastSurj203 (j : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin j)).filter
    (fun y => fastProper203 y ∧ Function.Surjective y)).card

private theorem surjCount203_eq_fast (j : ℕ) : surjCount graph203 j = fastSurj203 j := by
  unfold surjCount fastSurj203
  congr 1
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,isProper203_iff_fast]

theorem s203_0 : surjCount graph203 0 = 0 := by rw [surjCount203_eq_fast]; decide +kernel
theorem s203_1 : surjCount graph203 1 = 0 := by rw [surjCount203_eq_fast]; decide +kernel
theorem s203_2 : surjCount graph203 2 = 0 := by rw [surjCount203_eq_fast]; decide +kernel
theorem s203_3 : surjCount graph203 3 = 0 := by rw [surjCount203_eq_fast]; decide +kernel
theorem s203_4 : surjCount graph203 4 = 48 := by rw [surjCount203_eq_fast]; decide +kernel
theorem s203_5 : surjCount graph203 5 = 360 := by rw [surjCount203_eq_fast]; decide +kernel

theorem s203_6 : surjCount graph203 6 = 720 := by
  rw [surjCount_card graph203]
  decide

theorem count203 (k : ℕ) :
    properAssignmentCount graph203 k
      = 48 * k.choose 4 + 360 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph203 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s203_0, s203_1, s203_2, s203_3, s203_4, s203_5, s203_6]
  ring

theorem num203 : IsChromaticNumber graph203 4 where
  positive := by rw [count203]; decide
  zero_below k hk := by
    rw [count203]
    interval_cases k <;> decide

theorem chrom203 : IsChromaticPolynomial graph203
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph203 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph203

/-! ### The catalogue proposition -/

/-- The exact catalogue target polynomial. -/
noncomputable def target203 (p : ℝ) : ℝ :=
  (0)*p^0 + (10)*p^1 + (-63)*p^2 + (148)*p^3 + (-154)*p^4 + (60)*p^5

set_option maxHeartbeats 1000000 in
/-- **Atlas 203 satisfies the catalogue proposition, given the graphon bound.**
The graphon inequality is supplied separately by the interval SOS certificate. -/
theorem satisfiesLowerBound_203_of_bound
    (hbound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (2 : ℝ) / 3 ≤ cliqueDensity 2 W →
          target203 (cliqueDensity 2 W) ≤ homDensity graph203 W) :
    Taeyoung.SatisfiesLowerBound graph203 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph203 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph203) hP chrom203
  have hreq : r = 4 := IsChromaticNumber.unique (H := graph203) hr num203
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
    simp only [target203] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph203 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = target203 (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s203_0, s203_1, s203_2, s203_3, s203_4, s203_5, s203_6, target203,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

theorem target203_interval (s : Real) :
    target203 ((3+s)/4) = ((3)*s^0 + (19)*s^1 + (54)*s^2 + (94)*s^3 + (71)*s^4 + (15)*s^5)/256 := by
  unfold target203
  ring

#print axioms satisfiesLowerBound_203_of_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas203
