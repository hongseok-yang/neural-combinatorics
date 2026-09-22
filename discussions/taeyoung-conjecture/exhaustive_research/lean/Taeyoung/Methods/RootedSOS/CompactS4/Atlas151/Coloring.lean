import Taeyoung.Methods.Negative.Chromatic

/-! The finite coloring counts and catalogue conversion for Atlas151.
Keeping these computations independent of rooted graphon integration lowers
peak memory during kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas151

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Negative

/-! ### The graph -/

/-- Atlas151, with exactly the catalogue edge list. -/
def graph151 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 4), (1, 2), (1, 5), (2, 3), (3, 4), (3, 5), (4, 5)]

instance : DecidableRel graph151.Adj := graphFromEdges_decidableAdj _ _

/-! ### Chromatic data, checked by surjective coloring counts. -/

/-- Check the catalogue edges directly, avoiding a graph adjacency computation for
all 36 ordered vertex pairs in every candidate coloring. -/
private def fastProper151 {j : ℕ} (y : Fin 6 → Fin j) : Prop :=
  y 0 ≠ y 1 ∧ y 0 ≠ y 4 ∧ y 1 ≠ y 2 ∧ y 1 ≠ y 5 ∧ y 2 ≠ y 3 ∧ y 3 ≠ y 4 ∧ y 3 ≠ y 5 ∧ y 4 ≠ y 5

private instance {j : ℕ} (y : Fin 6 → Fin j) : Decidable (fastProper151 y) := by
  unfold fastProper151
  infer_instance

private theorem isProper151_iff_fast {j : ℕ} (y : Fin 6 → Fin j) :
    IsProper graph151 y ↔ fastProper151 y := by
  constructor
  · intro h
    exact ⟨h 0 1 (by decide),h 0 4 (by decide),h 1 2 (by decide),h 1 5 (by decide),h 2 3 (by decide),h 3 4 (by decide),h 3 5 (by decide),h 4 5 (by decide)⟩
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [graph151,graphFromEdges,fastProper151,ne_comm]
    all_goals aesop

private def fastSurj151 (j : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin j)).filter
    (fun y => fastProper151 y ∧ Function.Surjective y)).card

private theorem surjCount151_eq_fast (j : ℕ) : surjCount graph151 j = fastSurj151 j := by
  unfold surjCount fastSurj151
  congr 1
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,isProper151_iff_fast]

theorem s151_0 : surjCount graph151 0 = 0 := by rw [surjCount151_eq_fast]; decide +kernel
theorem s151_1 : surjCount graph151 1 = 0 := by rw [surjCount151_eq_fast]; decide +kernel
theorem s151_2 : surjCount graph151 2 = 0 := by rw [surjCount151_eq_fast]; decide +kernel
theorem s151_3 : surjCount graph151 3 = 24 := by rw [surjCount151_eq_fast]; decide +kernel
theorem s151_4 : surjCount graph151 4 = 288 := by rw [surjCount151_eq_fast]; decide +kernel
theorem s151_5 : surjCount graph151 5 = 840 := by rw [surjCount151_eq_fast]; decide +kernel

theorem s151_6 : surjCount graph151 6 = 720 := by
  rw [surjCount_card graph151]
  decide

theorem count151 (k : ℕ) :
    properAssignmentCount graph151 k
      = 24 * k.choose 3 + 288 * k.choose 4 + 840 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph151 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s151_0, s151_1, s151_2, s151_3, s151_4, s151_5, s151_6]
  ring

theorem num151 : IsChromaticNumber graph151 3 where
  positive := by rw [count151]; decide
  zero_below k hk := by
    rw [count151]
    interval_cases k <;> decide

theorem chrom151 : IsChromaticPolynomial graph151
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph151 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph151

/-! ### The catalogue proposition -/

/-- The exact catalogue target polynomial. -/
noncomputable def target151 (p : ℝ) : ℝ :=
  (0)*p^0 + (2)*p^1 + (-13)*p^2 + (32)*p^3 + (-36)*p^4 + (16)*p^5

set_option maxHeartbeats 1000000 in
/-- **Atlas 151 satisfies the catalogue proposition, given the graphon bound.**
The graphon inequality is supplied separately by the interval SOS certificate. -/
theorem satisfiesLowerBound_151_of_bound
    (hbound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (1 : ℝ) / 2 ≤ cliqueDensity 2 W →
          target151 (cliqueDensity 2 W) ≤ homDensity graph151 W) :
    Taeyoung.SatisfiesLowerBound graph151 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph151 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph151) hP chrom151
  have hreq : r = 3 := IsChromaticNumber.unique (H := graph151) hr num151
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
    simp only [target151] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph151 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = target151 (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s151_0, s151_1, s151_2, s151_3, s151_4, s151_5, s151_6, target151,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

theorem target151_interval (s : Real) :
    target151 ((2+s)/3) = ((8)*s^0 + (38)*s^1 + (65)*s^2 + (64)*s^3 + (52)*s^4 + (16)*s^5)/243 := by
  unfold target151
  ring

#print axioms satisfiesLowerBound_151_of_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas151
