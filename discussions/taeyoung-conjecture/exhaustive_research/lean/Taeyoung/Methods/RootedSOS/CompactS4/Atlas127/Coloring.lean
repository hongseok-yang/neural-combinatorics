import Taeyoung.Methods.Negative.Chromatic

/-! The finite coloring counts and catalogue conversion for Atlas127.
Keeping these computations independent of rooted graphon integration lowers
peak memory during kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas127

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Negative

/-! ### The graph -/

/-- Atlas127, with exactly the catalogue edge list. -/
def graph127 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 2), (0, 5), (1, 2), (1, 3), (2, 3), (3, 4), (4, 5)]

instance : DecidableRel graph127.Adj := graphFromEdges_decidableAdj _ _

/-! ### Chromatic data, checked by surjective coloring counts. -/

/-- Check the catalogue edges directly, avoiding a graph adjacency computation for
all 36 ordered vertex pairs in every candidate coloring. -/
private def fastProper127 {j : ℕ} (y : Fin 6 → Fin j) : Prop :=
  y 0 ≠ y 2 ∧ y 0 ≠ y 5 ∧ y 1 ≠ y 2 ∧ y 1 ≠ y 3 ∧ y 2 ≠ y 3 ∧ y 3 ≠ y 4 ∧ y 4 ≠ y 5

private instance {j : ℕ} (y : Fin 6 → Fin j) : Decidable (fastProper127 y) := by
  unfold fastProper127
  infer_instance

private theorem isProper127_iff_fast {j : ℕ} (y : Fin 6 → Fin j) :
    IsProper graph127 y ↔ fastProper127 y := by
  constructor
  · intro h
    exact ⟨h 0 2 (by decide),h 0 5 (by decide),h 1 2 (by decide),h 1 3 (by decide),h 2 3 (by decide),h 3 4 (by decide),h 4 5 (by decide)⟩
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [graph127,graphFromEdges,fastProper127,ne_comm]
    all_goals aesop

private def fastSurj127 (j : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin j)).filter
    (fun y => fastProper127 y ∧ Function.Surjective y)).card

private theorem surjCount127_eq_fast (j : ℕ) : surjCount graph127 j = fastSurj127 j := by
  unfold surjCount fastSurj127
  congr 1
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,isProper127_iff_fast]

theorem s127_0 : surjCount graph127 0 = 0 := by rw [surjCount127_eq_fast]; decide +kernel
theorem s127_1 : surjCount graph127 1 = 0 := by rw [surjCount127_eq_fast]; decide +kernel
theorem s127_2 : surjCount graph127 2 = 0 := by rw [surjCount127_eq_fast]; decide +kernel
theorem s127_3 : surjCount graph127 3 = 30 := by rw [surjCount127_eq_fast]; decide +kernel
theorem s127_4 : surjCount graph127 4 = 360 := by rw [surjCount127_eq_fast]; decide +kernel
theorem s127_5 : surjCount graph127 5 = 960 := by rw [surjCount127_eq_fast]; decide +kernel

theorem s127_6 : surjCount graph127 6 = 720 := by
  rw [surjCount_card graph127]
  decide

theorem count127 (k : ℕ) :
    properAssignmentCount graph127 k
      = 30 * k.choose 3 + 360 * k.choose 4 + 960 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph127 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s127_0, s127_1, s127_2, s127_3, s127_4, s127_5, s127_6]
  ring

theorem num127 : IsChromaticNumber graph127 3 where
  positive := by rw [count127]; decide
  zero_below k hk := by
    rw [count127]
    interval_cases k <;> decide

theorem chrom127 : IsChromaticPolynomial graph127
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph127 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph127

/-! ### The catalogue proposition -/

/-- The exact catalogue target polynomial. -/
noncomputable def target127 (p : ℝ) : ℝ :=
  (0)*p^0 + (1)*p^1 + (-6)*p^2 + (14)*p^3 + (-16)*p^4 + (8)*p^5

set_option maxHeartbeats 1000000 in
/-- **Atlas 127 satisfies the catalogue proposition, given the graphon bound.**
The graphon inequality is supplied separately by the interval SOS certificate. -/
theorem satisfiesLowerBound_127_of_bound
    (hbound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (1 : ℝ) / 2 ≤ cliqueDensity 2 W →
          target127 (cliqueDensity 2 W) ≤ homDensity graph127 W) :
    Taeyoung.SatisfiesLowerBound graph127 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph127 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph127) hP chrom127
  have hreq : r = 3 := IsChromaticNumber.unique (H := graph127) hr num127
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
    simp only [target127] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph127 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = target127 (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s127_0, s127_1, s127_2, s127_3, s127_4, s127_5, s127_6, target127,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

theorem target127_interval (s : Real) :
    target127 ((2+s)/3) = ((10)*s^0 + (49)*s^1 + (82)*s^2 + (62)*s^3 + (32)*s^4 + (8)*s^5)/243 := by
  unfold target127
  ring

#print axioms satisfiesLowerBound_127_of_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas127
