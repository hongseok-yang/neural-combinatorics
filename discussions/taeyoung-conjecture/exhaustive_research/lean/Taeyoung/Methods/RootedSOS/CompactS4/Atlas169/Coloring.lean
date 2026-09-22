import Taeyoung.Methods.Negative.Chromatic

/-! The finite coloring counts and catalogue conversion for Atlas169.
Keeping these computations independent of rooted graphon integration lowers
peak memory during kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas169

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Negative

/-! ### The graph -/

/-- Atlas169, with exactly the catalogue edge list. -/
def graph169 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (2, 3), (2, 5), (3, 4)]

instance : DecidableRel graph169.Adj := graphFromEdges_decidableAdj _ _

/-! ### Chromatic data, checked by surjective coloring counts. -/

/-- Check the catalogue edges directly, avoiding a graph adjacency computation for
all 36 ordered vertex pairs in every candidate coloring. -/
private def fastProper169 {j : ℕ} (y : Fin 6 → Fin j) : Prop :=
  y 0 ≠ y 1 ∧ y 0 ≠ y 2 ∧ y 0 ≠ y 4 ∧ y 0 ≠ y 5 ∧ y 1 ≠ y 2 ∧ y 1 ≠ y 5 ∧ y 2 ≠ y 3 ∧ y 2 ≠ y 5 ∧ y 3 ≠ y 4

private instance {j : ℕ} (y : Fin 6 → Fin j) : Decidable (fastProper169 y) := by
  unfold fastProper169
  infer_instance

private theorem isProper169_iff_fast {j : ℕ} (y : Fin 6 → Fin j) :
    IsProper graph169 y ↔ fastProper169 y := by
  constructor
  · intro h
    exact ⟨h 0 1 (by decide),h 0 2 (by decide),h 0 4 (by decide),h 0 5 (by decide),h 1 2 (by decide),h 1 5 (by decide),h 2 3 (by decide),h 2 5 (by decide),h 3 4 (by decide)⟩
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [graph169,graphFromEdges,fastProper169,ne_comm]
    all_goals aesop

private def fastSurj169 (j : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin j)).filter
    (fun y => fastProper169 y ∧ Function.Surjective y)).card

private theorem surjCount169_eq_fast (j : ℕ) : surjCount graph169 j = fastSurj169 j := by
  unfold surjCount fastSurj169
  congr 1
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,isProper169_iff_fast]

theorem s169_0 : surjCount graph169 0 = 0 := by rw [surjCount169_eq_fast]; decide +kernel
theorem s169_1 : surjCount graph169 1 = 0 := by rw [surjCount169_eq_fast]; decide +kernel
theorem s169_2 : surjCount graph169 2 = 0 := by rw [surjCount169_eq_fast]; decide +kernel
theorem s169_3 : surjCount graph169 3 = 0 := by rw [surjCount169_eq_fast]; decide +kernel
theorem s169_4 : surjCount graph169 4 = 168 := by rw [surjCount169_eq_fast]; decide +kernel
theorem s169_5 : surjCount graph169 5 = 720 := by rw [surjCount169_eq_fast]; decide +kernel

theorem s169_6 : surjCount graph169 6 = 720 := by
  rw [surjCount_card graph169]
  decide

theorem count169 (k : ℕ) :
    properAssignmentCount graph169 k
      = 168 * k.choose 4 + 720 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph169 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s169_0, s169_1, s169_2, s169_3, s169_4, s169_5, s169_6]
  ring

theorem num169 : IsChromaticNumber graph169 4 where
  positive := by rw [count169]; decide
  zero_below k hk := by
    rw [count169]
    interval_cases k <;> decide

theorem chrom169 : IsChromaticPolynomial graph169
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph169 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph169

/-! ### The catalogue proposition -/

/-- The exact catalogue target polynomial. -/
noncomputable def target169 (p : ℝ) : ℝ :=
  (0)*p^0 + (2)*p^1 + (-13)*p^2 + (33)*p^3 + (-39)*p^4 + (18)*p^5

set_option maxHeartbeats 1000000 in
/-- **Atlas 169 satisfies the catalogue proposition, given the graphon bound.**
The graphon inequality is supplied separately by the interval SOS certificate. -/
theorem satisfiesLowerBound_169_of_bound
    (hbound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (2 : ℝ) / 3 ≤ cliqueDensity 2 W →
          target169 (cliqueDensity 2 W) ≤ homDensity graph169 W) :
    Taeyoung.SatisfiesLowerBound graph169 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph169 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph169) hP chrom169
  have hreq : r = 4 := IsChromaticNumber.unique (H := graph169) hr num169
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
    simp only [target169] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph169 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = target169 (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s169_0, s169_1, s169_2, s169_3, s169_4, s169_5, s169_6, target169,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

theorem target169_interval (s : Real) :
    target169 ((2+s)/3) = ((0)*s^0 + (6)*s^1 + (21)*s^2 + (27)*s^3 + (21)*s^4 + (6)*s^5)/81 := by
  unfold target169
  ring

#print axioms satisfiesLowerBound_169_of_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas169
