import Taeyoung.Methods.Negative.Chromatic

/-! The finite coloring counts and catalogue conversion for Atlas188.
Keeping these computations independent of rooted graphon integration lowers
peak memory during kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas188

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Negative

/-! ### The graph -/

/-- Atlas188, with exactly the catalogue edge list. -/
def graph188 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 4), (4, 5)]

instance : DecidableRel graph188.Adj := graphFromEdges_decidableAdj _ _

/-! ### Chromatic data, checked by surjective coloring counts. -/

/-- Check the catalogue edges directly, avoiding a graph adjacency computation for
all 36 ordered vertex pairs in every candidate coloring. -/
private def fastProper188 {j : ℕ} (y : Fin 6 → Fin j) : Prop :=
  y 0 ≠ y 1 ∧ y 0 ≠ y 2 ∧ y 0 ≠ y 5 ∧ y 1 ≠ y 2 ∧ y 1 ≠ y 3 ∧ y 1 ≠ y 5 ∧ y 2 ≠ y 3 ∧ y 2 ≠ y 4 ∧ y 3 ≠ y 4 ∧ y 4 ≠ y 5

private instance {j : ℕ} (y : Fin 6 → Fin j) : Decidable (fastProper188 y) := by
  unfold fastProper188
  infer_instance

private theorem isProper188_iff_fast {j : ℕ} (y : Fin 6 → Fin j) :
    IsProper graph188 y ↔ fastProper188 y := by
  constructor
  · intro h
    exact ⟨h 0 1 (by decide),h 0 2 (by decide),h 0 5 (by decide),h 1 2 (by decide),h 1 3 (by decide),h 1 5 (by decide),h 2 3 (by decide),h 2 4 (by decide),h 3 4 (by decide),h 4 5 (by decide)⟩
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [graph188,graphFromEdges,fastProper188,ne_comm]
    all_goals aesop

private def fastSurj188 (j : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin j)).filter
    (fun y => fastProper188 y ∧ Function.Surjective y)).card

private theorem surjCount188_eq_fast (j : ℕ) : surjCount graph188 j = fastSurj188 j := by
  unfold surjCount fastSurj188
  congr 1
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,isProper188_iff_fast]

theorem s188_0 : surjCount graph188 0 = 0 := by rw [surjCount188_eq_fast]; decide +kernel
theorem s188_1 : surjCount graph188 1 = 0 := by rw [surjCount188_eq_fast]; decide +kernel
theorem s188_2 : surjCount graph188 2 = 0 := by rw [surjCount188_eq_fast]; decide +kernel
theorem s188_3 : surjCount graph188 3 = 6 := by rw [surjCount188_eq_fast]; decide +kernel
theorem s188_4 : surjCount graph188 4 = 144 := by rw [surjCount188_eq_fast]; decide +kernel
theorem s188_5 : surjCount graph188 5 = 600 := by rw [surjCount188_eq_fast]; decide +kernel

theorem s188_6 : surjCount graph188 6 = 720 := by
  rw [surjCount_card graph188]
  decide

theorem count188 (k : ℕ) :
    properAssignmentCount graph188 k
      = 6 * k.choose 3 + 144 * k.choose 4 + 600 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph188 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s188_0, s188_1, s188_2, s188_3, s188_4, s188_5, s188_6]
  ring

theorem num188 : IsChromaticNumber graph188 3 where
  positive := by rw [count188]; decide
  zero_below k hk := by
    rw [count188]
    interval_cases k <;> decide

theorem chrom188 : IsChromaticPolynomial graph188
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph188 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph188

/-! ### The catalogue proposition -/

/-- The exact catalogue target polynomial. -/
noncomputable def target188 (p : ℝ) : ℝ :=
  (0)*p^0 + (5)*p^1 + (-32)*p^2 + (77)*p^3 + (-83)*p^4 + (34)*p^5

set_option maxHeartbeats 1000000 in
/-- **Atlas 188 satisfies the catalogue proposition, given the graphon bound.**
The graphon inequality is supplied separately by the interval SOS certificate. -/
theorem satisfiesLowerBound_188_of_bound
    (hbound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (1 : ℝ) / 2 ≤ cliqueDensity 2 W →
          target188 (cliqueDensity 2 W) ≤ homDensity graph188 W) :
    Taeyoung.SatisfiesLowerBound graph188 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph188 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph188) hP chrom188
  have hreq : r = 3 := IsChromaticNumber.unique (H := graph188) hr num188
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
    simp only [target188] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph188 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = target188 (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s188_0, s188_1, s188_2, s188_3, s188_4, s188_5, s188_6, target188,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

theorem target188_interval (s : Real) :
    target188 ((2+s)/3) = ((2)*s^0 + (17)*s^1 + (38)*s^2 + (61)*s^3 + (91)*s^4 + (34)*s^5)/243 := by
  unfold target188
  ring

#print axioms satisfiesLowerBound_188_of_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas188
