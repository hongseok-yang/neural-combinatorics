import Taeyoung.Methods.Negative.Chromatic

/-! The finite coloring counts and catalogue conversion for Atlas124.
Keeping these computations independent of rooted graphon integration lowers
peak memory during kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas124

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Negative

/-! ### The graph -/

/-- Atlas124, with exactly the catalogue edge list. -/
def graph124 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 4), (1, 2), (1, 5), (2, 3), (3, 4)]

instance : DecidableRel graph124.Adj := graphFromEdges_decidableAdj _ _

/-! ### Chromatic data

`χ_{H124}(r) = r(r-2)(r-1)²(r²-3r+3)`, whose last factor is irreducible, so the
attachment-tower route of `affineProd` does not apply.  The surjective-count
route does, exactly as for Atlas 148. -/

/-- Check the seven edges directly, avoiding a graph adjacency computation for
all 36 ordered vertex pairs in every candidate coloring. -/
private def fastProper124 {j : ℕ} (y : Fin 6 → Fin j) : Prop :=
  y 0 ≠ y 1 ∧ y 0 ≠ y 2 ∧ y 0 ≠ y 4 ∧ y 1 ≠ y 2 ∧ y 1 ≠ y 5 ∧ y 2 ≠ y 3 ∧ y 3 ≠ y 4

private instance {j : ℕ} (y : Fin 6 → Fin j) : Decidable (fastProper124 y) := by
  unfold fastProper124
  infer_instance

private theorem isProper124_iff_fast {j : ℕ} (y : Fin 6 → Fin j) :
    IsProper graph124 y ↔ fastProper124 y := by
  constructor
  · intro h
    exact ⟨h 0 1 (by decide),h 0 2 (by decide),h 0 4 (by decide),h 1 2 (by decide),h 1 5 (by decide),h 2 3 (by decide),h 3 4 (by decide)⟩
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [graph124,graphFromEdges,fastProper124,ne_comm]
    all_goals aesop

private def fastSurj124 (j : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin j)).filter
    (fun y => fastProper124 y ∧ Function.Surjective y)).card

private theorem surjCount124_eq_fast (j : ℕ) : surjCount graph124 j = fastSurj124 j := by
  unfold surjCount fastSurj124
  congr 1
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,isProper124_iff_fast]

theorem s124_0 : surjCount graph124 0 = 0 := by rw [surjCount124_eq_fast]; decide +kernel
theorem s124_1 : surjCount graph124 1 = 0 := by rw [surjCount124_eq_fast]; decide +kernel
theorem s124_2 : surjCount graph124 2 = 0 := by rw [surjCount124_eq_fast]; decide +kernel
theorem s124_3 : surjCount graph124 3 = 36 := by rw [surjCount124_eq_fast]; decide +kernel
theorem s124_4 : surjCount graph124 4 = 360 := by rw [surjCount124_eq_fast]; decide +kernel
theorem s124_5 : surjCount graph124 5 = 960 := by rw [surjCount124_eq_fast]; decide +kernel

theorem s124_6 : surjCount graph124 6 = 720 := by
  rw [surjCount_card graph124]
  decide

theorem count124 (k : ℕ) :
    properAssignmentCount graph124 k
      = 36 * k.choose 3 + 360 * k.choose 4 + 960 * k.choose 5
        + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph124 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s124_0, s124_1, s124_2, s124_3, s124_4, s124_5, s124_6]
  ring

theorem num124 : IsChromaticNumber graph124 3 where
  positive := by rw [count124]; decide
  zero_below k hk := by
    rw [count124]
    interval_cases k <;> decide

theorem chrom124 : IsChromaticPolynomial graph124
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph124 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph124

/-! ### The catalogue proposition -/

/-- `Φ_{H124}(p) = p²(2p-1)(p³+(1-p)³)`. -/
noncomputable def target124 (p : ℝ) : ℝ :=
  p ^ 2 * (2 * p - 1) * (p ^ 3 + (1 - p) ^ 3)

set_option maxHeartbeats 1000000 in
/-- **Atlas 124 satisfies the catalogue proposition, given the graphon bound.**
The graphon inequality is supplied separately by the interval SOS certificate. -/
theorem satisfiesLowerBound_124_of_bound
    (hbound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (1 : ℝ) / 2 ≤ cliqueDensity 2 W →
          target124 (cliqueDensity 2 W) ≤ homDensity graph124 W) :
    Taeyoung.SatisfiesLowerBound graph124 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph124 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph124) hP chrom124
  have hreq : r = 3 := IsChromaticNumber.unique (H := graph124) hr num124
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
    simp only [target124] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph124 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = target124 (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s124_0, s124_1, s124_2, s124_3, s124_4, s124_5, s124_6, target124,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

theorem target124_interval (s : Real) :
    target124 ((1+s)/2) = s*(s+1)^2*(3*s^2+1)/16 := by
  unfold target124
  ring

#print axioms satisfiesLowerBound_124_of_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas124
