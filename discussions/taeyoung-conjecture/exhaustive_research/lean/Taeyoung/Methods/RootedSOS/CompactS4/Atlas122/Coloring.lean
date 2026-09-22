import Taeyoung.Methods.Negative.Chromatic

/-! The finite coloring counts and catalogue conversion for Atlas122.
Keeping these computations independent of rooted graphon integration lowers
peak memory during kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas122

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Negative

/-! ### The graph -/

/-- Atlas122, with exactly the catalogue edge list. -/
def graph122 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 3), (0, 4), (1, 2), (1, 5), (2, 3), (3, 4)]

instance : DecidableRel graph122.Adj := graphFromEdges_decidableAdj _ _

/-! ### Chromatic data

`χ_{H122}(r) = r(r-2)(r-1)²(r²-3r+3)`, whose last factor is irreducible, so the
attachment-tower route of `affineProd` does not apply.  The surjective-count
route does, exactly as for Atlas 148. -/

/-- Check the seven edges directly, avoiding a graph adjacency computation for
all 36 ordered vertex pairs in every candidate coloring. -/
private def fastProper122 {j : ℕ} (y : Fin 6 → Fin j) : Prop :=
  y 0 ≠ y 1 ∧ y 0 ≠ y 3 ∧ y 0 ≠ y 4 ∧ y 1 ≠ y 2 ∧ y 1 ≠ y 5 ∧ y 2 ≠ y 3 ∧ y 3 ≠ y 4

private instance {j : ℕ} (y : Fin 6 → Fin j) : Decidable (fastProper122 y) := by
  unfold fastProper122
  infer_instance

private theorem isProper122_iff_fast {j : ℕ} (y : Fin 6 → Fin j) :
    IsProper graph122 y ↔ fastProper122 y := by
  constructor
  · intro h
    exact ⟨h 0 1 (by decide),h 0 3 (by decide),h 0 4 (by decide),h 1 2 (by decide),h 1 5 (by decide),h 2 3 (by decide),h 3 4 (by decide)⟩
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [graph122,graphFromEdges,fastProper122,ne_comm]
    all_goals aesop

private def fastSurj122 (j : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin j)).filter
    (fun y => fastProper122 y ∧ Function.Surjective y)).card

private theorem surjCount122_eq_fast (j : ℕ) : surjCount graph122 j = fastSurj122 j := by
  unfold surjCount fastSurj122
  congr 1
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,isProper122_iff_fast]

theorem s122_0 : surjCount graph122 0 = 0 := by rw [surjCount122_eq_fast]; decide +kernel
theorem s122_1 : surjCount graph122 1 = 0 := by rw [surjCount122_eq_fast]; decide +kernel
theorem s122_2 : surjCount graph122 2 = 0 := by rw [surjCount122_eq_fast]; decide +kernel
theorem s122_3 : surjCount graph122 3 = 36 := by rw [surjCount122_eq_fast]; decide +kernel
theorem s122_4 : surjCount graph122 4 = 360 := by rw [surjCount122_eq_fast]; decide +kernel
theorem s122_5 : surjCount graph122 5 = 960 := by rw [surjCount122_eq_fast]; decide +kernel

theorem s122_6 : surjCount graph122 6 = 720 := by
  rw [surjCount_card graph122]
  decide

theorem count122 (k : ℕ) :
    properAssignmentCount graph122 k
      = 36 * k.choose 3 + 360 * k.choose 4 + 960 * k.choose 5
        + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph122 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s122_0, s122_1, s122_2, s122_3, s122_4, s122_5, s122_6]
  ring

theorem num122 : IsChromaticNumber graph122 3 where
  positive := by rw [count122]; decide
  zero_below k hk := by
    rw [count122]
    interval_cases k <;> decide

theorem chrom122 : IsChromaticPolynomial graph122
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph122 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph122

/-! ### The catalogue proposition -/

/-- `Φ_{H122}(p) = p²(2p-1)(p³+(1-p)³)`. -/
noncomputable def target122 (p : ℝ) : ℝ :=
  p ^ 2 * (2 * p - 1) * (p ^ 3 + (1 - p) ^ 3)

set_option maxHeartbeats 1000000 in
/-- **Atlas 122 satisfies the catalogue proposition, given the graphon bound.**
The graphon inequality is supplied separately by the interval SOS certificate. -/
theorem satisfiesLowerBound_122_of_bound
    (hbound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (1 : ℝ) / 2 ≤ cliqueDensity 2 W →
          target122 (cliqueDensity 2 W) ≤ homDensity graph122 W) :
    Taeyoung.SatisfiesLowerBound graph122 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph122 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph122) hP chrom122
  have hreq : r = 3 := IsChromaticNumber.unique (H := graph122) hr num122
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
    simp only [target122] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph122 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = target122 (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s122_0, s122_1, s122_2, s122_3, s122_4, s122_5, s122_6, target122,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

theorem target122_interval (s : Real) :
    target122 ((1+s)/2) = s*(s+1)^2*(3*s^2+1)/16 := by
  unfold target122
  ring

#print axioms satisfiesLowerBound_122_of_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas122
