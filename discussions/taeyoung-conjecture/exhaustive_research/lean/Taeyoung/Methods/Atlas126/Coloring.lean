import Taeyoung.Methods.Negative.Chromatic

/-! The finite coloring counts and catalogue conversion for Atlas126.
Keeping these computations independent of rooted graphon integration lowers
peak memory during kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.Atlas126

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Negative

/-! ### The graph -/

/-- Atlas 126: the triangle `0,1,2` and the `4`-cycle `0,4,3,5` sharing the
single vertex `0`. -/
def graph126 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (1, 2), (0, 4), (0, 5), (3, 4), (3, 5)]

instance : DecidableRel graph126.Adj := graphFromEdges_decidableAdj _ _

/-! ### Chromatic data

`χ_{H₁₂₆}(r) = r(r-2)(r-1)²(r²-3r+3)`, whose last factor is irreducible, so the
attachment-tower route of `affineProd` does not apply.  The surjective-count
route does, exactly as for Atlas 148. -/

/-- Check the seven edges directly, avoiding a graph adjacency computation for
all 36 ordered vertex pairs in every candidate coloring. -/
private def fastProper126 {j : ℕ} (y : Fin 6 → Fin j) : Prop :=
  y 0 ≠ y 1 ∧ y 0 ≠ y 2 ∧ y 1 ≠ y 2 ∧ y 0 ≠ y 4 ∧
    y 0 ≠ y 5 ∧ y 3 ≠ y 4 ∧ y 3 ≠ y 5

private instance {j : ℕ} (y : Fin 6 → Fin j) : Decidable (fastProper126 y) := by
  unfold fastProper126
  infer_instance

private theorem isProper126_iff_fast {j : ℕ} (y : Fin 6 → Fin j) :
    IsProper graph126 y ↔ fastProper126 y := by
  constructor
  · intro h
    exact ⟨h 0 1 (by decide),h 0 2 (by decide),h 1 2 (by decide),
      h 0 4 (by decide),h 0 5 (by decide),h 3 4 (by decide),h 3 5 (by decide)⟩
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [graph126,graphFromEdges,fastProper126,ne_comm]
    exact Ne.symm h.1

private def fastSurj126 (j : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin j)).filter
    (fun y => fastProper126 y ∧ Function.Surjective y)).card

private theorem surjCount126_eq_fast (j : ℕ) : surjCount graph126 j = fastSurj126 j := by
  unfold surjCount fastSurj126
  congr 1
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,isProper126_iff_fast]

theorem s126_0 : surjCount graph126 0 = 0 := by rw [surjCount126_eq_fast]; decide +kernel
theorem s126_1 : surjCount graph126 1 = 0 := by rw [surjCount126_eq_fast]; decide +kernel
theorem s126_2 : surjCount graph126 2 = 0 := by rw [surjCount126_eq_fast]; decide +kernel
theorem s126_3 : surjCount graph126 3 = 36 := by rw [surjCount126_eq_fast]; decide +kernel
theorem s126_4 : surjCount graph126 4 = 360 := by rw [surjCount126_eq_fast]; decide +kernel
theorem s126_5 : surjCount graph126 5 = 960 := by rw [surjCount126_eq_fast]; decide +kernel

theorem s126_6 : surjCount graph126 6 = 720 := by
  rw [surjCount_card graph126]
  decide

theorem count126 (k : ℕ) :
    properAssignmentCount graph126 k
      = 36 * k.choose 3 + 360 * k.choose 4 + 960 * k.choose 5
        + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph126 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s126_0, s126_1, s126_2, s126_3, s126_4, s126_5, s126_6]
  ring

theorem num126 : IsChromaticNumber graph126 3 where
  positive := by rw [count126]; decide
  zero_below k hk := by
    rw [count126]
    interval_cases k <;> decide

theorem chrom126 : IsChromaticPolynomial graph126
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph126 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph126

/-! ### The catalogue proposition -/

/-- `Φ_{H₁₂₆}(p) = p²(2p-1)(p³+(1-p)³)`. -/
noncomputable def target126 (p : ℝ) : ℝ :=
  p ^ 2 * (2 * p - 1) * (p ^ 3 + (1 - p) ^ 3)

set_option maxHeartbeats 1000000 in
/-- **Atlas 126 satisfies the catalogue proposition, given the graphon bound.**
Only the scalar supporting plane of `notes/atlas126_...` is missing; every
chromatic and measure-theoretic step is discharged here. -/
theorem satisfiesLowerBound_126_of_bound
    (hbound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (1 : ℝ) / 2 ≤ cliqueDensity 2 W →
          target126 (cliqueDensity 2 W) ≤ homDensity graph126 W) :
    Taeyoung.SatisfiesLowerBound graph126 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph126 j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := graph126) hP chrom126
  have hreq : r = 3 := IsChromaticNumber.unique (H := graph126) hr num126
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
    simp only [target126] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 6) + 1),
            C ((surjCount graph126 j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ)))
        = target126 (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        s126_0, s126_1, s126_2, s126_3, s126_4, s126_5, s126_6, target126,
        eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

end Taeyoung.Methods.Atlas126
