import Taeyoung.Methods.Negative.StepGraphon
import Taeyoung.Methods.Negative.Chromatic

/-!
# The Turán-local negative rows

Atlas 166, 172 and 206.  Their witnesses come from
`notes/turan_local_and_high_density_negative_tests.tex`: a balanced Turán
graphon perturbed by `ε = 1/4` on selected cells.  Each is a rational step
graphon on `Fin k` with the uniform measure, so `Methods/Negative/StepGraphon`
applies with numerator matrix `N` and scale `s = 4`.

* **166, 172** — the *two-scale* witness: split both classes of `T₂` in half and
  put `ε` between the two halves inside each original class.  Four equal parts,
  `N i j = 4` across the original classes, `1` between halves of the same class,
  `0` inside a half.
* **206** — the *one-diagonal* witness: `T₃` with `ε` throughout one diagonal
  class.  Three equal parts, `N i j = 4` off the diagonal, `1` at `(0,0)` and
  `0` at the other two diagonal cells.

Each density reduces to one kernel evaluation of a sum of naturals over
`V → Fin k` (`4⁶ = 4096` or `3⁶ = 729` assignments).  The chromatic side reuses
`Methods/Negative/Chromatic`, exactly as the tensor rows do.

Atlas 152 is **not** here: its five parts have unequal masses, so it needs a
weighted finite measure rather than the uniform one.
-/

open Finset Polynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Taeyoung.Methods.Negative

open Taeyoung Taeyoung.Methods.PureChordal MeasureTheory

/-! ### The two witnesses -/

/-- The two-scale witness at `ε = 1/4`, as a numerator matrix over `s = 4`. -/
def twoScaleN : Fin 4 → Fin 4 → ℕ :=
  ![![0, 1, 4, 4], ![1, 0, 4, 4], ![4, 4, 0, 1], ![4, 4, 1, 0]]

theorem twoScaleN_symm : ∀ i j, twoScaleN i j = twoScaleN j i := by decide
theorem twoScaleN_le : ∀ i j, twoScaleN i j ≤ 4 := by decide

/-- `U_{1/4}` of the note. -/
noncomputable def twoScaleW : Graphon (Fin 4) (finiteUniformMeasure (Fin 4)) :=
  stepGraphon 4 4 twoScaleN twoScaleN_symm twoScaleN_le

/-- The one-diagonal witness at `ε = 1/4`, as a numerator matrix over `s = 4`. -/
def oneDiagN : Fin 3 → Fin 3 → ℕ :=
  ![![1, 4, 4], ![4, 0, 4], ![4, 4, 0]]

theorem oneDiagN_symm : ∀ i j, oneDiagN i j = oneDiagN j i := by decide
theorem oneDiagN_le : ∀ i j, oneDiagN i j ≤ 4 := by decide

/-- `V_{1/4}` of the note. -/
noncomputable def oneDiagW : Graphon (Fin 3) (finiteUniformMeasure (Fin 3)) :=
  stepGraphon 3 4 oneDiagN oneDiagN_symm oneDiagN_le

/-! ### Their edge densities -/

theorem sumPair_twoScale : ∑ z : Fin 2 → Fin 4, twoScaleN (z 0) (z 1) = 36 := by
  decide +kernel

theorem sumPair_oneDiag : ∑ z : Fin 2 → Fin 3, oneDiagN (z 0) (z 1) = 25 := by
  decide +kernel

theorem cliqueDensity_twoScale : cliqueDensity 2 twoScaleW = 9 / 16 := by
  rw [cliqueDensity_two_of_natWeight twoScaleW (fun z ↦ twoScaleN (z 0) (z 1))
    ((4 : ℝ)) (fun z ↦ rfl), sumPair_twoScale]
  norm_num

theorem cliqueDensity_oneDiag : cliqueDensity 2 oneDiagW = 25 / 36 := by
  rw [cliqueDensity_two_of_natWeight oneDiagW (fun z ↦ oneDiagN (z 0) (z 1))
    ((4 : ℝ)) (fun z ↦ rfl), sumPair_oneDiag]
  norm_num

/-! ### Atlas 166 -/

def graph166 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 3), (0, 4), (0, 5), (1, 2), (1, 5), (2, 3), (3, 4), (3, 5)]

instance : DecidableRel graph166.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_166 : graph166.edgeFinset =
    {s(0, 1), s(0, 3), s(0, 4), s(0, 5), s(1, 2), s(1, 5), s(2, 3), s(3, 4), s(3, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

/-- The natural-number numerator of the graph weight. -/
def F166 (z : Fin 6 → Fin 4) : ℕ :=
    twoScaleN (z 0) (z 1) *
    twoScaleN (z 0) (z 3) *
    twoScaleN (z 0) (z 4) *
    twoScaleN (z 0) (z 5) *
    twoScaleN (z 1) (z 2) *
    twoScaleN (z 1) (z 5) *
    twoScaleN (z 2) (z 3) *
    twoScaleN (z 3) (z 4) *
    twoScaleN (z 3) (z 5)

lemma graphWeight_166 (z : Fin 6 → Fin 4) :
    graphWeight graph166 twoScaleW z =
      twoScaleW (z 0) (z 1) *
      twoScaleW (z 0) (z 3) *
      twoScaleW (z 0) (z 4) *
      twoScaleW (z 0) (z 5) *
      twoScaleW (z 1) (z 2) *
      twoScaleW (z 1) (z 5) *
      twoScaleW (z 2) (z 3) *
      twoScaleW (z 3) (z 4) *
      twoScaleW (z 3) (z 5) := by
  rw [graphWeight, edgeFinset_166]
  simp
  ring

lemma graphWeight_nat_166 (z : Fin 6 → Fin 4) :
    graphWeight graph166 twoScaleW z = (F166 z : ℝ) / (4 : ℝ) ^ 9 := by
  rw [graphWeight_166]
  simp only [twoScaleW, stepGraphon_apply, F166]
  push_cast
  ring

theorem S166 : ∑ z : Fin 6 → Fin 4, F166 z = 1904640 := by decide +kernel

theorem homDensity_166 :
    homDensity graph166 twoScaleW = 1904640 / (((4 : ℝ) ^ 6) * (4 : ℝ) ^ 9) := by
  rw [homDensity_of_natWeight graph166 twoScaleW F166 ((4 : ℝ) ^ 9)
    graphWeight_nat_166, S166, Fintype.card_fin]
  norm_num

theorem s166_0 : surjCount graph166 0 = 0 := by decide +kernel
theorem s166_1 : surjCount graph166 1 = 0 := by decide +kernel
theorem s166_2 : surjCount graph166 2 = 0 := by decide +kernel
theorem s166_3 : surjCount graph166 3 = 12 := by decide +kernel
theorem s166_4 : surjCount graph166 4 = 192 := by decide +kernel
theorem s166_5 : surjCount graph166 5 = 720 := by decide +kernel
theorem s166_6 : surjCount graph166 6 = 720 := by
  rw [surjCount_card graph166]
  decide

theorem count166 (k : ℕ) :
    properAssignmentCount graph166 k = 12 * k.choose 3 + 192 * k.choose 4 + 720 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph166 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s166_0, s166_1, s166_2, s166_3, s166_4, s166_5, s166_6]
  ring

theorem num166 : IsChromaticNumber graph166 3 where
  positive := by rw [count166]; decide
  zero_below k hk := by
    rw [count166]
    interval_cases k <;> decide

theorem chrom166 : IsChromaticPolynomial graph166
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph166 j : ℝ) / (j).factorial) * ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph166

/-- **Atlas 166 refutes the catalogue proposition.** -/
theorem violatesLowerBound_166 : ViolatesLowerBound graph166 := by
  refine violatesLowerBound_of_finiteUniform graph166 chrom166 num166 twoScaleW ?_ ?_
  · rw [cliqueDensity_twoScale, admissibleDensity]; norm_num
  · rw [homDensity_166, cliqueDensity_twoScale,
      chromaticTarget_of_ne_one _ (by norm_num : ((9 / 16) : ℝ) ≠ 1)]
    simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.prod_range_succ, Finset.prod_range_zero,
      s166_0, s166_1, s166_2, s166_3, s166_4, s166_5, s166_6,
      eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
    norm_num

/-! ### Atlas 172 -/

def graph172 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 3), (0, 4), (0, 5), (1, 2), (1, 5), (2, 3), (2, 5), (3, 4)]

instance : DecidableRel graph172.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_172 : graph172.edgeFinset =
    {s(0, 1), s(0, 3), s(0, 4), s(0, 5), s(1, 2), s(1, 5), s(2, 3), s(2, 5), s(3, 4)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

/-- The natural-number numerator of the graph weight. -/
def F172 (z : Fin 6 → Fin 4) : ℕ :=
    twoScaleN (z 0) (z 1) *
    twoScaleN (z 0) (z 3) *
    twoScaleN (z 0) (z 4) *
    twoScaleN (z 0) (z 5) *
    twoScaleN (z 1) (z 2) *
    twoScaleN (z 1) (z 5) *
    twoScaleN (z 2) (z 3) *
    twoScaleN (z 2) (z 5) *
    twoScaleN (z 3) (z 4)

lemma graphWeight_172 (z : Fin 6 → Fin 4) :
    graphWeight graph172 twoScaleW z =
      twoScaleW (z 0) (z 1) *
      twoScaleW (z 0) (z 3) *
      twoScaleW (z 0) (z 4) *
      twoScaleW (z 0) (z 5) *
      twoScaleW (z 1) (z 2) *
      twoScaleW (z 1) (z 5) *
      twoScaleW (z 2) (z 3) *
      twoScaleW (z 2) (z 5) *
      twoScaleW (z 3) (z 4) := by
  rw [graphWeight, edgeFinset_172]
  simp
  ring

lemma graphWeight_nat_172 (z : Fin 6 → Fin 4) :
    graphWeight graph172 twoScaleW z = (F172 z : ℝ) / (4 : ℝ) ^ 9 := by
  rw [graphWeight_172]
  simp only [twoScaleW, stepGraphon_apply, F172]
  push_cast
  ring

theorem S172 : ∑ z : Fin 6 → Fin 4, F172 z = 1572864 := by decide +kernel

theorem homDensity_172 :
    homDensity graph172 twoScaleW = 1572864 / (((4 : ℝ) ^ 6) * (4 : ℝ) ^ 9) := by
  rw [homDensity_of_natWeight graph172 twoScaleW F172 ((4 : ℝ) ^ 9)
    graphWeight_nat_172, S172, Fintype.card_fin]
  norm_num

theorem s172_0 : surjCount graph172 0 = 0 := by decide +kernel
theorem s172_1 : surjCount graph172 1 = 0 := by decide +kernel
theorem s172_2 : surjCount graph172 2 = 0 := by decide +kernel
theorem s172_3 : surjCount graph172 3 = 12 := by decide +kernel
theorem s172_4 : surjCount graph172 4 = 192 := by decide +kernel
theorem s172_5 : surjCount graph172 5 = 720 := by decide +kernel
theorem s172_6 : surjCount graph172 6 = 720 := by
  rw [surjCount_card graph172]
  decide

theorem count172 (k : ℕ) :
    properAssignmentCount graph172 k = 12 * k.choose 3 + 192 * k.choose 4 + 720 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph172 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s172_0, s172_1, s172_2, s172_3, s172_4, s172_5, s172_6]
  ring

theorem num172 : IsChromaticNumber graph172 3 where
  positive := by rw [count172]; decide
  zero_below k hk := by
    rw [count172]
    interval_cases k <;> decide

theorem chrom172 : IsChromaticPolynomial graph172
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph172 j : ℝ) / (j).factorial) * ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph172

/-- **Atlas 172 refutes the catalogue proposition.** -/
theorem violatesLowerBound_172 : ViolatesLowerBound graph172 := by
  refine violatesLowerBound_of_finiteUniform graph172 chrom172 num172 twoScaleW ?_ ?_
  · rw [cliqueDensity_twoScale, admissibleDensity]; norm_num
  · rw [homDensity_172, cliqueDensity_twoScale,
      chromaticTarget_of_ne_one _ (by norm_num : ((9 / 16) : ℝ) ≠ 1)]
    simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.prod_range_succ, Finset.prod_range_zero,
      s172_0, s172_1, s172_2, s172_3, s172_4, s172_5, s172_6,
      eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
    norm_num

/-! ### Atlas 206 -/

def graph206 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)]

instance : DecidableRel graph206.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_206 : graph206.edgeFinset =
    {s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(0, 5), s(1, 2), s(1, 3), s(1, 5), s(2, 3), s(2, 4), s(3, 4), s(3, 5), s(4, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

/-- The natural-number numerator of the graph weight. -/
def F206 (z : Fin 6 → Fin 3) : ℕ :=
    oneDiagN (z 0) (z 1) *
    oneDiagN (z 0) (z 2) *
    oneDiagN (z 0) (z 3) *
    oneDiagN (z 0) (z 4) *
    oneDiagN (z 0) (z 5) *
    oneDiagN (z 1) (z 2) *
    oneDiagN (z 1) (z 3) *
    oneDiagN (z 1) (z 5) *
    oneDiagN (z 2) (z 3) *
    oneDiagN (z 2) (z 4) *
    oneDiagN (z 3) (z 4) *
    oneDiagN (z 3) (z 5) *
    oneDiagN (z 4) (z 5)

lemma graphWeight_206 (z : Fin 6 → Fin 3) :
    graphWeight graph206 oneDiagW z =
      oneDiagW (z 0) (z 1) *
      oneDiagW (z 0) (z 2) *
      oneDiagW (z 0) (z 3) *
      oneDiagW (z 0) (z 4) *
      oneDiagW (z 0) (z 5) *
      oneDiagW (z 1) (z 2) *
      oneDiagW (z 1) (z 3) *
      oneDiagW (z 1) (z 5) *
      oneDiagW (z 2) (z 3) *
      oneDiagW (z 2) (z 4) *
      oneDiagW (z 3) (z 4) *
      oneDiagW (z 3) (z 5) *
      oneDiagW (z 4) (z 5) := by
  rw [graphWeight, edgeFinset_206]
  simp
  ring

lemma graphWeight_nat_206 (z : Fin 6 → Fin 3) :
    graphWeight graph206 oneDiagW z = (F206 z : ℝ) / (4 : ℝ) ^ 13 := by
  rw [graphWeight_206]
  simp only [oneDiagW, stepGraphon_apply, F206]
  push_cast
  ring

theorem S206 : ∑ z : Fin 6 → Fin 3, F206 z = 77731841 := by decide +kernel

theorem homDensity_206 :
    homDensity graph206 oneDiagW = 77731841 / (((3 : ℝ) ^ 6) * (4 : ℝ) ^ 13) := by
  rw [homDensity_of_natWeight graph206 oneDiagW F206 ((4 : ℝ) ^ 13)
    graphWeight_nat_206, S206, Fintype.card_fin]
  norm_num

theorem s206_0 : surjCount graph206 0 = 0 := by decide +kernel
theorem s206_1 : surjCount graph206 1 = 0 := by decide +kernel
theorem s206_2 : surjCount graph206 2 = 0 := by decide +kernel
theorem s206_3 : surjCount graph206 3 = 0 := by decide +kernel
theorem s206_4 : surjCount graph206 4 = 24 := by decide +kernel
theorem s206_5 : surjCount graph206 5 = 240 := by decide +kernel
theorem s206_6 : surjCount graph206 6 = 720 := by
  rw [surjCount_card graph206]
  decide

theorem count206 (k : ℕ) :
    properAssignmentCount graph206 k = 24 * k.choose 4 + 240 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph206 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s206_0, s206_1, s206_2, s206_3, s206_4, s206_5, s206_6]
  ring

theorem num206 : IsChromaticNumber graph206 4 where
  positive := by rw [count206]; decide
  zero_below k hk := by
    rw [count206]
    interval_cases k <;> decide

theorem chrom206 : IsChromaticPolynomial graph206
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph206 j : ℝ) / (j).factorial) * ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph206

/-- **Atlas 206 refutes the catalogue proposition.** -/
theorem violatesLowerBound_206 : ViolatesLowerBound graph206 := by
  refine violatesLowerBound_of_finiteUniform graph206 chrom206 num206 oneDiagW ?_ ?_
  · rw [cliqueDensity_oneDiag, admissibleDensity]; norm_num
  · rw [homDensity_206, cliqueDensity_oneDiag,
      chromaticTarget_of_ne_one _ (by norm_num : ((25 / 36) : ℝ) ≠ 1)]
    simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.prod_range_succ, Finset.prod_range_zero,
      s206_0, s206_1, s206_2, s206_3, s206_4, s206_5, s206_6,
      eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
    norm_num

end Taeyoung.Methods.Negative
