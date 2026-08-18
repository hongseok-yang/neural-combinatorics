import Taeyoung.Methods.Negative.WeightedStep
import Taeyoung.Methods.Negative.Chromatic

open Finset Polynomial MeasureTheory

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Taeyoung.Methods.Negative

open Taeyoung Taeyoung.Methods.PureChordal

/-! ### Atlas 152: the fractional-fibre witness

Five parts of unequal mass.  Writing the masses over the common denominator
`D = 3750000` gives `w = (1870752, 2998, 1875000, 125, 1125)`, and the cell
values over `s = 16` give the matrix `N152`; the fractional fibre is the entry
`N152 2 3 = 1`, i.e. `W = 1/16` between the bulk class `B` and the small
exceptional class `S₁`.  See
`notes/atlas_152_fractional_fibre_local_counterexample.tex`. -/

def w152 : Fin 5 → ℕ := ![1870752, 2998, 1875000, 125, 1125]

theorem w152_sum : ∑ i, w152 i = 3750000 := by decide

noncomputable instance : IsProbabilityMeasure (weightedMeasure 5 w152 3750000) :=
  isProbabilityMeasure_weightedMeasure 5 w152 3750000 w152_sum (by norm_num)

def N152 : Fin 5 → Fin 5 → ℕ :=
  ![![0, 0, 16, 16, 0], ![0, 0, 16, 0, 16], ![16, 16, 0, 1, 16],
    ![16, 0, 1, 0, 0], ![0, 16, 16, 0, 0]]

theorem N152_symm : ∀ i j, N152 i j = N152 j i := by decide
theorem N152_le : ∀ i j, N152 i j ≤ 16 := by decide

/-- The five-step fractional-fibre graphon of the note. -/
noncomputable def W152 : Graphon (Fin 5) (weightedMeasure 5 w152 3750000) where
  toFun i j := (N152 i j : ℝ) / (16 : ℝ)
  measurable := measurable_of_finite _
  nonneg i j := by positivity
  le_one i j := by
    rw [div_le_one (by norm_num : (0:ℝ) < 16)]
    exact_mod_cast N152_le i j
  symm i j := by rw [N152_symm i j]

@[simp] lemma W152_apply (i j : Fin 5) : W152 i j = (N152 i j : ℝ) / (16 : ℝ) := rfl

def graph152 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 5), (1, 2), (1, 5), (2, 3), (2, 4), (3, 4), (4, 5)]

instance : DecidableRel graph152.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_152 : graph152.edgeFinset =
    {s(0, 1), s(0, 5), s(1, 2), s(1, 5), s(2, 3), s(2, 4), s(3, 4), s(4, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

/-- The natural-number numerator of the graph weight. -/
def F152 (z : Fin 6 → Fin 5) : ℕ :=
    N152 (z 0) (z 1) * N152 (z 0) (z 5) * N152 (z 1) (z 2) * N152 (z 1) (z 5) *
    N152 (z 2) (z 3) * N152 (z 2) (z 4) * N152 (z 3) (z 4) * N152 (z 4) (z 5)

lemma graphWeight_152 (z : Fin 6 → Fin 5) :
    graphWeight graph152 W152 z =
      W152 (z 0) (z 1) * W152 (z 0) (z 5) * W152 (z 1) (z 2) * W152 (z 1) (z 5) *
      W152 (z 2) (z 3) * W152 (z 2) (z 4) * W152 (z 3) (z 4) *
      W152 (z 4) (z 5) := by
  rw [graphWeight, edgeFinset_152]
  simp
  ring

lemma graphWeight_nat_152 (z : Fin 6 → Fin 5) :
    graphWeight graph152 W152 z = (F152 z : ℝ) / (16 : ℝ) ^ 8 := by
  rw [graphWeight_152]
  simp only [W152_apply, F152]
  push_cast
  ring

theorem S152 :
    ∑ z : Fin 6 → Fin 5, (∏ v, w152 (z v)) * F152 z
      = 36858911528492236800000000000000000000 := by
  decide +kernel

theorem Sp152 :
    ∑ z : Fin 2 → Fin 5, (∏ v, w152 (z v)) * N152 (z 0) (z 1)
      = 112500559686000 := by
  decide +kernel

theorem homDensity_152 :
    homDensity graph152 W152
      = 36858911528492236800000000000000000000
          / (((3750000 : ℝ) ^ 6) * (16 : ℝ) ^ 8) := by
  rw [homDensity_weighted 5 w152 3750000 graph152 w152_sum (by norm_num) W152
    F152 ((16 : ℝ) ^ 8) graphWeight_nat_152, S152]
  norm_num

theorem cliqueDensity_152 :
    cliqueDensity 2 W152 = 18750093281 / 37500000000 := by
  rw [cliqueDensity, homDensity_weighted 5 w152 3750000 (⊤ : SimpleGraph (Fin 2))
    w152_sum (by norm_num) W152 (fun z ↦ N152 (z 0) (z 1)) ((16 : ℝ))
    (fun z ↦ by rw [graphWeight_top_fin_two]; exact W152_apply _ _), Sp152]
  norm_num

theorem s152_0 : surjCount graph152 0 = 0 := by decide +kernel
theorem s152_1 : surjCount graph152 1 = 0 := by decide +kernel
theorem s152_2 : surjCount graph152 2 = 0 := by decide +kernel
theorem s152_3 : surjCount graph152 3 = 18 := by decide +kernel
theorem s152_4 : surjCount graph152 4 = 264 := by decide +kernel
theorem s152_5 : surjCount graph152 5 = 840 := by decide +kernel

theorem s152_6 : surjCount graph152 6 = 720 := by
  rw [surjCount_card graph152]
  decide

theorem count152 (k : ℕ) :
    properAssignmentCount graph152 k
      = 18 * k.choose 3 + 264 * k.choose 4 + 840 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph152 k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    s152_0, s152_1, s152_2, s152_3, s152_4, s152_5, s152_6]
  ring

theorem num152 : IsChromaticNumber graph152 3 where
  positive := by rw [count152]; decide
  zero_below k hk := by
    rw [count152]
    interval_cases k <;> decide

theorem chrom152 : IsChromaticPolynomial graph152
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph152 j : ℝ) / (j).factorial) * ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph152

/-- **Atlas 152 refutes the catalogue proposition.** -/
theorem violatesLowerBound_152 : ViolatesLowerBound graph152 := by
  intro hsat
  have hadm : admissibleDensity 3 (cliqueDensity 2 W152) := by
    rw [cliqueDensity_152, admissibleDensity]; norm_num
  have hkey := hsat _ 3 chrom152 num152 (Ω := Fin 5) W152 hadm
  have hp : edgeDensity W152 = 18750093281 / 37500000000 := cliqueDensity_152
  rw [homDensity_152, hp,
    chromaticTarget_of_ne_one _
      (by norm_num : ((18750093281 : ℝ) / 37500000000) ≠ 1)] at hkey
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    Finset.prod_range_succ, Finset.prod_range_zero,
    s152_0, s152_1, s152_2, s152_3, s152_4, s152_5, s152_6,
    eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero] at hkey
  norm_num at hkey

end Taeyoung.Methods.Negative
