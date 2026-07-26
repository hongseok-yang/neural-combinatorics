import PureChordal.HomDensity
import Mathlib.Tactic.Ring

/-!
# Elementary graphon regularization

For `0 ≤ ε ≤ 1`, set `Wε = ε + (1-ε)W`.  This file proves the explicit
Lipschitz estimate

`|t(F,Wε) - t(F,W)| ≤ |E(F)| ε`.

No cut metric, graphon approximation theorem, or dominated-convergence argument
is used.
-/

open MeasureTheory
open scoped BigOperators

namespace PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma abs_finset_prod_sub_prod_le_sum_abs
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1)
    (hb0 : ∀ i ∈ s, 0 ≤ b i) (hb1 : ∀ i ∈ s, b i ≤ 1) :
    |(∏ i ∈ s, a i) - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
      have ha0e := ha0 e (Finset.mem_insert_self e s)
      have ha1e := ha1 e (Finset.mem_insert_self e s)
      have hb0e := hb0 e (Finset.mem_insert_self e s)
      have hb1e := hb1 e (Finset.mem_insert_self e s)
      have ha0s : ∀ i ∈ s, 0 ≤ a i :=
        fun i hi ↦ ha0 i (Finset.mem_insert_of_mem hi)
      have ha1s : ∀ i ∈ s, a i ≤ 1 :=
        fun i hi ↦ ha1 i (Finset.mem_insert_of_mem hi)
      have hb0s : ∀ i ∈ s, 0 ≤ b i :=
        fun i hi ↦ hb0 i (Finset.mem_insert_of_mem hi)
      have hb1s : ∀ i ∈ s, b i ≤ 1 :=
        fun i hi ↦ hb1 i (Finset.mem_insert_of_mem hi)
      have hpa0 : 0 ≤ ∏ i ∈ s, a i := Finset.prod_nonneg ha0s
      have hpa1 : (∏ i ∈ s, a i) ≤ 1 := Finset.prod_le_one ha0s ha1s
      have hpb0 : 0 ≤ ∏ i ∈ s, b i := Finset.prod_nonneg hb0s
      have hpb1 : (∏ i ∈ s, b i) ≤ 1 := Finset.prod_le_one hb0s hb1s
      rw [Finset.prod_insert he, Finset.prod_insert he, Finset.sum_insert he]
      calc
        |a e * (∏ i ∈ s, a i) - b e * ∏ i ∈ s, b i|
            =
          |a e * ((∏ i ∈ s, a i) - ∏ i ∈ s, b i) +
            (a e - b e) * ∏ i ∈ s, b i| := by ring_nf
        _ ≤
          |a e * ((∏ i ∈ s, a i) - ∏ i ∈ s, b i)| +
            |(a e - b e) * ∏ i ∈ s, b i| := abs_add_le _ _
        _ =
          a e * |(∏ i ∈ s, a i) - ∏ i ∈ s, b i| +
            |a e - b e| * ∏ i ∈ s, b i := by
              rw [abs_mul, abs_mul, abs_of_nonneg ha0e, abs_of_nonneg hpb0]
        _ ≤
          1 * (∑ i ∈ s, |a i - b i|) + |a e - b e| * 1 := by
              exact add_le_add
                (mul_le_mul ha1e (ih ha0s ha1s hb0s hb1s)
                  (abs_nonneg _) zero_le_one)
                (mul_le_mul_of_nonneg_left hpb1 (abs_nonneg _))
        _ = |a e - b e| + ∑ i ∈ s, |a i - b i| := by ring

/-- The uniformly positive regularization `ε + (1-ε)W`. -/
def Graphon.regularize (W : Graphon Ω μ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : Graphon Ω μ where
  toFun x y := ε + (1 - ε) * W x y
  measurable := by
    exact measurable_const.add (measurable_const.mul W.measurable)
  nonneg x y := add_nonneg hε0 (mul_nonneg (sub_nonneg.mpr hε1) (W.nonneg x y))
  le_one x y := by
    calc
      ε + (1 - ε) * W x y ≤ ε + (1 - ε) * 1 := by
        simpa [add_comm] using
          add_le_add_left
            (mul_le_mul_of_nonneg_left (W.le_one x y) (sub_nonneg.mpr hε1)) ε
      _ = 1 := by ring
  symm x y := by rw [W.symm x y]

@[simp] lemma Graphon.regularize_apply (W : Graphon Ω μ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (x y : Ω) :
    W.regularize ε hε0 hε1 x y = ε + (1 - ε) * W x y := rfl

lemma Graphon.abs_regularize_sub_le (W : Graphon Ω μ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (x y : Ω) :
    |W.regularize ε hε0 hε1 x y - W x y| ≤ ε := by
  have hOne : 0 ≤ 1 - W x y := sub_nonneg.mpr (W.le_one x y)
  calc
    |W.regularize ε hε0 hε1 x y - W x y| = |ε * (1 - W x y)| := by
      congr 1
      simp only [Graphon.regularize_apply]
      ring
    _ = ε * (1 - W x y) := abs_of_nonneg (mul_nonneg hε0 hOne)
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left
      (sub_le_self 1 (W.nonneg x y)) hε0
    _ = ε := mul_one ε

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma abs_edgeValue_regularize_sub_le (W : Graphon Ω μ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (x : V → Ω) (e : Sym2 V) :
    |edgeValue (W.regularize ε hε0 hε1) x e - edgeValue W x e| ≤ ε := by
  induction e using Sym2.inductionOn with
  | _ u v => simpa using W.abs_regularize_sub_le ε hε0 hε1 (x u) (x v)

lemma abs_graphWeight_regularize_sub_le
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon Ω μ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (x : V → Ω) :
    |graphWeight H (W.regularize ε hε0 hε1) x - graphWeight H W x|
      ≤ H.edgeFinset.card * ε := by
  calc
    |graphWeight H (W.regularize ε hε0 hε1) x - graphWeight H W x|
        ≤ ∑ e ∈ H.edgeFinset,
            |edgeValue (W.regularize ε hε0 hε1) x e - edgeValue W x e| := by
          exact abs_finset_prod_sub_prod_le_sum_abs H.edgeFinset
            (fun e ↦ edgeValue (W.regularize ε hε0 hε1) x e)
            (fun e ↦ edgeValue W x e)
            (fun e _ ↦ edgeValue_nonneg _ _ e)
            (fun e _ ↦ edgeValue_le_one _ _ e)
            (fun e _ ↦ edgeValue_nonneg _ _ e)
            (fun e _ ↦ edgeValue_le_one _ _ e)
    _ ≤ ∑ _e ∈ H.edgeFinset, ε := by
          exact Finset.sum_le_sum fun e _ ↦
            abs_edgeValue_regularize_sub_le W ε hε0 hε1 x e
    _ = H.edgeFinset.card * ε := by simp

theorem abs_homDensity_regularize_sub_le
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon Ω μ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    |homDensity H (W.regularize ε hε0 hε1) - homDensity H W|
      ≤ H.edgeFinset.card * ε := by
  rw [homDensity, homDensity,
    ← integral_sub (integrable_graphWeight H (W.regularize ε hε0 hε1))
      (integrable_graphWeight H W)]
  calc
    |∫ x, graphWeight H (W.regularize ε hε0 hε1) x -
        graphWeight H W x ∂assignmentMeasure V μ|
        ≤ ∫ x, |graphWeight H (W.regularize ε hε0 hε1) x -
            graphWeight H W x| ∂assignmentMeasure V μ :=
          abs_integral_le_integral_abs
    _ ≤ ∫ _x, H.edgeFinset.card * ε ∂assignmentMeasure V μ := by
          exact integral_mono
            ((integrable_graphWeight H (W.regularize ε hε0 hε1)).sub
              (integrable_graphWeight H W)).abs
            (integrable_const _)
            (abs_graphWeight_regularize_sub_le H W ε hε0 hε1)
    _ = H.edgeFinset.card * ε := by simp

/-- The same explicit continuity estimate after taking a fixed natural power.
This is the form needed for the left side of clique-tree gluing. -/
theorem abs_homDensity_regularize_pow_sub_le
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon Ω μ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (n : ℕ) :
    |(homDensity H (W.regularize ε hε0 hε1)) ^ n -
        (homDensity H W) ^ n|
      ≤ n * (H.edgeFinset.card * ε) := by
  have h := abs_finset_prod_sub_prod_le_sum_abs
    (Finset.univ : Finset (Fin n))
    (fun _ => homDensity H (W.regularize ε hε0 hε1))
    (fun _ => homDensity H W)
    (fun _ _ => homDensity_nonneg H _)
    (fun _ _ => homDensity_le_one H _)
    (fun _ _ => homDensity_nonneg H W)
    (fun _ _ => homDensity_le_one H W)
  calc
    |(homDensity H (W.regularize ε hε0 hε1)) ^ n -
        (homDensity H W) ^ n|
        ≤ ∑ _i : Fin n,
          |homDensity H (W.regularize ε hε0 hε1) -
            homDensity H W| := by
              simpa using h
    _ ≤ ∑ _i : Fin n, H.edgeFinset.card * ε := by
      exact Finset.sum_le_sum fun _ _ =>
        abs_homDensity_regularize_sub_le H W ε hε0 hε1
    _ = n * (H.edgeFinset.card * ε) := by simp

end PureChordal
