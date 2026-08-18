import Taeyoung.Methods.Link.WeightedGoodman

/-!
# Walk operators, and the two densities of the odd-walk inequality

`notes/blekherman_raymond.tex` proves `t(P₅,W)³ ≥ t(P₃,W)⁵` twice: once by
Shannon entropy on a finite host graph, and once — §2 of that note — directly on
graphons, with relative entropy against `μ` in place of entropy against counting
measure.  The graphon-native proof is the one formalized here, because it needs
no finite host, no `W`-random sampling and no approximation step, and so it is
valid on the arbitrary probability spaces `SatisfiesLowerBound` quantifies over.

This file sets up the vocabulary.  Everything is phrased through the iterate

```
walkIter W n = T_W^n 1,   (T_W h)(x) = ∫ W(x,y) h(y) dμ(y),
```

so that the elementary bounds are one induction each rather than one proof per
level.  The two densities the inequality compares are

```
a₃ = t(P₃,W) = ∫ B,        a₅ = t(P₅,W) = ∫ A·B,
```

with `A = walkIter W 2` and `B = walkIter W 3`; both identities are the
self-adjointness of `T_W`, and they are what let the whole argument stay inside
`Ω` rather than moving to `Ω⁴` and `Ω⁶`.
-/

namespace Taeyoung.Methods.OddWalk

open MeasureTheory
open Taeyoung Taeyoung.Methods.Link

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The iterated walk operator -/

/-- `walkIter W n = T_W^n 1`, the rooted `n`-edge walk density. -/
noncomputable def walkIter (W : Graphon Ω μ) : ℕ → Ω → ℝ
  | 0 => fun _ ↦ 1
  | (n + 1) => fun x ↦ ∫ y, W x y * walkIter W n y ∂μ

@[simp] lemma walkIter_zero (W : Graphon Ω μ) (x : Ω) : walkIter W 0 x = 1 := rfl

lemma walkIter_succ (W : Graphon Ω μ) (n : ℕ) (x : Ω) :
    walkIter W (n + 1) x = ∫ y, W x y * walkIter W n y ∂μ := rfl

lemma measurable_walkIter (W : Graphon Ω μ) : ∀ n, Measurable (walkIter W n)
  | 0 => measurable_const
  | (n + 1) => by
      have h : StronglyMeasurable
          (Function.uncurry fun x y ↦ W x y * walkIter W n y) :=
        (W.measurable.mul
          ((measurable_walkIter W n).comp measurable_snd)).stronglyMeasurable
      exact (h.integral_prod_right' (ν := μ)).measurable

lemma walkIter_nonneg (W : Graphon Ω μ) : ∀ (n : ℕ) (x : Ω), 0 ≤ walkIter W n x
  | 0, _ => zero_le_one
  | (n + 1), x =>
      integral_nonneg fun y ↦ mul_nonneg (W.nonneg x y) (walkIter_nonneg W n y)

lemma walkIter_le_one (W : Graphon Ω μ) (n : ℕ) (x : Ω) : walkIter W n x ≤ 1 := by
  induction n generalizing x with
  | zero => exact le_rfl
  | succ n ih =>
      have hle : ∀ y, W x y * walkIter W n y ≤ 1 := fun y ↦
        mul_le_one₀ (W.le_one x y) (walkIter_nonneg W n y) (ih y)
      have hint : Integrable (fun y ↦ W x y * walkIter W n y) μ :=
        integrable_of_bdd
          ((measurable_row W.measurable x).mul (measurable_walkIter W n))
          fun y ↦ by
            rw [abs_of_nonneg (mul_nonneg (W.nonneg x y) (walkIter_nonneg W n y))]
            exact hle y
      calc walkIter W (n + 1) x = ∫ y, W x y * walkIter W n y ∂μ := rfl
        _ ≤ ∫ _y : Ω, (1 : ℝ) ∂μ := integral_mono hint (integrable_const _) hle
        _ = 1 := by simp

/-- Every row of the operator is integrable: it is measurable and bounded by 1. -/
lemma integrable_walkRow (W : Graphon Ω μ) (n : ℕ) (x : Ω) :
    Integrable (fun y ↦ W x y * walkIter W n y) μ :=
  integrable_of_bdd ((measurable_row W.measurable x).mul (measurable_walkIter W n))
    fun y ↦ by
      rw [abs_of_nonneg (mul_nonneg (W.nonneg x y) (walkIter_nonneg W n y))]
      exact mul_le_one₀ (W.le_one x y) (walkIter_nonneg W n y) (walkIter_le_one W n y)

lemma integrable_walkIter (W : Graphon Ω μ) (n : ℕ) : Integrable (walkIter W n) μ :=
  integrable_of_bdd (measurable_walkIter W n) fun x ↦ by
    rw [abs_of_nonneg (walkIter_nonneg W n x)]
    exact walkIter_le_one W n x

/-- A pointwise lower bound on `W` propagates through the iterate.  This is what
makes every density in the entropy argument strictly positive after
regularization. -/
lemma pow_le_walkIter (W : Graphon Ω μ) {ε : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ x y, ε ≤ W x y) : ∀ (n : ℕ) (x : Ω), ε ^ n ≤ walkIter W n x := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
      intro x
      have hle : ∀ y, ε ^ (n + 1) ≤ W x y * walkIter W n y := fun y ↦ by
        have := mul_le_mul (hW x y) (ih y) (pow_nonneg hε n) (W.nonneg x y)
        simpa [pow_succ, mul_comm] using this
      calc ε ^ (n + 1) = ∫ _y : Ω, ε ^ (n + 1) ∂μ := by simp
        _ ≤ ∫ y, W x y * walkIter W n y ∂μ :=
            integral_mono (integrable_const _) (integrable_walkRow W n x) hle
        _ = walkIter W (n + 1) x := rfl

/-! ### Identification with the existing operators -/

lemma walkIter_one (W : Graphon Ω μ) (x : Ω) : walkIter W 1 x = degree W x := by
  simp [walkIter_succ, degree]

lemma walkIter_two (W : Graphon Ω μ) (x : Ω) : walkIter W 2 x = pathOp W x := by
  rw [walkIter_succ]
  simp only [pathOp, walkIter_one]

/-! ### The two densities -/

/-- `a₃ = t(P₃,W)`, the three-edge walk density. -/
noncomputable def a3 (W : Graphon Ω μ) : ℝ := ∫ x, walkIter W 3 x ∂μ

/-- `a₅ = t(P₅,W)`, the five-edge walk density.  Written as `∫ A·B` rather than
as a six-fold integral: `⟨1,T⁵1⟩ = ⟨T²1,T³1⟩` by self-adjointness. -/
noncomputable def a5 (W : Graphon Ω μ) : ℝ := ∫ x, walkIter W 2 x * walkIter W 3 x ∂μ

lemma a3_nonneg (W : Graphon Ω μ) : 0 ≤ a3 W :=
  integral_nonneg fun x ↦ walkIter_nonneg W 3 x

lemma a5_nonneg (W : Graphon Ω μ) : 0 ≤ a5 W :=
  integral_nonneg fun x ↦ mul_nonneg (walkIter_nonneg W 2 x) (walkIter_nonneg W 3 x)

lemma pow_three_le_a3 (W : Graphon Ω μ) {ε : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ x y, ε ≤ W x y) : ε ^ 3 ≤ a3 W := by
  calc ε ^ 3 = ∫ _x : Ω, ε ^ 3 ∂μ := by simp
    _ ≤ a3 W := integral_mono (integrable_const _) (integrable_walkIter W 3)
        fun x ↦ pow_le_walkIter W hε hW 3 x

lemma pow_five_le_a5 (W : Graphon Ω μ) {ε : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ x y, ε ≤ W x y) : ε ^ 5 ≤ a5 W := by
  have hint : Integrable (fun x ↦ walkIter W 2 x * walkIter W 3 x) μ :=
    integrable_of_bdd ((measurable_walkIter W 2).mul (measurable_walkIter W 3))
      fun x ↦ by
        rw [abs_of_nonneg (mul_nonneg (walkIter_nonneg W 2 x) (walkIter_nonneg W 3 x))]
        exact mul_le_one₀ (walkIter_le_one W 2 x) (walkIter_nonneg W 3 x)
          (walkIter_le_one W 3 x)
  have hle : ∀ x : Ω, ε ^ 5 ≤ walkIter W 2 x * walkIter W 3 x := fun x ↦ by
    have := mul_le_mul (pow_le_walkIter W hε hW 2 x) (pow_le_walkIter W hε hW 3 x)
      (pow_nonneg hε 3) (walkIter_nonneg W 2 x)
    calc ε ^ 5 = ε ^ 2 * ε ^ 3 := by ring
      _ ≤ walkIter W 2 x * walkIter W 3 x := this
  calc ε ^ 5 = ∫ _x : Ω, ε ^ 5 ∂μ := by simp
    _ ≤ a5 W := integral_mono (integrable_const _) hint hle


/-! ### Self-adjointness of `T_W`

Every normalization in the entropy argument — that each marginal of the `P₃`
measure really is a probability density — is an instance of
`integral_walkIter_mul`, which is `⟨T^m 1, T^n 1⟩ = ⟨1, T^{m+n} 1⟩`. -/

lemma integrable_prod_walk (W : Graphon Ω μ) {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ x, |f x| ≤ 1) (hgb : ∀ x, |g x| ≤ 1) :
    Integrable (fun q : Ω × Ω ↦ f q.1 * (W q.1 q.2 * g q.2)) (μ.prod μ) :=
  integrable_prod_of_bdd
    ((hf.comp measurable_fst).mul (W.measurable.mul (hg.comp measurable_snd)))
    (C := 1) fun q ↦ by
      rw [abs_mul, abs_mul]
      have h1 : |W q.1 q.2| ≤ 1 := by
        rw [abs_of_nonneg (W.nonneg _ _)]; exact W.le_one _ _
      calc |f q.1| * (|W q.1 q.2| * |g q.2|)
          ≤ 1 * (1 * 1) :=
            mul_le_mul (hfb _)
              (mul_le_mul h1 (hgb _) (abs_nonneg _) zero_le_one)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_one
        _ = 1 := by norm_num

/-- **`T_W` is self-adjoint.**  `∫ f · T_W g = ∫ g · T_W f`, from Fubini and the
symmetry of `W`. -/
lemma integral_mul_op_comm (W : Graphon Ω μ) {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ x, |f x| ≤ 1) (hgb : ∀ x, |g x| ≤ 1) :
    ∫ x, f x * (∫ y, W x y * g y ∂μ) ∂μ
      = ∫ y, g y * (∫ x, W y x * f x ∂μ) ∂μ := by
  have hint := integrable_prod_walk W hf hg hfb hgb
  calc ∫ x, f x * (∫ y, W x y * g y ∂μ) ∂μ
      = ∫ x, ∫ y, f x * (W x y * g y) ∂μ ∂μ := by
        simp_rw [integral_const_mul]
    _ = ∫ y, ∫ x, f x * (W x y * g y) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ y, g y * (∫ x, W y x * f x ∂μ) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
        show ∫ x, f x * (W x y * g y) ∂μ = g y * ∫ x, W y x * f x ∂μ
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        simp only [W.symm y x]
        ring

private lemma abs_walkIter_le_one (W : Graphon Ω μ) (n : ℕ) (x : Ω) :
    |walkIter W n x| ≤ 1 := by
  rw [abs_of_nonneg (walkIter_nonneg W n x)]
  exact walkIter_le_one W n x

/-- **The walk pairing only sees the total length.**  `⟨T^m 1, T^n 1⟩ =
⟨1, T^{m+n} 1⟩`. -/
lemma integral_walkIter_mul (W : Graphon Ω μ) :
    ∀ (n m : ℕ), ∫ x, walkIter W m x * walkIter W n x ∂μ
      = ∫ x, walkIter W (m + n) x ∂μ := by
  intro n
  induction n with
  | zero => intro m; simp
  | succ n ih =>
      intro m
      calc ∫ x, walkIter W m x * walkIter W (n + 1) x ∂μ
          = ∫ x, walkIter W m x * (∫ y, W x y * walkIter W n y ∂μ) ∂μ := rfl
        _ = ∫ y, walkIter W n y * (∫ x, W y x * walkIter W m x ∂μ) ∂μ :=
            integral_mul_op_comm W (measurable_walkIter W m) (measurable_walkIter W n)
              (abs_walkIter_le_one W m) (abs_walkIter_le_one W n)
        _ = ∫ y, walkIter W (m + 1) y * walkIter W n y ∂μ := by
            refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
            simp only [walkIter_succ]
            ring
        _ = ∫ x, walkIter W (m + 1 + n) x ∂μ := ih (m + 1)
        _ = ∫ x, walkIter W (m + (n + 1)) x ∂μ := by
            rw [show m + 1 + n = m + (n + 1) from by omega]

/-- `a₅` really is the five-edge walk density. -/
lemma a5_eq (W : Graphon Ω μ) : a5 W = ∫ x, walkIter W 5 x ∂μ :=
  integral_walkIter_mul W 3 2

/-- `∫ d·A = a₃`: the normalization behind `m₁` and `m₂`. -/
lemma integral_degree_mul_pathOp (W : Graphon Ω μ) :
    ∫ x, walkIter W 1 x * walkIter W 2 x ∂μ = a3 W :=
  integral_walkIter_mul W 2 1

end Taeyoung.Methods.OddWalk
