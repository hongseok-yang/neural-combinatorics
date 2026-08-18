import Taeyoung.Methods.OddWalk.GibbsLog

/-!
# The marginals of the `P₃` measure

`notes/blekherman_raymond.tex` §2 runs the entropy argument against the
probability density

```
f(x₀,x₁,x₂,x₃) = W(x₀,x₁) W(x₁,x₂) W(x₂,x₃) / a₃
```

on `Ω⁴`, and everything it needs from `f` is its one- and two-dimensional
marginals.  Those are closed-form, and — this is what keeps the development
small — there are only **four** of them up to symmetry.

`P₃` has two kinds of vertex, an end (`0`, `3`) and an interior one (`1`, `2`),
and two kinds of edge, an end edge (`{0,1}`, `{2,3}`) and the middle one
(`{1,2}`).  So the marginals are

```
mEnd = B/a₃,                 mMid = d·A/a₃,
kEnd(u,v) = W(u,v)·A(v)/a₃,  kMid(u,v) = W(u,v)·d(u)·d(v)/a₃,
```

with `d = T1`, `A = T²1`, `B = T³1`.  The marginal on `{2,3}` is
`kEnd` with its arguments swapped, and `kMid` is already symmetric, so no
further definitions are needed: a walk step traversing an end edge *towards*
the end uses `fun u v ↦ kEnd W v u`.

Three identities carry all the consistency the chain induction needs, and each
is one unfolding of `walkIter` plus, in one case, the symmetry of `W`.
-/

namespace Taeyoung.Methods.OddWalk

open MeasureTheory
open Taeyoung Taeyoung.Methods.Link

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Elementary bounds on `a₃` -/

lemma a3_le_one (W : Graphon Ω μ) : a3 W ≤ 1 := by
  calc a3 W ≤ ∫ _x : Ω, (1 : ℝ) ∂μ :=
        integral_mono (integrable_walkIter W 3) (integrable_const _)
          fun x ↦ walkIter_le_one W 3 x
    _ = 1 := by simp

lemma a3_pos (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) (hW : ∀ x y, ε ≤ W x y) :
    0 < a3 W :=
  lt_of_lt_of_le (by positivity) (pow_three_le_a3 W hε.le hW)

/-- Integrating the *first* argument of `W` is the same as integrating the
second: this is the only place the symmetry of `W` enters the marginals. -/
lemma integral_edge_left (W : Graphon Ω μ) (v : Ω) :
    ∫ u, W u v ∂μ = walkIter W 1 v := by
  rw [walkIter_one]
  show ∫ u, W u v ∂μ = ∫ y, W v y ∂μ
  exact integral_congr_ae (ae_of_all _ fun u ↦ W.symm u v)

/-! ### The four marginals -/

/-- Vertex marginal at an end of `P₃`. -/
noncomputable def mEnd (W : Graphon Ω μ) (x : Ω) : ℝ := walkIter W 3 x / a3 W

/-- Vertex marginal at an interior vertex of `P₃`. -/
noncomputable def mMid (W : Graphon Ω μ) (x : Ω) : ℝ :=
  walkIter W 1 x * walkIter W 2 x / a3 W

/-- Pair marginal on an end edge, oriented away from the end. -/
noncomputable def kEnd (W : Graphon Ω μ) (u v : Ω) : ℝ :=
  W u v * walkIter W 2 v / a3 W

/-- Pair marginal on the middle edge.  Symmetric in its two arguments. -/
noncomputable def kMid (W : Graphon Ω μ) (u v : Ω) : ℝ :=
  W u v * walkIter W 1 u * walkIter W 1 v / a3 W

lemma kMid_symm (W : Graphon Ω μ) (u v : Ω) : kMid W u v = kMid W v u := by
  simp only [kMid, W.symm u v]
  ring

/-! ### Measurability -/

lemma measurable_mEnd (W : Graphon Ω μ) : Measurable (mEnd W) :=
  (measurable_walkIter W 3).div_const _

lemma measurable_mMid (W : Graphon Ω μ) : Measurable (mMid W) :=
  (((measurable_walkIter W 1).mul (measurable_walkIter W 2))).div_const _

lemma measurable_kEnd (W : Graphon Ω μ) :
    Measurable (Function.uncurry (kEnd W)) :=
  ((W.measurable.mul ((measurable_walkIter W 2).comp measurable_snd))).div_const _

lemma measurable_kMid (W : Graphon Ω μ) :
    Measurable (Function.uncurry (kMid W)) :=
  (((W.measurable.mul ((measurable_walkIter W 1).comp measurable_fst))).mul
    ((measurable_walkIter W 1).comp measurable_snd)).div_const _

/-! ### The three marginal identities -/

/-- Integrating an end edge away from its end vertex returns the end marginal. -/
theorem integral_kEnd_right (W : Graphon Ω μ) (u : Ω) :
    ∫ v, kEnd W u v ∂μ = mEnd W u := by
  show ∫ v, W u v * walkIter W 2 v / a3 W ∂μ = walkIter W 3 u / a3 W
  rw [integral_div]
  rfl

/-- Integrating an end edge *at* its end vertex returns the interior marginal. -/
theorem integral_kEnd_left (W : Graphon Ω μ) (v : Ω) :
    ∫ u, kEnd W u v ∂μ = mMid W v := by
  show ∫ u, W u v * walkIter W 2 v / a3 W ∂μ
      = walkIter W 1 v * walkIter W 2 v / a3 W
  rw [integral_div]
  congr 1
  rw [integral_mul_const, integral_edge_left]

/-- Both marginals of the middle edge are the interior marginal. -/
theorem integral_kMid_right (W : Graphon Ω μ) (u : Ω) :
    ∫ v, kMid W u v ∂μ = mMid W u := by
  show ∫ v, W u v * walkIter W 1 u * walkIter W 1 v / a3 W ∂μ
      = walkIter W 1 u * walkIter W 2 u / a3 W
  rw [integral_div]
  congr 1
  calc ∫ v, W u v * walkIter W 1 u * walkIter W 1 v ∂μ
      = ∫ v, walkIter W 1 u * (W u v * walkIter W 1 v) ∂μ :=
        integral_congr_ae (ae_of_all _ fun v ↦ by ring)
    _ = walkIter W 1 u * ∫ v, W u v * walkIter W 1 v ∂μ := integral_const_mul _ _
    _ = walkIter W 1 u * walkIter W 2 u := rfl

lemma integral_kMid_left (W : Graphon Ω μ) (v : Ω) :
    ∫ u, kMid W u v ∂μ = mMid W v := by
  calc ∫ u, kMid W u v ∂μ = ∫ u, kMid W v u ∂μ :=
        integral_congr_ae (ae_of_all _ fun u ↦ kMid_symm W u v)
    _ = mMid W v := integral_kMid_right W v

/-! ### Normalizations -/

theorem integral_mEnd (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε)
    (hW : ∀ x y, ε ≤ W x y) : ∫ x, mEnd W x ∂μ = 1 := by
  show ∫ x, walkIter W 3 x / a3 W ∂μ = 1
  rw [integral_div]
  exact div_self (ne_of_gt (a3_pos W hε hW))

theorem integral_mMid (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε)
    (hW : ∀ x y, ε ≤ W x y) : ∫ x, mMid W x ∂μ = 1 := by
  show ∫ x, walkIter W 1 x * walkIter W 2 x / a3 W ∂μ = 1
  rw [integral_div, integral_degree_mul_pathOp]
  exact div_self (ne_of_gt (a3_pos W hε hW))

/-! ### Two-sided bounds

Under a pointwise floor `ε ≤ W` every one of the four marginals lies in
`[ε³, ε⁻³]`, which is exactly the hypothesis shape
`integral_mul_log_div_le_log_integral` asks for. -/

section Bounds

variable (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) (hW : ∀ x y, ε ≤ W x y)

include hε hW

/-- The shape every marginal has: a numerator and a denominator both in
`[ε³, 1]`, hence a quotient in `[ε³, (ε³)⁻¹]`. -/
private lemma div_mem_bounds {p q : ℝ} (hp : ε ^ 3 ≤ p) (hp1 : p ≤ 1)
    (hq : ε ^ 3 ≤ q) (hq1 : q ≤ 1) :
    ε ^ 3 ≤ p / q ∧ p / q ≤ (ε ^ 3)⁻¹ := by
  have hε3 : (0 : ℝ) < ε ^ 3 := by positivity
  have hq0 : 0 < q := lt_of_lt_of_le hε3 hq
  have hp0 : 0 < p := lt_of_lt_of_le hε3 hp
  constructor
  · rw [le_div_iff₀ hq0]; nlinarith
  · rw [div_le_iff₀ hq0]
    rw [inv_mul_eq_div, le_div_iff₀ hε3]
    nlinarith

private lemma walk3_bounds (x : Ω) : ε ^ 3 ≤ walkIter W 3 x ∧ walkIter W 3 x ≤ 1 :=
  ⟨pow_le_walkIter W hε.le hW 3 x, walkIter_le_one W 3 x⟩

private lemma a3_in_bounds : ε ^ 3 ≤ a3 W ∧ a3 W ≤ 1 :=
  ⟨pow_three_le_a3 W hε.le hW, a3_le_one W⟩

lemma mEnd_bounds (x : Ω) : ε ^ 3 ≤ mEnd W x ∧ mEnd W x ≤ (ε ^ 3)⁻¹ :=
  div_mem_bounds W hε hW (walk3_bounds W hε hW x).1 (walk3_bounds W hε hW x).2
    (a3_in_bounds W hε hW).1 (a3_in_bounds W hε hW).2

lemma mMid_bounds (x : Ω) : ε ^ 3 ≤ mMid W x ∧ mMid W x ≤ (ε ^ 3)⁻¹ := by
  refine div_mem_bounds W hε hW ?_ ?_ (a3_in_bounds W hε hW).1 (a3_in_bounds W hε hW).2
  · calc ε ^ 3 = ε ^ 1 * ε ^ 2 := by ring
      _ ≤ walkIter W 1 x * walkIter W 2 x :=
          mul_le_mul (pow_le_walkIter W hε.le hW 1 x) (pow_le_walkIter W hε.le hW 2 x)
            (by positivity) (walkIter_nonneg W 1 x)
  · exact mul_le_one₀ (walkIter_le_one W 1 x) (walkIter_nonneg W 2 x)
      (walkIter_le_one W 2 x)

lemma kEnd_bounds (u v : Ω) : ε ^ 3 ≤ kEnd W u v ∧ kEnd W u v ≤ (ε ^ 3)⁻¹ := by
  refine div_mem_bounds W hε hW ?_ ?_ (a3_in_bounds W hε hW).1 (a3_in_bounds W hε hW).2
  · calc ε ^ 3 = ε ^ 1 * ε ^ 2 := by ring
      _ ≤ W u v * walkIter W 2 v :=
          mul_le_mul (by simpa using hW u v) (pow_le_walkIter W hε.le hW 2 v)
            (by positivity) (W.nonneg u v)
  · exact mul_le_one₀ (W.le_one u v) (walkIter_nonneg W 2 v) (walkIter_le_one W 2 v)

lemma kMid_bounds (u v : Ω) : ε ^ 3 ≤ kMid W u v ∧ kMid W u v ≤ (ε ^ 3)⁻¹ := by
  refine div_mem_bounds W hε hW ?_ ?_ (a3_in_bounds W hε hW).1 (a3_in_bounds W hε hW).2
  · have h1 : ε * ε ≤ W u v * walkIter W 1 u :=
      mul_le_mul (hW u v) (by simpa using pow_le_walkIter W hε.le hW 1 u)
        hε.le (W.nonneg u v)
    calc ε ^ 3 = ε * ε * ε := by ring
      _ ≤ W u v * walkIter W 1 u * walkIter W 1 v :=
          mul_le_mul h1 (by simpa using pow_le_walkIter W hε.le hW 1 v) hε.le
            (mul_nonneg (W.nonneg u v) (walkIter_nonneg W 1 u))
  · exact mul_le_one₀
      (mul_le_one₀ (W.le_one u v) (walkIter_nonneg W 1 u) (walkIter_le_one W 1 u))
      (walkIter_nonneg W 1 v) (walkIter_le_one W 1 v)

end Bounds

end Taeyoung.Methods.OddWalk
