import Taeyoung.Methods.OddWalk.Identity

/-!
# The three folds

`notes/blekherman_raymond.tex` folds `P₅` onto `P₃` three ways,

```
φ₁ = (0,1,0,1,2,3),   φ₂ = (0,1,2,1,2,3),   φ₃ = (0,1,2,3,2,3),
```

each traversing one edge of `P₃` three times and the other two once.  This file
sets up the vocabulary the three instantiations share.

A fold is a sequence of five steps; at step `k` the chain carries the vertex
density `u_k`, the pair density `K_k`, and the partition function
`h_k = walkIter W (5-k)`, and `chain_step` peels one edge.  Because
`walkIter W (n+1) y` is *definitionally* `∫ z, W y z * walkIter W n z ∂μ`, the
right-hand side of `chain_step` is already the next partition function and the
five steps telescope with no rewriting.

Only three step shapes occur, since every vertex of `P₃` is an end or an
interior vertex and every edge is an end edge or the middle one:

| step | `u` | `K` | `v` |
|---|---|---|---|
| away from an end | `mEnd` | `kEnd` | `mMid` |
| towards an end | `mMid` | `kEnd` swapped | `mEnd` |
| across the middle | `mMid` | `kMid` | `mMid` |

All bounds are taken at `c = ε⁵`, `C = (ε⁵)⁻¹`, which contains both the
marginals (in `[ε³, (ε³)⁻¹]`) and every `walkIter W n` for `n ≤ 4` (in
`[ε⁴, 1]`).
-/

namespace Taeyoung.Methods.OddWalk

open MeasureTheory
open Taeyoung Taeyoung.Methods.Link

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Shared functionals -/

/-- The edge term of a pair density. -/
noncomputable def Eker (W : Graphon Ω μ) (K : Ω → Ω → ℝ) : ℝ :=
  ∫ u, ∫ v, K u v * (Real.log (W u v) - Real.log (K u v)) ∂μ ∂μ

/-- The vertex term of a vertex density. -/
noncomputable def Vden (ν : Measure Ω) (u : Ω → ℝ) : ℝ :=
  ∫ x, u x * Real.log (u x) ∂ν

/-- The mixed term carried along the chain. -/
noncomputable def Spair (ν : Measure Ω) (u h : Ω → ℝ) : ℝ :=
  ∫ x, u x * Real.log (h x) ∂ν

lemma Eend_eq_Eker (W : Graphon Ω μ) : Eend W = Eker W (kEnd W) := rfl
lemma Emid_eq_Eker (W : Graphon Ω μ) : Emid W = Eker W (kMid W) := rfl
lemma Vmid_eq_Vden (W : Graphon Ω μ) : Vmid W = Vden μ (mMid W) := rfl
lemma Vend_eq_Vden (W : Graphon Ω μ) : Vend W = Vden μ (mEnd W) := rfl

section Fold

variable (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
  (hW : ∀ x y, ε ≤ W x y)

include hε hε1 hW

/-! ### The working constants -/

private lemma eps5_pos : (0:ℝ) < ε ^ 5 := by positivity

private lemma eps5_le_eps3 : ε ^ 5 ≤ ε ^ 3 :=
  pow_le_pow_of_le_one hε.le hε1 (by norm_num)

private lemma eps5_le_eps4 : ε ^ 5 ≤ ε ^ 4 :=
  pow_le_pow_of_le_one hε.le hε1 (by norm_num)

private lemma one_le_inv_eps5 : (1:ℝ) ≤ (ε ^ 5)⁻¹ := by
  rw [le_inv_comm₀ one_pos (by positivity)]
  simpa using pow_le_one₀ hε.le hε1

private lemma inv_eps3_le_inv_eps5 : (ε ^ 3)⁻¹ ≤ (ε ^ 5)⁻¹ := by
  have h5 : (0:ℝ) < ε ^ 5 := by positivity
  have h : ε ^ 5 ≤ ε ^ 3 := eps5_le_eps3 W hε hε1 hW
  gcongr

/-! ### The marginals, at the working constants -/

lemma mEnd_lo (x : Ω) : ε ^ 5 ≤ mEnd W x :=
  le_trans (eps5_le_eps3 W hε hε1 hW) (mEnd_bounds W hε hW x).1

lemma mEnd_hi (x : Ω) : mEnd W x ≤ (ε ^ 5)⁻¹ :=
  le_trans (mEnd_bounds W hε hW x).2 (inv_eps3_le_inv_eps5 W hε hε1 hW)

lemma mMid_lo (x : Ω) : ε ^ 5 ≤ mMid W x :=
  le_trans (eps5_le_eps3 W hε hε1 hW) (mMid_bounds W hε hW x).1

lemma mMid_hi (x : Ω) : mMid W x ≤ (ε ^ 5)⁻¹ :=
  le_trans (mMid_bounds W hε hW x).2 (inv_eps3_le_inv_eps5 W hε hε1 hW)

lemma kEnd_lo (u v : Ω) : ε ^ 5 ≤ kEnd W u v :=
  le_trans (eps5_le_eps3 W hε hε1 hW) (kEnd_bounds W hε hW u v).1

lemma kEnd_hi (u v : Ω) : kEnd W u v ≤ (ε ^ 5)⁻¹ :=
  le_trans (kEnd_bounds W hε hW u v).2 (inv_eps3_le_inv_eps5 W hε hε1 hW)

lemma kMid_lo (u v : Ω) : ε ^ 5 ≤ kMid W u v :=
  le_trans (eps5_le_eps3 W hε hε1 hW) (kMid_bounds W hε hW u v).1

lemma kMid_hi (u v : Ω) : kMid W u v ≤ (ε ^ 5)⁻¹ :=
  le_trans (kMid_bounds W hε hW u v).2 (inv_eps3_le_inv_eps5 W hε hε1 hW)

lemma walk_lo {n : ℕ} (hn : n ≤ 5) (x : Ω) : ε ^ 5 ≤ walkIter W n x :=
  le_trans (pow_le_pow_of_le_one hε.le hε1 hn) (pow_le_walkIter W hε.le hW n x)

lemma walk_hi {n : ℕ} (x : Ω) : walkIter W n x ≤ (ε ^ 5)⁻¹ :=
  le_trans (walkIter_le_one W n x) (one_le_inv_eps5 W hε hε1 hW)

lemma W_lo (u v : Ω) : ε ^ 5 ≤ W u v :=
  le_trans (pow_le_pow_of_le_one hε.le hε1 (by norm_num : 1 ≤ 5))
    (by simpa using hW u v)

/-! ### The kernel of a step towards an end -/

/-- Reversing the orientation of an end edge does not change its edge term. -/
theorem Eker_kEnd_swap : Eker W (fun u v ↦ kEnd W v u) = Eend W := by
  have hmeas : Measurable (Function.uncurry
      fun u v ↦ kEnd W v u * (Real.log (W u v) - Real.log (kEnd W v u))) := by
    have h1 : Measurable fun q : Ω × Ω ↦ kEnd W q.2 q.1 :=
      (measurable_kEnd W).comp measurable_swap
    exact h1.mul (W.measurable.log.sub h1.log)
  have hbdd : ∀ q : Ω × Ω, |kEnd W q.2 q.1
      * (Real.log (W q.1 q.2) - Real.log (kEnd W q.2 q.1))|
      ≤ (ε ^ 5)⁻¹ * ((|Real.log (ε ^ 5)| + |Real.log ((ε ^ 5)⁻¹)|)
        + (|Real.log (ε ^ 5)| + |Real.log ((ε ^ 5)⁻¹)|)) := by
    intro q
    rw [abs_mul]
    refine mul_le_mul ?_ ((abs_sub _ _).trans (add_le_add
      (abs_log_le_of_mem (eps5_pos W hε hε1 hW) (W_lo W hε hε1 hW q.1 q.2)
        (le_trans (W.le_one _ _) (one_le_inv_eps5 W hε hε1 hW)))
      (abs_log_le_of_mem (eps5_pos W hε hε1 hW) (kEnd_lo W hε hε1 hW q.2 q.1)
        (kEnd_hi W hε hε1 hW q.2 q.1)))) (abs_nonneg _) (by positivity)
    rw [abs_of_nonneg (le_trans (le_of_lt (eps5_pos W hε hε1 hW))
      (kEnd_lo W hε hε1 hW q.2 q.1))]
    exact kEnd_hi W hε hε1 hW q.2 q.1
  show ∫ u, ∫ v, kEnd W v u * (Real.log (W u v) - Real.log (kEnd W v u)) ∂μ ∂μ = _
  rw [integral_integral_swap (integrable_prod_of_bdd hmeas hbdd)]
  refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
  refine integral_congr_ae (ae_of_all _ fun b ↦ ?_)
  show kEnd W a b * (Real.log (W b a) - Real.log (kEnd W a b))
      = kEnd W a b * (Real.log (W a b) - Real.log (kEnd W a b))
  rw [W.symm b a]


/-! ### The three step shapes -/

/-- A step away from an end vertex. -/
lemma step_away {n : ℕ} (hn : n ≤ 5) :
    Eker W (kEnd W) + Vden μ (mEnd W) + Spair μ (mMid W) (walkIter W n)
      ≤ Spair μ (mEnd W) (walkIter W (n + 1)) :=
  chain_step W (eps5_pos W hε hε1 hW) (one_le_inv_eps5 W hε hε1 hW)
    (measurable_mEnd W) (measurable_mMid W) (measurable_kEnd W)
    (measurable_walkIter W n)
    (mEnd_lo W hε hε1 hW) (mEnd_hi W hε hε1 hW)
    (mMid_lo W hε hε1 hW) (mMid_hi W hε hε1 hW)
    (fun _ _ ↦ kEnd_lo W hε hε1 hW _ _) (fun _ _ ↦ kEnd_hi W hε hε1 hW _ _)
    (walk_lo W hε hε1 hW hn) (fun _ ↦ walk_hi W hε hε1 hW _)
    (fun _ _ ↦ W_lo W hε hε1 hW _ _)
    (integral_kEnd_right W) (integral_kEnd_left W)

/-- A step towards an end vertex: the same end edge, reversed. -/
lemma step_toward {n : ℕ} (hn : n ≤ 5) :
    Eker W (fun y z ↦ kEnd W z y) + Vden μ (mMid W) + Spair μ (mEnd W) (walkIter W n)
      ≤ Spair μ (mMid W) (walkIter W (n + 1)) :=
  chain_step W (eps5_pos W hε hε1 hW) (one_le_inv_eps5 W hε hε1 hW)
    (measurable_mMid W) (measurable_mEnd W)
    ((measurable_kEnd W).comp measurable_swap)
    (measurable_walkIter W n)
    (mMid_lo W hε hε1 hW) (mMid_hi W hε hε1 hW)
    (mEnd_lo W hε hε1 hW) (mEnd_hi W hε hε1 hW)
    (fun y z ↦ kEnd_lo W hε hε1 hW z y) (fun y z ↦ kEnd_hi W hε hε1 hW z y)
    (walk_lo W hε hε1 hW hn) (fun _ ↦ walk_hi W hε hε1 hW _)
    (fun _ _ ↦ W_lo W hε hε1 hW _ _)
    (fun y ↦ integral_kEnd_left W y) (fun z ↦ integral_kEnd_right W z)

/-- A step across the middle edge. -/
lemma step_mid {n : ℕ} (hn : n ≤ 5) :
    Eker W (kMid W) + Vden μ (mMid W) + Spair μ (mMid W) (walkIter W n)
      ≤ Spair μ (mMid W) (walkIter W (n + 1)) :=
  chain_step W (eps5_pos W hε hε1 hW) (one_le_inv_eps5 W hε hε1 hW)
    (measurable_mMid W) (measurable_mMid W) (measurable_kMid W)
    (measurable_walkIter W n)
    (mMid_lo W hε hε1 hW) (mMid_hi W hε hε1 hW)
    (mMid_lo W hε hε1 hW) (mMid_hi W hε hε1 hW)
    (fun _ _ ↦ kMid_lo W hε hε1 hW _ _) (fun _ _ ↦ kMid_hi W hε hε1 hW _ _)
    (walk_lo W hε hε1 hW hn) (fun _ ↦ walk_hi W hε hε1 hW _)
    (fun _ _ ↦ W_lo W hε hε1 hW _ _)
    (integral_kMid_right W) (integral_kMid_left W)

/-! ### The two ends of the chain -/

/-- The far end: `h₅ = 1`, so the chain starts from zero. -/
lemma Spair_walk_zero : Spair μ (mEnd W) (walkIter W 0) = 0 := by
  show ∫ x, mEnd W x * Real.log (walkIter W 0 x) ∂μ = 0
  simp

/-- The near end: one more application of Gibbs converts the surviving
`∫ mEnd · log (T_W⁵ 1)` into `log a₅`. -/
lemma Spair_walk_five_le :
    Spair μ (mEnd W) (walkIter W 5) ≤ Real.log (a5 W) + Vend W := by
  have h5 : (0:ℝ) < ε ^ 5 := eps5_pos W hε hε1 hW
  have key := integral_mul_log_div_le_log_integral (ν := μ) (measurable_mEnd W)
    (measurable_walkIter W 5) (integral_mEnd W hε hW)
    ⟨ε ^ 5, h5, mEnd_lo W hε hε1 hW⟩
    ⟨(ε ^ 5)⁻¹, by positivity, mEnd_hi W hε hε1 hW⟩
    ⟨ε ^ 5, h5, walk_lo W hε hε1 hW (le_refl 5)⟩
    ⟨(ε ^ 5)⁻¹, by positivity, fun _ ↦ walk_hi W hε hε1 hW _⟩
  -- `∫ walkIter W 5 = a₅`
  rw [← a5_eq W] at key
  -- split the logarithm
  have hpt : ∀ x : Ω, mEnd W x * Real.log (walkIter W 5 x / mEnd W x)
      = mEnd W x * Real.log (walkIter W 5 x) - mEnd W x * Real.log (mEnd W x) := by
    intro x
    have h1 : 0 < walkIter W 5 x := lt_of_lt_of_le h5 (walk_lo W hε hε1 hW (le_refl 5) x)
    have h2 : 0 < mEnd W x := lt_of_lt_of_le h5 (mEnd_lo W hε hε1 hW x)
    rw [Real.log_div (ne_of_gt h1) (ne_of_gt h2)]
    ring
  have i1 : Integrable (fun x ↦ mEnd W x * Real.log (walkIter W 5 x)) μ :=
    integrable_of_bdd ((measurable_mEnd W).mul (measurable_walkIter W 5).log)
      (C := (ε ^ 5)⁻¹ * (|Real.log (ε ^ 5)| + |Real.log ((ε ^ 5)⁻¹)|)) fun x ↦ by
        rw [abs_mul]
        refine mul_le_mul ?_ (abs_log_le_of_mem h5 (walk_lo W hε hε1 hW (le_refl 5) x)
          (walk_hi W hε hε1 hW x)) (abs_nonneg _) (by positivity)
        rw [abs_of_nonneg (le_trans h5.le (mEnd_lo W hε hε1 hW x))]
        exact mEnd_hi W hε hε1 hW x
  have i2 : Integrable (fun x ↦ mEnd W x * Real.log (mEnd W x)) μ :=
    integrable_of_bdd ((measurable_mEnd W).mul (measurable_mEnd W).log)
      (C := (ε ^ 5)⁻¹ * (|Real.log (ε ^ 5)| + |Real.log ((ε ^ 5)⁻¹)|)) fun x ↦ by
        rw [abs_mul]
        refine mul_le_mul ?_ (abs_log_le_of_mem h5 (mEnd_lo W hε hε1 hW x)
          (mEnd_hi W hε hε1 hW x)) (abs_nonneg _) (by positivity)
        rw [abs_of_nonneg (le_trans h5.le (mEnd_lo W hε hε1 hW x))]
        exact mEnd_hi W hε hε1 hW x
  rw [integral_congr_ae (ae_of_all _ hpt), integral_sub i1 i2] at key
  show (∫ x, mEnd W x * Real.log (walkIter W 5 x) ∂μ) ≤ _
  have hV : Vend W = ∫ x, mEnd W x * Real.log (mEnd W x) ∂μ := rfl
  rw [hV]
  linarith


/-! ### The three folds

Each fold is five steps.  The `Spair` terms telescope: the right-hand side of
step `k` is the third summand on the left of step `k-1`, so all of them cancel
except `Spair (mEnd W) (walkIter W 0) = 0` at the far end and
`Spair (mEnd W) (walkIter W 5)` at the near end. -/

private lemma succ_norm : (4:ℕ) + 1 = 5 ∧ (3:ℕ) + 1 = 4 ∧ (2:ℕ) + 1 = 3
    ∧ (1:ℕ) + 1 = 2 ∧ (0:ℕ) + 1 = 1 := by norm_num

/-- `φ₁ = (0,1,0,1,2,3)`: the end edge `{0,1}` traversed three times. -/
theorem fold_one : 4 * Eend W + Emid W + Vend W + 3 * Vmid W ≤ Real.log (a5 W) := by
  have s0 := step_away W hε hε1 hW (n := 4) (by norm_num)
  have s1 := step_toward W hε hε1 hW (n := 3) (by norm_num)
  have s2 := step_away W hε hε1 hW (n := 2) (by norm_num)
  have s3 := step_mid W hε hε1 hW (n := 1) (by norm_num)
  have s4 := step_toward W hε hε1 hW (n := 0) (by norm_num)
  simp only [show (4:ℕ)+1 = 5 from rfl, show (3:ℕ)+1 = 4 from rfl,
    show (2:ℕ)+1 = 3 from rfl, show (1:ℕ)+1 = 2 from rfl,
    show (0:ℕ)+1 = 1 from rfl] at s0 s1 s2 s3 s4
  rw [Eker_kEnd_swap W hε hε1 hW] at s1 s4
  rw [← Eend_eq_Eker W] at s0 s2
  rw [← Emid_eq_Eker W] at s3
  simp only [← Vend_eq_Vden W, ← Vmid_eq_Vden W] at s0 s1 s2 s3 s4
  have h0 := Spair_walk_zero W hε hε1 hW
  have h5 := Spair_walk_five_le W hε hε1 hW
  linarith

/-- `φ₂ = (0,1,2,1,2,3)`: the middle edge traversed three times. -/
theorem fold_two : 2 * Eend W + 3 * Emid W + 4 * Vmid W ≤ Real.log (a5 W) := by
  have s0 := step_away W hε hε1 hW (n := 4) (by norm_num)
  have s1 := step_mid W hε hε1 hW (n := 3) (by norm_num)
  have s2 := step_mid W hε hε1 hW (n := 2) (by norm_num)
  have s3 := step_mid W hε hε1 hW (n := 1) (by norm_num)
  have s4 := step_toward W hε hε1 hW (n := 0) (by norm_num)
  simp only [show (4:ℕ)+1 = 5 from rfl, show (3:ℕ)+1 = 4 from rfl,
    show (2:ℕ)+1 = 3 from rfl, show (1:ℕ)+1 = 2 from rfl,
    show (0:ℕ)+1 = 1 from rfl] at s0 s1 s2 s3 s4
  rw [Eker_kEnd_swap W hε hε1 hW] at s4
  rw [← Eend_eq_Eker W] at s0
  rw [← Emid_eq_Eker W] at s1 s2 s3
  simp only [← Vend_eq_Vden W, ← Vmid_eq_Vden W] at s0 s1 s2 s3 s4
  have h0 := Spair_walk_zero W hε hε1 hW
  have h5 := Spair_walk_five_le W hε hε1 hW
  linarith

/-- `φ₃ = (0,1,2,3,2,3)`: the end edge `{2,3}` traversed three times. -/
theorem fold_three : 4 * Eend W + Emid W + Vend W + 3 * Vmid W ≤ Real.log (a5 W) := by
  have s0 := step_away W hε hε1 hW (n := 4) (by norm_num)
  have s1 := step_mid W hε hε1 hW (n := 3) (by norm_num)
  have s2 := step_toward W hε hε1 hW (n := 2) (by norm_num)
  have s3 := step_away W hε hε1 hW (n := 1) (by norm_num)
  have s4 := step_toward W hε hε1 hW (n := 0) (by norm_num)
  simp only [show (4:ℕ)+1 = 5 from rfl, show (3:ℕ)+1 = 4 from rfl,
    show (2:ℕ)+1 = 3 from rfl, show (1:ℕ)+1 = 2 from rfl,
    show (0:ℕ)+1 = 1 from rfl] at s0 s1 s2 s3 s4
  rw [Eker_kEnd_swap W hε hε1 hW] at s2 s4
  rw [← Eend_eq_Eker W] at s0 s3
  rw [← Emid_eq_Eker W] at s1
  simp only [← Vend_eq_Vden W, ← Vmid_eq_Vden W] at s0 s1 s2 s3 s4
  have h0 := Spair_walk_zero W hε hε1 hW
  have h5 := Spair_walk_five_le W hε hε1 hW
  linarith

/-! ### Summation -/

/-- **The odd-walk inequality for a regularized graphon**, in logarithmic form.
The three folds contribute edge multiplicities `(10, 5)` and vertex
multiplicities `(2, 10)`; the tree-entropy identity collapses
`10·Eend + 5·Emid + 10·Vmid` to `5·log a₃`, and `Vend ≥ 0` discards the rest. -/
theorem five_log_a3_le : 5 * Real.log (a3 W) ≤ 3 * Real.log (a5 W) := by
  have f1 := fold_one W hε hε1 hW
  have f2 := fold_two W hε hε1 hW
  have f3 := fold_three W hε hε1 hW
  have hid := tree_entropy_identity W hε hε1 hW
  have hV : 0 ≤ Vend W :=
    integral_mul_log_nonneg (measurable_mEnd W) (integral_mEnd W hε hW)
      ⟨ε ^ 5, eps5_pos W hε hε1 hW, mEnd_lo W hε hε1 hW⟩
      ⟨(ε ^ 5)⁻¹, by positivity, mEnd_hi W hε hε1 hW⟩
  linarith

/-- **`a₅³ ≥ a₃⁵` for a graphon bounded away from zero.** -/
theorem pow_le_pow_of_regular : a3 W ^ 5 ≤ a5 W ^ 3 := by
  have h := five_log_a3_le W hε hε1 hW
  have h3 : 0 < a3 W := a3_pos W hε hW
  have h5 : 0 < a5 W :=
    lt_of_lt_of_le (by positivity) (pow_five_le_a5 W hε.le hW)
  have e3 : Real.log (a3 W ^ 5) = 5 * Real.log (a3 W) := by
    rw [Real.log_pow]; norm_num
  have e5 : Real.log (a5 W ^ 3) = 3 * Real.log (a5 W) := by
    rw [Real.log_pow]; norm_num
  by_contra hcon
  push_neg at hcon
  have := Real.log_lt_log (by positivity) hcon
  rw [e3, e5] at this
  linarith

end Fold

end Taeyoung.Methods.OddWalk
