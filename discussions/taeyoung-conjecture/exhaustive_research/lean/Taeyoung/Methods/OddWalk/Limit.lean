import Taeyoung.Methods.OddWalk.Fold
import Taeyoung.Methods.PureChordal.Regularization

/-!
# Removing the regularization

`OddWalk/Fold.lean` proves `a₃⁵ ≤ a₅³` for graphons bounded away from zero,
which is where the entropy argument needs every density to be positive.  This
file removes that hypothesis.

The route is the one named in `notes/blekherman_raymond.tex` §2.6: apply the
regularized statement to `W_ε = ε + (1-ε)W` and let `ε ↓ 0`.  Both walk
densities are Lipschitz in the kernel — `|walkIter W_ε n - walkIter W n| ≤ n·ε`
by induction on `n` — and `t ↦ t^k` is `k`-Lipschitz on `[0,1]`, so the two
sides move by at most `15ε` each.  No compactness or convergence machinery is
needed: the conclusion follows from `a₃⁵ ≤ a₅³ + 30ε` for every `ε ∈ (0,1]`.
-/

namespace Taeyoung.Methods.OddWalk

open MeasureTheory
open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### `t ↦ tᵏ` is `k`-Lipschitz on `[0,1]` -/

lemma abs_pow_sub_pow_le {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    ∀ k : ℕ, |u ^ k - v ^ k| ≤ k * |u - v| := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : u ^ (k + 1) - v ^ (k + 1)
          = u * (u ^ k - v ^ k) + (u - v) * v ^ k := by ring
      have h1 : |u * (u ^ k - v ^ k)| ≤ 1 * (k * |u - v|) := by
        rw [abs_mul]
        exact mul_le_mul (by rw [abs_of_nonneg hu0]; exact hu1) ih (abs_nonneg _)
          zero_le_one
      have h2 : |(u - v) * v ^ k| ≤ |u - v| * 1 := by
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [abs_of_nonneg (pow_nonneg hv0 k)]
        exact pow_le_one₀ hv0 hv1
      calc |u ^ (k + 1) - v ^ (k + 1)|
          = |u * (u ^ k - v ^ k) + (u - v) * v ^ k| := by rw [hstep]
        _ ≤ |u * (u ^ k - v ^ k)| + |(u - v) * v ^ k| := abs_add_le _ _
        _ ≤ 1 * (k * |u - v|) + |u - v| * 1 := add_le_add h1 h2
        _ = (k + 1 : ℕ) * |u - v| := by push_cast; ring

/-! ### The walk densities are Lipschitz in the kernel -/

lemma a5_le_one (W : Graphon Ω μ) : a5 W ≤ 1 := by
  have hint : Integrable (fun x ↦ walkIter W 2 x * walkIter W 3 x) μ :=
    integrable_of_bdd ((measurable_walkIter W 2).mul (measurable_walkIter W 3))
      fun x ↦ by
        rw [abs_of_nonneg (mul_nonneg (walkIter_nonneg W 2 x) (walkIter_nonneg W 3 x))]
        exact mul_le_one₀ (walkIter_le_one W 2 x) (walkIter_nonneg W 3 x)
          (walkIter_le_one W 3 x)
  calc a5 W ≤ ∫ _x : Ω, (1:ℝ) ∂μ :=
        integral_mono hint (integrable_const _) fun x ↦
          mul_le_one₀ (walkIter_le_one W 2 x) (walkIter_nonneg W 3 x)
            (walkIter_le_one W 3 x)
    _ = 1 := by simp

section Regular

variable (W : Graphon Ω μ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)

include hε0 hε1

/-- The regularized kernel is bounded below by `ε`. -/
lemma le_regularize (x y : Ω) : ε ≤ W.regularize ε hε0 hε1 x y := by
  rw [Graphon.regularize_apply]
  nlinarith [W.nonneg x y, sub_nonneg.mpr hε1]

/-- **The walk operator is `n`-Lipschitz in the kernel.** -/
lemma abs_walkIter_regularize_sub_le :
    ∀ (n : ℕ) (x : Ω),
      |walkIter (W.regularize ε hε0 hε1) n x - walkIter W n x| ≤ n * ε := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
      intro x
      set Wr := W.regularize ε hε0 hε1 with hWr
      have hpt : ∀ y, |Wr x y * walkIter Wr n y - W x y * walkIter W n y|
          ≤ ε + n * ε := by
        intro y
        have h1 : |Wr x y - W x y| ≤ ε := W.abs_regularize_sub_le ε hε0 hε1 x y
        have h2 : |walkIter Wr n y - walkIter W n y| ≤ n * ε := ih y
        have hsplit : Wr x y * walkIter Wr n y - W x y * walkIter W n y
            = (Wr x y - W x y) * walkIter Wr n y
              + W x y * (walkIter Wr n y - walkIter W n y) := by ring
        calc |Wr x y * walkIter Wr n y - W x y * walkIter W n y|
            = |(Wr x y - W x y) * walkIter Wr n y
                + W x y * (walkIter Wr n y - walkIter W n y)| := by rw [hsplit]
          _ ≤ |(Wr x y - W x y) * walkIter Wr n y|
                + |W x y * (walkIter Wr n y - walkIter W n y)| := abs_add_le _ _
          _ ≤ ε * 1 + 1 * (n * ε) := by
              refine add_le_add ?_ ?_
              · rw [abs_mul]
                exact mul_le_mul h1
                  (by rw [abs_of_nonneg (walkIter_nonneg Wr n y)]
                      exact walkIter_le_one Wr n y)
                  (abs_nonneg _) (le_trans (abs_nonneg _) h1)
              · rw [abs_mul]
                exact mul_le_mul
                  (by rw [abs_of_nonneg (W.nonneg x y)]; exact W.le_one x y)
                  h2 (abs_nonneg _) zero_le_one
          _ = ε + n * ε := by ring
      calc |walkIter Wr (n + 1) x - walkIter W (n + 1) x|
          = |∫ y, (Wr x y * walkIter Wr n y - W x y * walkIter W n y) ∂μ| := by
            rw [integral_sub (integrable_walkRow Wr n x) (integrable_walkRow W n x)]
            rfl
        _ ≤ ∫ y, |Wr x y * walkIter Wr n y - W x y * walkIter W n y| ∂μ :=
            abs_integral_le_integral_abs
        _ ≤ ∫ _y : Ω, (ε + n * ε) ∂μ :=
            integral_mono
              ((integrable_walkRow Wr n x).sub (integrable_walkRow W n x)).abs
              (integrable_const _) hpt
        _ = ε + n * ε := by simp
        _ = ((n : ℝ) + 1) * ε := by ring
        _ = ((n + 1 : ℕ) : ℝ) * ε := by push_cast; ring

lemma abs_a3_regularize_sub_le : |a3 (W.regularize ε hε0 hε1) - a3 W| ≤ 3 * ε := by
  set Wr := W.regularize ε hε0 hε1 with hWr
  calc |a3 Wr - a3 W| = |∫ x, (walkIter Wr 3 x - walkIter W 3 x) ∂μ| := by
        rw [integral_sub (integrable_walkIter Wr 3) (integrable_walkIter W 3)]
        rfl
    _ ≤ ∫ x, |walkIter Wr 3 x - walkIter W 3 x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _x : Ω, (3 * ε) ∂μ :=
        integral_mono ((integrable_walkIter Wr 3).sub (integrable_walkIter W 3)).abs
          (integrable_const _) fun x ↦ by
            simpa using abs_walkIter_regularize_sub_le W hε0 hε1 3 x
    _ = 3 * ε := by simp

lemma abs_a5_regularize_sub_le : |a5 (W.regularize ε hε0 hε1) - a5 W| ≤ 5 * ε := by
  set Wr := W.regularize ε hε0 hε1 with hWr
  have hε0' : (0:ℝ) ≤ ε := hε0
  have hpt : ∀ x : Ω, |walkIter Wr 2 x * walkIter Wr 3 x
      - walkIter W 2 x * walkIter W 3 x| ≤ 5 * ε := by
    intro x
    have h2 : |walkIter Wr 2 x - walkIter W 2 x| ≤ 2 * ε := by
      simpa using abs_walkIter_regularize_sub_le W hε0 hε1 2 x
    have h3 : |walkIter Wr 3 x - walkIter W 3 x| ≤ 3 * ε := by
      simpa using abs_walkIter_regularize_sub_le W hε0 hε1 3 x
    have hsplit : walkIter Wr 2 x * walkIter Wr 3 x - walkIter W 2 x * walkIter W 3 x
        = (walkIter Wr 2 x - walkIter W 2 x) * walkIter Wr 3 x
          + walkIter W 2 x * (walkIter Wr 3 x - walkIter W 3 x) := by ring
    calc |walkIter Wr 2 x * walkIter Wr 3 x - walkIter W 2 x * walkIter W 3 x|
        = |(walkIter Wr 2 x - walkIter W 2 x) * walkIter Wr 3 x
            + walkIter W 2 x * (walkIter Wr 3 x - walkIter W 3 x)| := by rw [hsplit]
      _ ≤ |(walkIter Wr 2 x - walkIter W 2 x) * walkIter Wr 3 x|
            + |walkIter W 2 x * (walkIter Wr 3 x - walkIter W 3 x)| := abs_add_le _ _
      _ ≤ (2 * ε) * 1 + 1 * (3 * ε) := by
          refine add_le_add ?_ ?_
          · rw [abs_mul]
            exact mul_le_mul h2
              (by rw [abs_of_nonneg (walkIter_nonneg Wr 3 x)]
                  exact walkIter_le_one Wr 3 x)
              (abs_nonneg _) (le_trans (abs_nonneg _) h2)
          · rw [abs_mul]
            exact mul_le_mul
              (by rw [abs_of_nonneg (walkIter_nonneg W 2 x)]
                  exact walkIter_le_one W 2 x)
              h3 (abs_nonneg _) zero_le_one
      _ = 5 * ε := by ring
  have iR : Integrable (fun x ↦ walkIter Wr 2 x * walkIter Wr 3 x) μ :=
    integrable_of_bdd ((measurable_walkIter Wr 2).mul (measurable_walkIter Wr 3))
      fun x ↦ by
        rw [abs_of_nonneg (mul_nonneg (walkIter_nonneg Wr 2 x) (walkIter_nonneg Wr 3 x))]
        exact mul_le_one₀ (walkIter_le_one Wr 2 x) (walkIter_nonneg Wr 3 x)
          (walkIter_le_one Wr 3 x)
  have iW : Integrable (fun x ↦ walkIter W 2 x * walkIter W 3 x) μ :=
    integrable_of_bdd ((measurable_walkIter W 2).mul (measurable_walkIter W 3))
      fun x ↦ by
        rw [abs_of_nonneg (mul_nonneg (walkIter_nonneg W 2 x) (walkIter_nonneg W 3 x))]
        exact mul_le_one₀ (walkIter_le_one W 2 x) (walkIter_nonneg W 3 x)
          (walkIter_le_one W 3 x)
  calc |a5 Wr - a5 W|
      = |∫ x, (walkIter Wr 2 x * walkIter Wr 3 x
          - walkIter W 2 x * walkIter W 3 x) ∂μ| := by
        rw [integral_sub iR iW]; rfl
    _ ≤ ∫ x, |walkIter Wr 2 x * walkIter Wr 3 x
          - walkIter W 2 x * walkIter W 3 x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _x : Ω, (5 * ε) ∂μ :=
        integral_mono (iR.sub iW).abs (integrable_const _) hpt
    _ = 5 * ε := by simp

end Regular

/-! ### The odd-walk inequality -/

/-- **`t(P₅,W)³ ≥ t(P₃,W)⁵` for every graphon on every probability space.**
This is the Proposition of `notes/blekherman_raymond.tex`, proved by the
graphon-native argument of §2 of that note: no finite host graph, no sampling,
and no assumption that `(Ω,μ)` is standard Borel. -/
theorem a3_pow_five_le_a5_pow_three (W : Graphon Ω μ) : a3 W ^ 5 ≤ a5 W ^ 3 := by
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  set ε : ℝ := min 1 (δ / 30) with hεdef
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεδ : 30 * ε ≤ δ := by
    have : ε ≤ δ / 30 := min_le_right _ _
    linarith
  set Wr := W.regularize ε hε0.le hε1 with hWr
  -- the regularized inequality
  have hreg : a3 Wr ^ 5 ≤ a5 Wr ^ 3 :=
    pow_le_pow_of_regular Wr hε0 hε1 (le_regularize W hε0.le hε1)
  -- the two Lipschitz estimates
  have h3 : |a3 Wr - a3 W| ≤ 3 * ε := abs_a3_regularize_sub_le W hε0.le hε1
  have h5 : |a5 Wr - a5 W| ≤ 5 * ε := abs_a5_regularize_sub_le W hε0.le hε1
  have p3 : |a3 W ^ 5 - a3 Wr ^ 5| ≤ 5 * |a3 W - a3 Wr| := by
    simpa using abs_pow_sub_pow_le (a3_nonneg W) (a3_le_one W) (a3_nonneg Wr)
      (a3_le_one Wr) 5
  have p5 : |a5 Wr ^ 3 - a5 W ^ 3| ≤ 3 * |a5 Wr - a5 W| := by
    simpa using abs_pow_sub_pow_le (a5_nonneg Wr) (a5_le_one Wr) (a5_nonneg W)
      (a5_le_one W) 3
  have e3 : |a3 W - a3 Wr| = |a3 Wr - a3 W| := abs_sub_comm _ _
  have q3 := abs_le.mp p3
  have q5 := abs_le.mp p5
  rw [e3] at q3
  linarith [q3.1, q3.2, q5.1, q5.2]

end Taeyoung.Methods.OddWalk
