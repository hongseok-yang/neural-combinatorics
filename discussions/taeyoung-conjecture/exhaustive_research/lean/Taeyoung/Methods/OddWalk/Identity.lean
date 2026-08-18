import Taeyoung.Methods.OddWalk.Chain

/-!
# The tree-entropy identity

In `notes/blekherman_raymond.tex` §2 the identity

```
E₀₁ + E₁₂ + E₂₃ + V₁ + V₂ = log a₃
```

is proved by evaluating `∫ f log f` for the `P₃` density `f` in two ways.  That
route needs the four-dimensional measure.  It is avoided here: because the
marginals are explicit quotients, every logarithm splits, and the identity
becomes scalar algebra in the two quantities

```
P_d = ∫ mMid · log d ,      P_A = ∫ mMid · log A .
```

Indeed `log kEnd(u,v) = log W(u,v) + log A(v) − log a₃`, so the `log W` cancels
inside `E`, leaving

```
Eend = log a₃ − P_A ,   Emid = log a₃ − 2P_d ,   Vmid = P_d + P_A − log a₃ ,
```

and `2·Eend + Emid + 2·Vmid = log a₃` follows by cancellation.  In the notation
of the note, `Eend = E₀₁ = E₂₃`, `Emid = E₁₂` and `Vmid = V₁ = V₂`.
-/

namespace Taeyoung.Methods.OddWalk

open MeasureTheory
open Taeyoung Taeyoung.Methods.Link

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Relative entropy is nonnegative

This replaces the two isolated vertices `P₀ ⊔ P₀` of the finite proof, which
exist there only to supply the factor `n²`. -/

theorem integral_mul_log_nonneg {u : Ω → ℝ} (hu_meas : Measurable u)
    (hu_one : ∫ x, u x ∂μ = 1)
    (hu_lo : ∃ a > 0, ∀ x, a ≤ u x) (hu_hi : ∃ b > 0, ∀ x, u x ≤ b) :
    0 ≤ ∫ x, u x * Real.log (u x) ∂μ := by
  obtain ⟨a, ha, hlo⟩ := hu_lo
  obtain ⟨b, hb, hhi⟩ := hu_hi
  have huabs : ∀ x, |u x| ≤ b := fun x ↦ by
    rw [abs_of_nonneg (le_trans ha.le (hlo x))]; exact hhi x
  have key := integral_mul_log_div_le_log_integral (ν := μ) hu_meas
    (measurable_const (a := (1 : ℝ))) hu_one ⟨a, ha, hlo⟩ ⟨b, hb, hhi⟩
    ⟨1, one_pos, fun _ ↦ le_rfl⟩ ⟨1, one_pos, fun _ ↦ le_rfl⟩
  have hpt : ∀ x, u x * Real.log (1 / u x) = -(u x * Real.log (u x)) := fun x ↦ by
    have hux : 0 < u x := lt_of_lt_of_le ha (hlo x)
    rw [one_div, Real.log_inv]; ring
  rw [integral_congr_ae (ae_of_all _ hpt), integral_neg] at key
  simp only [integral_const, measure_univ, smul_eq_mul] at key
  norm_num at key
  linarith

section Identity

variable (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
  (hW : ∀ x y, ε ≤ W x y)

include hε hε1 hW

/-! ### The two scalars -/

/-- `P_d = ∫ mMid · log d`. -/
noncomputable def Pd : ℝ := ∫ x, mMid W x * Real.log (walkIter W 1 x) ∂μ

/-- `P_A = ∫ mMid · log A`. -/
noncomputable def PA : ℝ := ∫ x, mMid W x * Real.log (walkIter W 2 x) ∂μ

/-- `V₁ = V₂` of the note. -/
noncomputable def Vmid : ℝ := ∫ x, mMid W x * Real.log (mMid W x) ∂μ

/-- `V₀ = V₃` of the note. -/
noncomputable def Vend : ℝ := ∫ x, mEnd W x * Real.log (mEnd W x) ∂μ

omit hε hε1 hW

/-! ### Bookkeeping bounds -/

private lemma mMid_abs (hε : 0 < ε) (hW : ∀ x y, ε ≤ W x y) (x : Ω) :
    |mMid W x| ≤ (ε ^ 3)⁻¹ := by
  rw [abs_of_nonneg (le_trans (by positivity) (mMid_bounds W hε hW x).1)]
  exact (mMid_bounds W hε hW x).2

private lemma integrable_mMid_mul_log (hε : 0 < ε) (hW : ∀ x y, ε ≤ W x y)
    {g : Ω → ℝ} (hg : Measurable g) {c C : ℝ} (hc : 0 < c)
    (hlo : ∀ x, c ≤ g x) (hhi : ∀ x, g x ≤ C) :
    Integrable (fun x ↦ mMid W x * Real.log (g x)) μ :=
  integrable_of_bdd ((measurable_mMid W).mul hg.log)
    (C := (ε ^ 3)⁻¹ * (|Real.log c| + |Real.log C|)) fun x ↦ by
      rw [abs_mul]
      exact mul_le_mul (mMid_abs W hε hW x) (abs_log_le_of_mem hc (hlo x) (hhi x))
        (abs_nonneg _) (le_trans (abs_nonneg _) (mMid_abs W hε hW x))

include hε hε1 hW

/-! ### `Vmid = P_d + P_A − log a₃` -/

theorem Vmid_eq : Vmid W = Pd W + PA W - Real.log (a3 W) := by
  have ha3 : 0 < a3 W := a3_pos W hε hW
  have hd : ∀ x : Ω, ε ≤ walkIter W 1 x := fun x ↦ by
    simpa using pow_le_walkIter W hε.le hW 1 x
  have hA : ∀ x : Ω, ε ^ 2 ≤ walkIter W 2 x := fun x ↦ pow_le_walkIter W hε.le hW 2 x
  have hpt : ∀ x : Ω, mMid W x * Real.log (mMid W x)
      = mMid W x * Real.log (walkIter W 1 x)
        + mMid W x * Real.log (walkIter W 2 x)
        - mMid W x * Real.log (a3 W) := by
    intro x
    have h1 : 0 < walkIter W 1 x := lt_of_lt_of_le hε (hd x)
    have h2 : 0 < walkIter W 2 x := lt_of_lt_of_le (by positivity) (hA x)
    have hlog : Real.log (mMid W x)
        = Real.log (walkIter W 1 x) + Real.log (walkIter W 2 x)
          - Real.log (a3 W) := by
      show Real.log (walkIter W 1 x * walkIter W 2 x / a3 W) = _
      rw [Real.log_div (by positivity) (ne_of_gt ha3),
        Real.log_mul (ne_of_gt h1) (ne_of_gt h2)]
    rw [hlog]; ring
  have i1 : Integrable (fun x ↦ mMid W x * Real.log (walkIter W 1 x)) μ :=
    integrable_mMid_mul_log W hε hW (measurable_walkIter W 1) hε hd
      (walkIter_le_one W 1)
  have i2 : Integrable (fun x ↦ mMid W x * Real.log (walkIter W 2 x)) μ :=
    integrable_mMid_mul_log W hε hW (measurable_walkIter W 2) (by positivity) hA
      (walkIter_le_one W 2)
  have i3 : Integrable (fun x ↦ mMid W x * Real.log (a3 W)) μ :=
    (integrable_of_bdd (μ := μ) (measurable_mMid W) (mMid_abs W hε hW)).mul_const _
  have i12 : Integrable (fun x ↦ mMid W x * Real.log (walkIter W 1 x)
      + mMid W x * Real.log (walkIter W 2 x)) μ := i1.add i2
  show ∫ x, mMid W x * Real.log (mMid W x) ∂μ = _
  rw [integral_congr_ae (ae_of_all _ hpt), integral_sub i12 i3, integral_add i1 i2,
    integral_mul_const, integral_mMid W hε hW, one_mul]
  rfl


/-! ### The two edge terms -/

omit hε hε1 hW

/-- `E₀₁ = E₂₃` of the note. -/
noncomputable def Eend : ℝ :=
  ∫ u, ∫ v, kEnd W u v * (Real.log (W u v) - Real.log (kEnd W u v)) ∂μ ∂μ

/-- `E₁₂` of the note. -/
noncomputable def Emid : ℝ :=
  ∫ u, ∫ v, kMid W u v * (Real.log (W u v) - Real.log (kMid W u v)) ∂μ ∂μ

private lemma kEnd_abs (hε : 0 < ε) (hW : ∀ x y, ε ≤ W x y) (u v : Ω) :
    |kEnd W u v| ≤ (ε ^ 3)⁻¹ := by
  rw [abs_of_nonneg (le_trans (by positivity) (kEnd_bounds W hε hW u v).1)]
  exact (kEnd_bounds W hε hW u v).2

private lemma kMid_abs (hε : 0 < ε) (hW : ∀ x y, ε ≤ W x y) (u v : Ω) :
    |kMid W u v| ≤ (ε ^ 3)⁻¹ := by
  rw [abs_of_nonneg (le_trans (by positivity) (kMid_bounds W hε hW u v).1)]
  exact (kMid_bounds W hε hW u v).2

/-- The generic bound behind every integrability side condition below: a kernel
bounded by `(ε³)⁻¹` against the logarithm of a function in `[c, C]`. -/
private lemma kernel_log_bdd {Kk : Ω → Ω → ℝ}
    (hKb : ∀ u v, |Kk u v| ≤ (ε ^ 3)⁻¹)
    {g : Ω → ℝ} {c C : ℝ} (hc : 0 < c)
    (hlo : ∀ x, c ≤ g x) (hhi : ∀ x, g x ≤ C) (u v : Ω) :
    |Kk u v * Real.log (g v)| ≤ (ε ^ 3)⁻¹ * (|Real.log c| + |Real.log C|) := by
  rw [abs_mul]
  exact mul_le_mul (hKb u v) (abs_log_le_of_mem hc (hlo v) (hhi v)) (abs_nonneg _)
    (le_trans (abs_nonneg _) (hKb u v))

include hε hε1 hW

/-! ### `Eend = log a₃ − P_A` -/

theorem Eend_eq : Eend W = Real.log (a3 W) - PA W := by
  have ha3 : 0 < a3 W := a3_pos W hε hW
  have hA : ∀ x : Ω, ε ^ 2 ≤ walkIter W 2 x := fun x ↦ pow_le_walkIter W hε.le hW 2 x
  have hA0 : (0:ℝ) < ε ^ 2 := by positivity
  -- integrability of the two pieces of the inner integral
  have mA : Measurable (Function.uncurry
      fun u v ↦ kEnd W u v * Real.log (walkIter W 2 v)) :=
    (measurable_kEnd W).mul ((measurable_walkIter W 2).log.comp measurable_snd)
  have bA : ∀ u v : Ω, |kEnd W u v * Real.log (walkIter W 2 v)|
      ≤ (ε ^ 3)⁻¹ * (|Real.log (ε ^ 2)| + |Real.log 1|) := fun u v ↦
    kernel_log_bdd (kEnd_abs W hε hW) hA0 hA (walkIter_le_one W 2) u v
  have iA : ∀ u : Ω, Integrable (fun v ↦ kEnd W u v * Real.log (walkIter W 2 v)) μ :=
    fun u ↦ integrable_row_of_bdd mA bA u
  have iC : ∀ u : Ω, Integrable (fun v ↦ kEnd W u v * Real.log (a3 W)) μ := fun u ↦
    (integrable_of_bdd (μ := μ) (measurable_row (measurable_kEnd W) u)
      (kEnd_abs W hε hW u)).mul_const _
  -- pointwise: the `log W` cancels
  have hpt : ∀ u v : Ω, kEnd W u v * (Real.log (W u v) - Real.log (kEnd W u v))
      = kEnd W u v * Real.log (a3 W) - kEnd W u v * Real.log (walkIter W 2 v) := by
    intro u v
    have hW0 : 0 < W u v := lt_of_lt_of_le hε (hW u v)
    have hA0' : 0 < walkIter W 2 v := lt_of_lt_of_le hA0 (hA v)
    have hlog : Real.log (kEnd W u v)
        = Real.log (W u v) + Real.log (walkIter W 2 v) - Real.log (a3 W) := by
      show Real.log (W u v * walkIter W 2 v / a3 W) = _
      rw [Real.log_div (by positivity) (ne_of_gt ha3),
        Real.log_mul (ne_of_gt hW0) (ne_of_gt hA0')]
    rw [hlog]; ring
  -- the inner integral
  have hinner : ∀ u : Ω,
      (∫ v, kEnd W u v * (Real.log (W u v) - Real.log (kEnd W u v)) ∂μ)
        = mEnd W u * Real.log (a3 W)
          - ∫ v, kEnd W u v * Real.log (walkIter W 2 v) ∂μ := by
    intro u
    rw [integral_congr_ae (ae_of_all _ (hpt u)), integral_sub (iC u) (iA u),
      integral_mul_const, integral_kEnd_right W u]
  -- Fubini on the surviving term
  have hfub : (∫ u, (∫ v, kEnd W u v * Real.log (walkIter W 2 v) ∂μ) ∂μ) = PA W := by
    have hprod : Integrable (fun q : Ω × Ω ↦
        kEnd W q.1 q.2 * Real.log (walkIter W 2 q.2)) (μ.prod μ) :=
      integrable_prod_of_bdd mA fun q ↦ bA q.1 q.2
    calc (∫ u, (∫ v, kEnd W u v * Real.log (walkIter W 2 v) ∂μ) ∂μ)
        = ∫ v, (∫ u, kEnd W u v * Real.log (walkIter W 2 v) ∂μ) ∂μ :=
          integral_integral_swap hprod
      _ = PA W := by
          refine integral_congr_ae (ae_of_all _ fun v ↦ ?_)
          show ∫ u, kEnd W u v * Real.log (walkIter W 2 v) ∂μ
              = mMid W v * Real.log (walkIter W 2 v)
          rw [integral_mul_const, integral_kEnd_left W v]
  -- assemble
  have jC : Integrable (fun u ↦ mEnd W u * Real.log (a3 W)) μ :=
    (integrable_of_bdd (μ := μ) (measurable_mEnd W) fun u ↦ by
      rw [abs_of_nonneg (le_trans (by positivity) (mEnd_bounds W hε hW u).1)]
      exact (mEnd_bounds W hε hW u).2).mul_const _
  have jA : Integrable (fun u ↦ ∫ v, kEnd W u v * Real.log (walkIter W 2 v) ∂μ) μ :=
    integrable_of_bdd (measurable_inner mA) (abs_inner_le mA bA)
  show (∫ u, ∫ v, kEnd W u v * (Real.log (W u v) - Real.log (kEnd W u v)) ∂μ ∂μ) = _
  rw [integral_congr_ae (ae_of_all _ hinner), integral_sub jC jA, integral_mul_const,
    integral_mEnd W hε hW, one_mul, hfub]


/-! ### `Emid = log a₃ − 2·P_d` -/

theorem Emid_eq : Emid W = Real.log (a3 W) - 2 * Pd W := by
  have ha3 : 0 < a3 W := a3_pos W hε hW
  have hd : ∀ x : Ω, ε ≤ walkIter W 1 x := fun x ↦ by
    simpa using pow_le_walkIter W hε.le hW 1 x
  -- the three pieces of the inner integrand
  have mV : Measurable (Function.uncurry
      fun u v ↦ kMid W u v * Real.log (walkIter W 1 v)) :=
    (measurable_kMid W).mul ((measurable_walkIter W 1).log.comp measurable_snd)
  have bV : ∀ u v : Ω, |kMid W u v * Real.log (walkIter W 1 v)|
      ≤ (ε ^ 3)⁻¹ * (|Real.log ε| + |Real.log 1|) := fun u v ↦
    kernel_log_bdd (kMid_abs W hε hW) hε hd (walkIter_le_one W 1) u v
  have bU : ∀ u v : Ω, |kMid W u v * Real.log (walkIter W 1 u)|
      ≤ (ε ^ 3)⁻¹ * (|Real.log ε| + |Real.log 1|) := fun u v ↦ by
    rw [abs_mul]
    exact mul_le_mul (kMid_abs W hε hW u v)
      (abs_log_le_of_mem hε (hd u) (walkIter_le_one W 1 u)) (abs_nonneg _)
      (le_trans (abs_nonneg _) (kMid_abs W hε hW u v))
  have iV : ∀ u : Ω, Integrable (fun v ↦ kMid W u v * Real.log (walkIter W 1 v)) μ :=
    fun u ↦ integrable_row_of_bdd mV bV u
  have iU : ∀ u : Ω, Integrable (fun v ↦ kMid W u v * Real.log (walkIter W 1 u)) μ :=
    fun u ↦ (integrable_of_bdd (μ := μ) (measurable_row (measurable_kMid W) u)
      (kMid_abs W hε hW u)).mul_const _
  have iC : ∀ u : Ω, Integrable (fun v ↦ kMid W u v * Real.log (a3 W)) μ := fun u ↦
    (integrable_of_bdd (μ := μ) (measurable_row (measurable_kMid W) u)
      (kMid_abs W hε hW u)).mul_const _
  -- pointwise: the `log W` cancels, leaving both endpoint degrees
  have hpt : ∀ u v : Ω, kMid W u v * (Real.log (W u v) - Real.log (kMid W u v))
      = kMid W u v * Real.log (a3 W) - kMid W u v * Real.log (walkIter W 1 u)
        - kMid W u v * Real.log (walkIter W 1 v) := by
    intro u v
    have hW0 : 0 < W u v := lt_of_lt_of_le hε (hW u v)
    have hdu : 0 < walkIter W 1 u := lt_of_lt_of_le hε (hd u)
    have hdv : 0 < walkIter W 1 v := lt_of_lt_of_le hε (hd v)
    have hlog : Real.log (kMid W u v)
        = Real.log (W u v) + Real.log (walkIter W 1 u) + Real.log (walkIter W 1 v)
          - Real.log (a3 W) := by
      show Real.log (W u v * walkIter W 1 u * walkIter W 1 v / a3 W) = _
      rw [Real.log_div (by positivity) (ne_of_gt ha3),
        Real.log_mul (by positivity) (ne_of_gt hdv),
        Real.log_mul (ne_of_gt hW0) (ne_of_gt hdu)]
    rw [hlog]; ring
  -- the inner integral
  have hinner : ∀ u : Ω,
      (∫ v, kMid W u v * (Real.log (W u v) - Real.log (kMid W u v)) ∂μ)
        = mMid W u * Real.log (a3 W) - mMid W u * Real.log (walkIter W 1 u)
          - ∫ v, kMid W u v * Real.log (walkIter W 1 v) ∂μ := by
    intro u
    have iCU : Integrable (fun v ↦ kMid W u v * Real.log (a3 W)
        - kMid W u v * Real.log (walkIter W 1 u)) μ := (iC u).sub (iU u)
    rw [integral_congr_ae (ae_of_all _ (hpt u)), integral_sub iCU (iV u),
      integral_sub (iC u) (iU u), integral_mul_const, integral_mul_const,
      integral_kMid_right W u]
  -- Fubini on the surviving term
  have hfub : (∫ u, (∫ v, kMid W u v * Real.log (walkIter W 1 v) ∂μ) ∂μ) = Pd W := by
    have hprod : Integrable (fun q : Ω × Ω ↦
        kMid W q.1 q.2 * Real.log (walkIter W 1 q.2)) (μ.prod μ) :=
      integrable_prod_of_bdd mV fun q ↦ bV q.1 q.2
    calc (∫ u, (∫ v, kMid W u v * Real.log (walkIter W 1 v) ∂μ) ∂μ)
        = ∫ v, (∫ u, kMid W u v * Real.log (walkIter W 1 v) ∂μ) ∂μ :=
          integral_integral_swap hprod
      _ = Pd W := by
          refine integral_congr_ae (ae_of_all _ fun v ↦ ?_)
          show ∫ u, kMid W u v * Real.log (walkIter W 1 v) ∂μ
              = mMid W v * Real.log (walkIter W 1 v)
          rw [integral_mul_const, integral_kMid_left W v]
  -- assemble
  have mMabs : ∀ u : Ω, |mMid W u| ≤ (ε ^ 3)⁻¹ := mMid_abs W hε hW
  have jC : Integrable (fun u ↦ mMid W u * Real.log (a3 W)) μ :=
    (integrable_of_bdd (μ := μ) (measurable_mMid W) mMabs).mul_const _
  have jU : Integrable (fun u ↦ mMid W u * Real.log (walkIter W 1 u)) μ :=
    integrable_mMid_mul_log W hε hW (measurable_walkIter W 1) hε hd
      (walkIter_le_one W 1)
  have jV : Integrable (fun u ↦ ∫ v, kMid W u v * Real.log (walkIter W 1 v) ∂μ) μ :=
    integrable_of_bdd (measurable_inner mV) (abs_inner_le mV bV)
  have jCU : Integrable (fun u ↦ mMid W u * Real.log (a3 W)
      - mMid W u * Real.log (walkIter W 1 u)) μ := jC.sub jU
  show (∫ u, ∫ v, kMid W u v * (Real.log (W u v) - Real.log (kMid W u v)) ∂μ ∂μ) = _
  rw [integral_congr_ae (ae_of_all _ hinner), integral_sub jCU jV,
    integral_sub jC jU, integral_mul_const, integral_mMid W hε hW, one_mul, hfub]
  show _ = Real.log (a3 W) - 2 * Pd W
  have : (∫ u, mMid W u * Real.log (walkIter W 1 u) ∂μ) = Pd W := rfl
  rw [this]
  ring

/-! ### The identity -/

/-- **The tree-entropy identity**, `E₀₁ + E₁₂ + E₂₃ + V₁ + V₂ = log a₃` of the
note, with `E₀₁ = E₂₃ = Eend` and `V₁ = V₂ = Vmid`. -/
theorem tree_entropy_identity :
    2 * Eend W + Emid W + 2 * Vmid W = Real.log (a3 W) := by
  rw [Eend_eq W hε hε1 hW, Emid_eq W hε hε1 hW, Vmid_eq W hε hε1 hW]
  ring

end Identity

end Taeyoung.Methods.OddWalk
