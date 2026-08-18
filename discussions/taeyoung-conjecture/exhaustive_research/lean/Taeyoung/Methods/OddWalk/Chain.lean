import Taeyoung.Methods.OddWalk.Step

/-!
# Integrating the pointwise step

`OddWalk/Step.lean` bounds the inner integral for each fixed outer point.  This
file integrates that bound and splits the left-hand side into the three pieces
the chain induction needs:

```
∫∫ K (log W - log K)  +  ∫ u log u  +  ∫ v log h   ≤   ∫ u log (T_W h) .
```

Two of the three come for free — `∫ z, K y z · log (u y) = u y · log (u y)` is
the first marginal identity, with no Fubini — and only the `v` term needs the
integrals swapped, using the second marginal identity.  Every integrability
side condition is the same observation: on `[c, C]` with `c > 0` the integrand
is bounded, and `μ` is a probability measure.
-/

namespace Taeyoung.Methods.OddWalk

open MeasureTheory
open Taeyoung Taeyoung.Methods.Link

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Sections of a bounded kernel -/

lemma measurable_inner {G : Ω → Ω → ℝ} (hG : Measurable (Function.uncurry G)) :
    Measurable fun y ↦ ∫ z, G y z ∂μ :=
  (hG.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

lemma integrable_row_of_bdd {G : Ω → Ω → ℝ} (hG : Measurable (Function.uncurry G))
    {M : ℝ} (hM : ∀ y z, |G y z| ≤ M) (y : Ω) : Integrable (fun z ↦ G y z) μ :=
  integrable_of_bdd (measurable_row hG y) (hM y)

lemma abs_inner_le {G : Ω → Ω → ℝ} (hG : Measurable (Function.uncurry G))
    {M : ℝ} (hM : ∀ y z, |G y z| ≤ M) (y : Ω) : |∫ z, G y z ∂μ| ≤ M := by
  calc |∫ z, G y z ∂μ| ≤ ∫ z, |G y z| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _z : Ω, M ∂μ :=
        integral_mono (integrable_row_of_bdd hG hM y).abs (integrable_const _)
          fun z ↦ hM y z
    _ = M := by simp

section Chain

variable (W : Graphon Ω μ) {c C : ℝ} (hc : 0 < c) (hC1 : 1 ≤ C)
  {u v : Ω → ℝ} {K : Ω → Ω → ℝ} {h : Ω → ℝ}

include hc hC1

/-- **The chain step.**  One edge of the walk, peeled. -/
theorem chain_step
    (hu_meas : Measurable u) (hv_meas : Measurable v)
    (hK_meas : Measurable (Function.uncurry K)) (hh_meas : Measurable h)
    (hu_lo : ∀ x, c ≤ u x) (hu_hi : ∀ x, u x ≤ C)
    (hv_lo : ∀ x, c ≤ v x) (hv_hi : ∀ x, v x ≤ C)
    (hK_lo : ∀ y z, c ≤ K y z) (hK_hi : ∀ y z, K y z ≤ C)
    (hh_lo : ∀ x, c ≤ h x) (hh_hi : ∀ x, h x ≤ C)
    (hW_lo : ∀ y z, c ≤ W y z)
    (hKu : ∀ y, ∫ z, K y z ∂μ = u y)
    (hKv : ∀ z, ∫ y, K y z ∂μ = v z) :
    (∫ y, ∫ z, K y z * (Real.log (W y z) - Real.log (K y z)) ∂μ ∂μ)
      + (∫ y, u y * Real.log (u y) ∂μ)
      + (∫ z, v z * Real.log (h z) ∂μ)
      ≤ ∫ y, u y * Real.log (∫ z, W y z * h z ∂μ) ∂μ := by
  have hC : (0:ℝ) < C := lt_of_lt_of_le zero_lt_one hC1
  set L : ℝ := |Real.log c| + |Real.log C| with hLdef
  have hL0 : (0:ℝ) ≤ L := by positivity
  -- uniform logarithm bounds
  have hlogW : ∀ y z, |Real.log (W y z)| ≤ L := fun y z ↦
    abs_log_le_of_mem hc (hW_lo y z) (le_trans (W.le_one y z) hC1)
  have hlogK : ∀ y z, |Real.log (K y z)| ≤ L := fun y z ↦
    abs_log_le_of_mem hc (hK_lo y z) (hK_hi y z)
  have hlogh : ∀ z, |Real.log (h z)| ≤ L := fun z ↦
    abs_log_le_of_mem hc (hh_lo z) (hh_hi z)
  have hlogu : ∀ y, |Real.log (u y)| ≤ L := fun y ↦
    abs_log_le_of_mem hc (hu_lo y) (hu_hi y)
  have hKabs : ∀ y z, |K y z| ≤ C := fun y z ↦ by
    rw [abs_of_nonneg (le_trans hc.le (hK_lo y z))]; exact hK_hi y z
  have huabs : ∀ y, |u y| ≤ C := fun y ↦ by
    rw [abs_of_nonneg (le_trans hc.le (hu_lo y))]; exact hu_hi y
  -- the three integrands
  have hE_meas : Measurable (Function.uncurry
      fun y z ↦ K y z * (Real.log (W y z) - Real.log (K y z))) :=
    hK_meas.mul ((W.measurable.log).sub hK_meas.log)
  have hE_bdd : ∀ y z, |K y z * (Real.log (W y z) - Real.log (K y z))| ≤ C * (L + L) :=
    fun y z ↦ by
      rw [abs_mul]
      exact mul_le_mul (hKabs y z)
        ((abs_sub _ _).trans (add_le_add (hlogW y z) (hlogK y z)))
        (abs_nonneg _) (le_trans (abs_nonneg _) (hKabs y z))
  have hH_meas : Measurable (Function.uncurry fun y z ↦ K y z * Real.log (h z)) :=
    hK_meas.mul (hh_meas.log.comp measurable_snd)
  have hH_bdd : ∀ y z, |K y z * Real.log (h z)| ≤ C * L := fun y z ↦ by
    rw [abs_mul]
    exact mul_le_mul (hKabs y z) (hlogh z) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hKabs y z))
  -- pointwise decomposition of the inner integral
  have hdecomp : ∀ y, ∫ z, K y z * (Real.log (W y z) + Real.log (h z)
        + Real.log (u y) - Real.log (K y z)) ∂μ
      = (∫ z, K y z * (Real.log (W y z) - Real.log (K y z)) ∂μ)
        + (∫ z, K y z * Real.log (h z) ∂μ)
        + u y * Real.log (u y) := by
    intro y
    have e1 : ∀ z, K y z * (Real.log (W y z) + Real.log (h z) + Real.log (u y)
        - Real.log (K y z))
        = (K y z * (Real.log (W y z) - Real.log (K y z))
            + K y z * Real.log (h z)) + K y z * Real.log (u y) := fun z ↦ by ring
    have i1 : Integrable (fun z ↦ K y z
        * (Real.log (W y z) - Real.log (K y z))) μ :=
      integrable_row_of_bdd hE_meas hE_bdd y
    have i2 : Integrable (fun z ↦ K y z * Real.log (h z)) μ :=
      integrable_row_of_bdd hH_meas hH_bdd y
    have i3 : Integrable (fun z ↦ K y z * Real.log (u y)) μ :=
      (integrable_of_bdd (μ := μ) (measurable_row hK_meas y) (hKabs y)).mul_const _
    have i12 : Integrable (fun z ↦ K y z * (Real.log (W y z) - Real.log (K y z))
        + K y z * Real.log (h z)) μ := i1.add i2
    rw [integral_congr_ae (ae_of_all _ e1), integral_add i12 i3,
      integral_add i1 i2, integral_mul_const, hKu y]
  -- the Fubini term
  have hfub : ∫ y, (∫ z, K y z * Real.log (h z) ∂μ) ∂μ
      = ∫ z, v z * Real.log (h z) ∂μ := by
    have hprod : Integrable
        (fun q : Ω × Ω ↦ K q.1 q.2 * Real.log (h q.2)) (μ.prod μ) :=
      integrable_prod_of_bdd hH_meas (C := C * L) fun q ↦ hH_bdd q.1 q.2
    calc ∫ y, (∫ z, K y z * Real.log (h z) ∂μ) ∂μ
        = ∫ z, (∫ y, K y z * Real.log (h z) ∂μ) ∂μ :=
          integral_integral_swap hprod
      _ = ∫ z, v z * Real.log (h z) ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
          show ∫ y, K y z * Real.log (h z) ∂μ = v z * Real.log (h z)
          rw [integral_mul_const, hKv z]
  -- integrability of the three summands as functions of `y`
  have jE : Integrable (fun y ↦ ∫ z, K y z
      * (Real.log (W y z) - Real.log (K y z)) ∂μ) μ :=
    integrable_of_bdd (measurable_inner hE_meas) (abs_inner_le hE_meas hE_bdd)
  have jH : Integrable (fun y ↦ ∫ z, K y z * Real.log (h z) ∂μ) μ :=
    integrable_of_bdd (measurable_inner hH_meas) (abs_inner_le hH_meas hH_bdd)
  have jU : Integrable (fun y ↦ u y * Real.log (u y)) μ :=
    integrable_of_bdd (hu_meas.mul hu_meas.log) fun y ↦ by
      rw [abs_mul]
      exact mul_le_mul (huabs y) (hlogu y) (abs_nonneg _)
        (le_trans (abs_nonneg _) (huabs y))
  -- the right-hand side
  have hTh_lo : ∀ y, c * c ≤ ∫ z, W y z * h z ∂μ := fun y ↦ by
    have hb : ∀ z, c * c ≤ W y z * h z := fun z ↦
      mul_le_mul (hW_lo y z) (hh_lo z) hc.le (le_trans hc.le (hW_lo y z))
    have hint : Integrable (fun z ↦ W y z * h z) μ :=
      integrable_of_bdd ((measurable_row W.measurable y).mul hh_meas) fun z ↦ by
        rw [abs_of_nonneg (mul_nonneg (W.nonneg y z) (le_trans hc.le (hh_lo z)))]
        calc W y z * h z ≤ 1 * C :=
              mul_le_mul (W.le_one y z) (hh_hi z) (le_trans hc.le (hh_lo z)) zero_le_one
          _ = C := one_mul _
    calc c * c = ∫ _z : Ω, c * c ∂μ := by simp
      _ ≤ ∫ z, W y z * h z ∂μ := integral_mono (integrable_const _) hint hb
  have hTh_hi : ∀ y, (∫ z, W y z * h z ∂μ) ≤ C := fun y ↦ by
    have hint : Integrable (fun z ↦ W y z * h z) μ :=
      integrable_of_bdd ((measurable_row W.measurable y).mul hh_meas) fun z ↦ by
        rw [abs_of_nonneg (mul_nonneg (W.nonneg y z) (le_trans hc.le (hh_lo z)))]
        calc W y z * h z ≤ 1 * C :=
              mul_le_mul (W.le_one y z) (hh_hi z) (le_trans hc.le (hh_lo z)) zero_le_one
          _ = C := one_mul _
    calc ∫ z, W y z * h z ∂μ ≤ ∫ _z : Ω, C ∂μ :=
          integral_mono hint (integrable_const _) fun z ↦ by
            calc W y z * h z ≤ 1 * C :=
                  mul_le_mul (W.le_one y z) (hh_hi z)
                    (le_trans hc.le (hh_lo z)) zero_le_one
              _ = C := one_mul _
      _ = C := by simp
  have jR : Integrable (fun y ↦ u y * Real.log (∫ z, W y z * h z ∂μ)) μ := by
    refine integrable_of_bdd
      (hu_meas.mul ((measurable_inner
        (W.measurable.mul (hh_meas.comp measurable_snd))).log))
      (C := C * (|Real.log (c * c)| + |Real.log C|)) fun y ↦ ?_
    rw [abs_mul]
    exact mul_le_mul (huabs y)
      (abs_log_le_of_mem (by positivity) (hTh_lo y) (hTh_hi y))
      (abs_nonneg _) (le_trans (abs_nonneg _) (huabs y))
  -- `Integrable.add` yields a function sum `f + g`; restate it in applied form so
  -- that `integral_add` matches the goal syntactically.
  have jEH : Integrable (fun y ↦ (∫ z, K y z
      * (Real.log (W y z) - Real.log (K y z)) ∂μ)
      + (∫ z, K y z * Real.log (h z) ∂μ)) μ := jE.add jH
  have jSum : Integrable (fun y ↦ (∫ z, K y z
      * (Real.log (W y z) - Real.log (K y z)) ∂μ)
      + (∫ z, K y z * Real.log (h z) ∂μ) + u y * Real.log (u y)) μ := jEH.add jU
  -- assemble
  have hmain : ∀ y, (∫ z, K y z * (Real.log (W y z) - Real.log (K y z)) ∂μ)
        + (∫ z, K y z * Real.log (h z) ∂μ) + u y * Real.log (u y)
      ≤ u y * Real.log (∫ z, W y z * h z ∂μ) := fun y ↦ by
    rw [← hdecomp y]
    exact step_pointwise W hc hK_meas hh_meas hu_lo hu_hi hK_lo hK_hi hh_lo hh_hi
      hW_lo hKu y
  calc (∫ y, ∫ z, K y z * (Real.log (W y z) - Real.log (K y z)) ∂μ ∂μ)
        + (∫ y, u y * Real.log (u y) ∂μ) + (∫ z, v z * Real.log (h z) ∂μ)
      = ∫ y, ((∫ z, K y z * (Real.log (W y z) - Real.log (K y z)) ∂μ)
          + (∫ z, K y z * Real.log (h z) ∂μ) + u y * Real.log (u y)) ∂μ := by
        rw [integral_add jEH jU, integral_add jE jH, hfub]
        ring
    _ ≤ ∫ y, u y * Real.log (∫ z, W y z * h z ∂μ) ∂μ :=
        integral_mono jSum jR hmain

end Chain

end Taeyoung.Methods.OddWalk
