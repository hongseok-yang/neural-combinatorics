import Taeyoung.Methods.OddWalk.Marginals

/-!
# One step of the chain induction

This is the engine of `notes/blekherman_raymond.tex` §2.  Writing
`h_k = T_W^{5-k} 1`, the graphon-native proof peels the walk one edge at a time:
if `K` is the pair marginal on the step `k → k+1`, with vertex marginals `u` and
`v`, then

```
∫∫ K (log W - log K)  +  ∫ u log u  +  ∫ v log h_{k+1}   ≤   ∫ u log h_k .
```

Iterating five times and closing with one more application of Gibbs turns the
left-hand sides into the sum of edge and vertex terms, while the right-hand side
telescopes to `log a₅`.

**No measure on `Ω⁶` is built.**  The step is one application of
`integral_mul_log_div_le_log_integral` *pointwise in the outer variable* — the
conditional density `z ↦ K y z / u y` is a probability density for each fixed
`y`, which is exactly the Markov property of the folded walk — followed by one
Fubini on `Ω²`.  That replaces the six-fold construction the finite proof
performs implicitly when it samples a random homomorphism.

All bounds are carried as an unrelated pair `0 < c ≤ · ≤ C`; nothing here needs
`C = c⁻¹`, and keeping them independent removes every inverse from the
arithmetic.
-/

namespace Taeyoung.Methods.OddWalk

open MeasureTheory
open Taeyoung Taeyoung.Methods.Link

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- On `[c, C]` with `c > 0` the logarithm is bounded.  Every integrability side
condition in this development is an instance of this. -/
lemma abs_log_le_of_mem {c C t : ℝ} (hc : 0 < c) (hlo : c ≤ t) (hhi : t ≤ C) :
    |Real.log t| ≤ |Real.log c| + |Real.log C| := by
  have ht : 0 < t := lt_of_lt_of_le hc hlo
  have h1 : Real.log c ≤ Real.log t := Real.log_le_log hc hlo
  have h2 : Real.log t ≤ Real.log C := Real.log_le_log ht hhi
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · linarith [neg_abs_le (Real.log c), abs_nonneg (Real.log C)]
  · linarith [le_abs_self (Real.log C), abs_nonneg (Real.log c)]

section Step

variable (W : Graphon Ω μ) {c C : ℝ} (hc : 0 < c)
  {u : Ω → ℝ} {K : Ω → Ω → ℝ} {h : Ω → ℝ}

include hc

/-- **The pointwise step.**  For each fixed `y`, Gibbs applied to the conditional
density `z ↦ K y z / u y` against the kernel `z ↦ W y z · h z`. -/
theorem step_pointwise
    (hK_meas : Measurable (Function.uncurry K)) (hh_meas : Measurable h)
    (hu_lo : ∀ x, c ≤ u x) (hu_hi : ∀ x, u x ≤ C)
    (hK_lo : ∀ y z, c ≤ K y z) (hK_hi : ∀ y z, K y z ≤ C)
    (hh_lo : ∀ x, c ≤ h x) (hh_hi : ∀ x, h x ≤ C)
    (hW_lo : ∀ y z, c ≤ W y z)
    (hKu : ∀ y, ∫ z, K y z ∂μ = u y) (y : Ω) :
    ∫ z, K y z * (Real.log (W y z) + Real.log (h z) + Real.log (u y)
        - Real.log (K y z)) ∂μ
      ≤ u y * Real.log (∫ z, W y z * h z ∂μ) := by
  have hu0 : 0 < u y := lt_of_lt_of_le hc (hu_lo y)
  have hC : 0 < C := lt_of_lt_of_le hc (le_trans (hu_lo y) (hu_hi y))
  -- the conditional density and the kernel
  have hκ_meas : Measurable (fun z ↦ K y z / u y) :=
    (measurable_row hK_meas y).div_const _
  have hH_meas : Measurable (fun z ↦ W y z * h z) :=
    (measurable_row W.measurable y).mul hh_meas
  have hκ_one : ∫ z, K y z / u y ∂μ = 1 := by
    rw [integral_div, hKu y]
    exact div_self (ne_of_gt hu0)
  have hκ_lo : ∀ z, c / C ≤ K y z / u y := fun z ↦ by
    rw [div_le_div_iff₀ hC hu0]
    nlinarith [hK_lo y z, hu_hi y, hc.le, hu0.le]
  have hκ_hi : ∀ z, K y z / u y ≤ C / c := fun z ↦ by
    rw [div_le_div_iff₀ hu0 hc]
    nlinarith [hK_hi y z, hu_lo y, hc.le, hu0.le, hC.le]
  have hH_lo : ∀ z, c * c ≤ W y z * h z := fun z ↦
    mul_le_mul (hW_lo y z) (hh_lo z) hc.le (le_trans hc.le (hW_lo y z))
  have hH_hi : ∀ z, W y z * h z ≤ C := fun z ↦ by
    calc W y z * h z ≤ 1 * C :=
          mul_le_mul (W.le_one y z) (hh_hi z) (le_trans hc.le (hh_lo z)) zero_le_one
      _ = C := one_mul _
  have gibbs := integral_mul_log_div_le_log_integral (ν := μ) hκ_meas hH_meas hκ_one
    ⟨c / C, by positivity, hκ_lo⟩ ⟨C / c, by positivity, hκ_hi⟩
    ⟨c * c, by positivity, hH_lo⟩ ⟨C, hC, hH_hi⟩
  -- rewrite the integrand of the left-hand side
  have hpt : ∀ z, K y z * (Real.log (W y z) + Real.log (h z) + Real.log (u y)
      - Real.log (K y z))
      = u y * ((K y z / u y) * Real.log ((W y z * h z) / (K y z / u y))) := by
    intro z
    have hK0 : 0 < K y z := lt_of_lt_of_le hc (hK_lo y z)
    have hW0 : 0 < W y z := lt_of_lt_of_le hc (hW_lo y z)
    have hh0 : 0 < h z := lt_of_lt_of_le hc (hh_lo z)
    have hrw : (W y z * h z) / (K y z / u y) = W y z * h z * u y / K y z := by
      field_simp
    rw [hrw, Real.log_div (by positivity) (ne_of_gt hK0),
      Real.log_mul (by positivity) (ne_of_gt hu0),
      Real.log_mul (ne_of_gt hW0) (ne_of_gt hh0)]
    field_simp
  calc ∫ z, K y z * (Real.log (W y z) + Real.log (h z) + Real.log (u y)
          - Real.log (K y z)) ∂μ
      = ∫ z, u y * ((K y z / u y)
          * Real.log ((W y z * h z) / (K y z / u y))) ∂μ :=
        integral_congr_ae (ae_of_all _ hpt)
    _ = u y * ∫ z, (K y z / u y)
          * Real.log ((W y z * h z) / (K y z / u y)) ∂μ := integral_const_mul _ _
    _ ≤ u y * Real.log (∫ z, W y z * h z ∂μ) :=
        mul_le_mul_of_nonneg_left gibbs hu0.le

end Step

end Taeyoung.Methods.OddWalk
