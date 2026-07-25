/-
# High-density theorem — integrability of the kernel integrand (M5/M6 shared machinery, part A)

The reflection/deficit/surplus arguments of `thm:r1` and `thm:strip` split the improper integral
`∫_{(0,∞)} s^{r-1}(ℓ+s)^{-m} ρ_{n,m}(q+s) ds` into finitely many regions.  For that splitting to be
valid the integrand must be integrable on `(0,∞)`.

We get integrability *for free* from the substitution `x = ℓ/(ℓ+s)`: the kernel integrand is the
`|f'|`-weighted pushforward of the finite-interval integrand `gInt`, which agrees on `(0,1)` with a
polynomial (hence is bounded and continuous, hence integrable on the bounded `Ioo 0 1`).  Mathlib's
change-of-variables integrability transfer then moves this to `Ioi 0`.
-/

import OddCycleBound.DenseRegion.KernelImproper

open MeasureTheory Set
open scoped BigOperators

namespace OddCycleBound.DenseRegion

/-- The improper-form kernel integrand `s ↦ s^{r-1}(ℓ+s)^{-m}·ρ_{n,m}(q+s)`, `n = m−2r`. -/
noncomputable def kernelIntegrand (m r : ℕ) (q ℓ : ℝ) : ℝ → ℝ :=
  fun s => s ^ (r - 1) / (ℓ + s) ^ m * rho (m - 2 * r) m (q + s)

/-- The finite-interval (bracket-form) integrand of `gform_eq`; continuous everywhere. -/
private noncomputable def Fform (m r : ℕ) (q ℓ : ℝ) : ℝ → ℝ :=
  fun x => x ^ (r - 1) * (1 - x) ^ (r - 1)
    * ((m / (m - 2 * r : ℕ) : ℝ)
        * ((q * x + ℓ * (1 - x)) ^ (m - 2 * r) + ((1 - q) * x + (-ℓ) * (1 - x)) ^ (m - 2 * r))
      - x * (q * x + ℓ * (1 - x)) ^ (m - 2 * r - 1))

/-- **Integrability (A).**  The kernel integrand is integrable on `(0,∞)` (`ℓ>0`, `r≥1`, `n≥1`). -/
lemma kernelIntegrand_integrableOn {m r : ℕ} (hr : r ≠ 0) (hn : 1 ≤ m - 2 * r) (q ℓ : ℝ)
    (hl : 0 < ℓ) : IntegrableOn (kernelIntegrand m r q ℓ) (Set.Ioi 0) := by
  -- `gInt` is integrable on the bounded `Ioo 0 1` (it agrees there with the continuous `Fform`)
  have hFint : IntegrableOn (Fform m r q ℓ) (Set.Ioo (0:ℝ) 1) :=
    (Continuous.integrableOn_Icc (by unfold Fform; fun_prop)).mono_set Set.Ioo_subset_Icc_self
  have hgInt : IntegrableOn (gInt m r q ℓ) (Set.Ioo (0:ℝ) 1) := by
    refine hFint.congr_fun ?_ measurableSet_Ioo
    intro x hx
    simp only [Set.mem_Ioo] at hx
    rw [gInt, Fform, bracket_eq_rho hn q ℓ x (ne_of_gt hx.1)]
  -- transfer to `Ioi 0` via change of variables
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun s hs => subst_hasDerivWithinAt hl s hs) (subst_injOn hl) (gInt m r q ℓ)
  rw [subst_image hl] at hiff
  have hconst : IntegrableOn
      (fun s => ℓ ^ (m - 2 * r + r) * kernelIntegrand m r q ℓ s) (Set.Ioi 0) := by
    refine (hiff.mp hgInt).congr_fun ?_ measurableSet_Ioi
    intro s hs
    simp only [Set.mem_Ioi] at hs
    exact subst_pointwise hl hr hn q s hs
  -- drop the positive constant `ℓ^{n+r}`
  have hcne : (ℓ ^ (m - 2 * r + r) : ℝ) ≠ 0 := by positivity
  have h2 : IntegrableOn
      (fun s => (ℓ ^ (m - 2 * r + r))⁻¹ * (ℓ ^ (m - 2 * r + r) * kernelIntegrand m r q ℓ s))
      (Set.Ioi 0) := hconst.const_mul _
  refine h2.congr_fun ?_ measurableSet_Ioi
  intro s _
  dsimp only
  rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]

end OddCycleBound.DenseRegion
