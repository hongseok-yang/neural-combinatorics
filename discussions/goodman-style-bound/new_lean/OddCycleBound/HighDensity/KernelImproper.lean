/-
# High-density theorem — the improper `∫₀^∞` kernel form (M5/M6 gateway, `prop:kernel`)

The finite Beta(r,r) form `gform_eq` becomes the paper's improper-integral form (`eq:kernel`) under the
substitution `x = ℓ/(ℓ+s)`, `u = q+s` (for `ℓ > 0`):
`P̃_{m,r}(q,ℓ) = C_{m,r}·ℓ^{n+r} ∫₀^∞ s^{r-1}(ℓ+s)^{-m} ρ_{n,m}(q+s) ds`,  `n = m−2r`.

This is the reflection-friendly form on which `thm:r1` and `thm:strip` operate.  The `∫₀^∞` is realised
as a Lebesgue integral over `Set.Ioi 0`; the substitution is Mathlib's one-dimensional change of
variables `integral_image_eq_integral_abs_deriv_smul` with the bijection `Ioi 0 ≃ Ioo 0 1`.
-/

import OddCycleBound.HighDensity.KernelForm
import Mathlib.MeasureTheory.Function.JacobianOneDim

open MeasureTheory Set
open scoped BigOperators

namespace OddCycleBound.HighDensity

/-- The substitution `s ↦ ℓ/(ℓ+s)` maps `(0,∞)` onto `(0,1)` (for `ℓ > 0`). -/
lemma subst_image {ℓ : ℝ} (hl : 0 < ℓ) :
    (fun s => ℓ / (ℓ + s)) '' Set.Ioi (0:ℝ) = Set.Ioo 0 1 := by
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    simp only [Set.mem_Ioi] at hs
    exact ⟨by positivity, by rw [div_lt_one (by positivity)]; linarith⟩
  · intro hy
    simp only [Set.mem_Ioo] at hy
    refine ⟨ℓ * (1 - y) / y, ?_, ?_⟩
    · simp only [Set.mem_Ioi]; exact div_pos (by nlinarith [hy.1, hy.2]) hy.1
    · have hy0 : y ≠ 0 := ne_of_gt hy.1
      have : ℓ + ℓ * (1 - y) / y ≠ 0 := by
        rw [show ℓ + ℓ * (1 - y) / y = ℓ / y from by field_simp; ring]
        positivity
      field_simp
      ring

/-- The substitution's derivative `HasDerivWithinAt (s ↦ ℓ/(ℓ+s)) (−ℓ/(ℓ+s)²) (Ioi 0) s`. -/
lemma subst_hasDerivWithinAt {ℓ : ℝ} (hl : 0 < ℓ) (s : ℝ) (hs : s ∈ Set.Ioi (0:ℝ)) :
    HasDerivWithinAt (fun s => ℓ / (ℓ + s)) (-(ℓ / (ℓ + s) ^ 2)) (Set.Ioi 0) s := by
  simp only [Set.mem_Ioi] at hs
  have hne : ℓ + s ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => ℓ + s) 1 s := by simpa using (hasDerivAt_id s).const_add ℓ
  have h := (hasDerivAt_const s ℓ).div h1 hne
  simp only [zero_mul, mul_one, zero_sub] at h
  rw [show (-ℓ / (ℓ + s) ^ 2) = -(ℓ / (ℓ + s) ^ 2) from by ring] at h
  exact h.hasDerivWithinAt

/-- The substitution is injective on `(0,∞)`. -/
lemma subst_injOn {ℓ : ℝ} (hl : 0 < ℓ) : Set.InjOn (fun s => ℓ / (ℓ + s)) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hane : ℓ + a ≠ 0 := by positivity
  have hbne : ℓ + b ≠ 0 := by positivity
  simp only at hab
  field_simp at hab
  linarith

/-- The coefficient of the substituted integrand: `ℓ/(ℓ+s)²·X^{r-1}(1-X)^{r-1}X^{n} =
ℓ^{n+r}·s^{r-1}/(ℓ+s)^m`, where `X = ℓ/(ℓ+s)`, `1-X = s/(ℓ+s)`, `n = m−2r`, `m = n+2r`. -/
lemma subst_coef {ℓ : ℝ} (hl : 0 < ℓ) {m r : ℕ} (hr : r ≠ 0) (hn : 1 ≤ m - 2 * r) (s : ℝ)
    (hs : 0 < s) :
    ℓ / (ℓ + s) ^ 2
        * ((ℓ / (ℓ + s)) ^ (r - 1) * (s / (ℓ + s)) ^ (r - 1) * (ℓ / (ℓ + s)) ^ (m - 2 * r))
      = ℓ ^ (m - 2 * r + r) * (s ^ (r - 1) / (ℓ + s) ^ m) := by
  have hpos : (0 : ℝ) < ℓ + s := by linarith
  have hℓ : ℓ ^ (m - 2 * r + r) = ℓ ^ 1 * ℓ ^ (r - 1) * ℓ ^ (m - 2 * r) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hden : (ℓ + s) ^ m
      = (ℓ + s) ^ 2 * (ℓ + s) ^ (r - 1) * (ℓ + s) ^ (r - 1) * (ℓ + s) ^ (m - 2 * r) := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega
  rw [div_pow, div_pow, div_pow, hℓ, hden]
  field_simp

/-- The `ρ`-form integrand of `gform_eq`: `x^{r-1}(1-x)^{r-1}·xⁿ·ρ(Vₓ/x)` (`n = m−2r`). -/
private noncomputable def gInt (m r : ℕ) (q ℓ : ℝ) : ℝ → ℝ :=
  fun x => x ^ (r - 1) * (1 - x) ^ (r - 1)
    * (x ^ (m - 2 * r) * rho (m - 2 * r) m ((q * x + ℓ * (1 - x)) / x))

/-- **`prop:kernel` — the improper `∫₀^∞` kernel form.**  For `ℓ > 0`, `r ≥ 1`, `n = m−2r ≥ 1`:
`P̃_{m,r}(q,ℓ) = C_{m,r}·ℓ^{n+r} ∫_{(0,∞)} s^{r-1}(ℓ+s)^{-m} ρ_{n,m}(q+s) ds`.  Obtained from `gform_eq`
by the change of variables `x = ℓ/(ℓ+s)` (`Ioi 0 ≃ Ioo 0 1`), which sends the finite integrand to
`ℓ^{n+r}·s^{r-1}(ℓ+s)^{-m}·ρ(q+s)`. -/
lemma kernel_form {m r : ℕ} (hr : r ≠ 0) (hn : 1 ≤ m - 2 * r) (q ℓ : ℝ) (hl : 0 < ℓ) :
    diagKernel m r q ℓ
      = Cmr m r * ℓ ^ (m - 2 * r + r)
        * ∫ s in Set.Ioi (0:ℝ), s ^ (r - 1) / (ℓ + s) ^ m * rho (m - 2 * r) m (q + s) := by
  have harg : ∀ s : ℝ, 0 < s →
      (q * (ℓ / (ℓ + s)) + ℓ * (1 - ℓ / (ℓ + s))) / (ℓ / (ℓ + s)) = q + s := by
    intro s hs
    have : ℓ + s ≠ 0 := by positivity
    field_simp; ring
  have step1 : diagKernel m r q ℓ = Cmr m r * ∫ x in Set.Ioc (0:ℝ) 1, gInt m r q ℓ x := by
    rw [gform_eq hr hn, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    simp only [Set.mem_Ioc] at hx
    rw [bracket_eq_rho hn q ℓ x (ne_of_gt hx.1)]
    rfl
  have step2 : (∫ x in Set.Ioc (0:ℝ) 1, gInt m r q ℓ x)
      = ∫ x in Set.Ioo (0:ℝ) 1, gInt m r q ℓ x :=
    MeasureTheory.integral_Ioc_eq_integral_Ioo
  have step3 : (∫ x in Set.Ioo (0:ℝ) 1, gInt m r q ℓ x)
      = ∫ s in Set.Ioi (0:ℝ), |(-(ℓ / (ℓ + s) ^ 2))| • gInt m r q ℓ (ℓ / (ℓ + s)) := by
    rw [← subst_image hl,
      integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
        (fun s hs => subst_hasDerivWithinAt hl s hs) (subst_injOn hl)]
  have step4 : (∫ s in Set.Ioi (0:ℝ), |(-(ℓ / (ℓ + s) ^ 2))| • gInt m r q ℓ (ℓ / (ℓ + s)))
      = ∫ s in Set.Ioi (0:ℝ),
          ℓ ^ (m - 2 * r + r) * (s ^ (r - 1) / (ℓ + s) ^ m * rho (m - 2 * r) m (q + s)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    simp only [Set.mem_Ioi] at hs
    rw [smul_eq_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < ℓ / (ℓ + s) ^ 2)]
    simp only [gInt]
    have h1x : (1:ℝ) - ℓ / (ℓ + s) = s / (ℓ + s) := by
      have hne : ℓ + s ≠ 0 := by positivity
      field_simp; ring
    rw [harg s hs, h1x]
    linear_combination rho (m - 2 * r) m (q + s) * subst_coef hl hr hn s hs
  rw [step1, step2, step3, step4, MeasureTheory.integral_const_mul, ← mul_assoc]

end OddCycleBound.HighDensity
