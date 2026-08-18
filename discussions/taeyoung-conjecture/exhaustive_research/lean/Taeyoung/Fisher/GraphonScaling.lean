-- Vendored from `discussions/goodman-style-bound/fisher_lean`
-- (`OddCycleBound/Fisher/GraphonScaling.lean`), Lean v4.31.0, Mathlib rev fabf563a.
-- Only the `import` lines differ from the upstream file; see
-- `Taeyoung/Fisher.lean` for why the copy exists.
import Taeyoung.Fisher.GraphonContinuity

/-!
# Scaling graphons into the interior of a density band

Multiplying a graphon by a scalar in `[0,1]` preserves the graphon axioms.
This elementary device lets the finite-step transfer work with strict density
margins, even when the original graphon has edge density exactly `2/3`.
-/

open MeasureTheory Filter
open scoped Topology

namespace OddCycleBound

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Scalar multiplication of a kernel, written pointwise to keep the graphon
interface independent of bundled function-space structure. -/
def scaleKernel (c : ℝ) (W : Ω → Ω → ℝ) : Ω → Ω → ℝ :=
  fun x y => c * W x y

theorem isGraphon_scaleKernel {W : Ω → Ω → ℝ} (hW : IsGraphon W μ)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsGraphon (scaleKernel c W) μ := by
  refine ⟨hW.meas.const_mul c, ?_, ?_, ?_⟩
  · intro x y
    exact mul_nonneg hc0 (hW.nonneg x y)
  · intro x y
    change c * W x y ≤ 1
    simpa using mul_le_mul hc1 (hW.le_one x y) (hW.nonneg x y)
      (by norm_num : (0 : ℝ) ≤ 1)
  · intro x y
    simp only [scaleKernel, hW.symm x y]

theorem degree_scaleKernel (W : Ω → Ω → ℝ) (c : ℝ) (x : Ω) :
    degree (scaleKernel c W) μ x = c * degree W μ x := by
  simp only [degree, kernelOp, scaleKernel]
  rw [integral_const_mul]

theorem edgeDensity_scaleKernel (W : Ω → Ω → ℝ) (c : ℝ) :
    edgeDensity (scaleKernel c W) μ = c * edgeDensity W μ := by
  simp only [edgeDensity, mean, degree_scaleKernel]
  rw [integral_const_mul]

theorem triangleDensity_scaleKernel {W : Ω → Ω → ℝ} (hW : IsGraphon W μ)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    trace μ (compPow μ (scaleKernel c W) 2) =
      c ^ 3 * trace μ (compPow μ W 2) := by
  rw [trace_compPow_two_eq_triangleIntegral
      (isGraphon_scaleKernel hW hc0 hc1),
    trace_compPow_two_eq_triangleIntegral hW]
  simp only [scaleKernel]
  have hpoint : ∀ x y z,
      (c * W x y) * (c * W y z) * (c * W z x) =
        c ^ 3 * (W x y * W y z * W z x) := by
    intros
    ring
  simp_rw [hpoint]
  simp_rw [integral_const_mul]

theorem kernelL1Dist_scaleKernel_self {W : Ω → Ω → ℝ}
    (hW : IsGraphon W μ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    kernelL1Dist (μ := μ) (scaleKernel c W) W =
      (1 - c) * edgeDensity W μ := by
  simp only [kernelL1Dist, scaleKernel, edgeDensity, mean, degree, kernelOp]
  have hpoint : ∀ x y, |c * W x y - W x y| = (1 - c) * W x y := by
    intro x y
    rw [show c * W x y - W x y = -(1 - c) * W x y by ring,
      abs_mul, abs_neg, abs_of_nonneg (sub_nonneg.mpr hc1),
      abs_of_nonneg (hW.nonneg x y)]
  simp_rw [hpoint, integral_const_mul]

/-- A canonical sequence in `[0,1)` tending to `1`. -/
noncomputable def interiorScaleCoeff (n : ℕ) : ℝ :=
  1 - 1 / ((n : ℝ) + 1)

theorem interiorScaleCoeff_nonneg (n : ℕ) :
    0 ≤ interiorScaleCoeff n := by
  unfold interiorScaleCoeff
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hp : 0 < (n : ℝ) + 1 := lt_of_lt_of_le (by norm_num) hn
  have hinv : 1 / ((n : ℝ) + 1) ≤ 1 := by
    exact (div_le_one hp).2 hn
  linarith

theorem interiorScaleCoeff_lt_one (n : ℕ) :
    interiorScaleCoeff n < 1 := by
  unfold interiorScaleCoeff
  have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
  linarith

theorem tendsto_interiorScaleCoeff :
    Tendsto interiorScaleCoeff atTop (𝓝 1) := by
  unfold interiorScaleCoeff
  simpa using (tendsto_const_nhds.sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

/-- Scale a graphon by coefficients tending to one, after discarding a
finite prefix, so every scaled edge density lies strictly inside
`(1/2, 2/3)`. -/
theorem exists_interior_scaled_graphons {W : Ω → Ω → ℝ}
    (hW : IsGraphon W μ)
    (hlo : 1 / 2 < edgeDensity W μ)
    (hhi : edgeDensity W μ ≤ 2 / 3) :
    ∃ A : ℕ → Ω → Ω → ℝ,
      (∀ n, IsGraphon (A n) μ) ∧
      Tendsto (fun n => kernelL1Dist (μ := μ) (A n) W) atTop (𝓝 0) ∧
      ∀ n, 1 / 2 < edgeDensity (A n) μ ∧
        edgeDensity (A n) μ < 2 / 3 := by
  let p := edgeDensity W μ
  have hp0 : 0 < p := lt_trans (by norm_num) hlo
  have hscaled : Tendsto (fun n => interiorScaleCoeff n * p) atTop (𝓝 p) := by
    simpa [p] using tendsto_interiorScaleCoeff.mul_const p
  have hevent : ∀ᶠ n in atTop, 1 / 2 < interiorScaleCoeff n * p :=
    hscaled.eventually (Ioi_mem_nhds hlo)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hevent)
  let A : ℕ → Ω → Ω → ℝ :=
    fun n => scaleKernel (interiorScaleCoeff (n + N)) W
  refine ⟨A, ?_, ?_, ?_⟩
  · intro n
    exact isGraphon_scaleKernel hW (interiorScaleCoeff_nonneg _)
      (interiorScaleCoeff_lt_one _).le
  · have hcshift : Tendsto (fun n => interiorScaleCoeff (n + N)) atTop (𝓝 1) :=
      (tendsto_add_atTop_iff_nat N).2 tendsto_interiorScaleCoeff
    have hdist : (fun n => kernelL1Dist (μ := μ) (A n) W) =
        fun n => (1 - interiorScaleCoeff (n + N)) * p := by
      funext n
      exact kernelL1Dist_scaleKernel_self hW (interiorScaleCoeff_nonneg _)
        (interiorScaleCoeff_lt_one _).le
    rw [hdist]
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    simpa using (hone.sub hcshift).mul_const p
  · intro n
    rw [edgeDensity_scaleKernel]
    constructor
    · exact hN (n + N) (Nat.le_add_left N n)
    · calc
        interiorScaleCoeff (n + N) * p < 1 * p :=
          mul_lt_mul_of_pos_right (interiorScaleCoeff_lt_one _) hp0
        _ = p := one_mul p
        _ ≤ 2 / 3 := hhi

end OddCycleBound
