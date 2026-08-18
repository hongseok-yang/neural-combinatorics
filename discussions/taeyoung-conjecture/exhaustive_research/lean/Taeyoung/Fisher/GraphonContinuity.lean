-- Vendored from `discussions/goodman-style-bound/fisher_lean`
-- (`OddCycleBound/Fisher/GraphonContinuity.lean`), Lean v4.31.0, Mathlib rev fabf563a.
-- Only the `import` lines differ from the upstream file; see
-- `Taeyoung/Fisher.lean` for why the copy exists.
import Taeyoung.Fisher.Kernel

/-!
# Elementary density-continuity estimates for graphons

These estimates isolate the closed-limit part of the finite-graph-to-graphon
transfer.  The distance used here is the nested `L¹` distance, which is enough
for both edge and triangle homomorphism densities.
-/

open MeasureTheory Filter
open scoped Topology

namespace OddCycleBound

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Nested `L¹` distance between two kernels. -/
noncomputable def kernelL1Dist (U W : Ω → Ω → ℝ) : ℝ :=
  ∫ x, ∫ y, |U x y - W x y| ∂μ ∂μ

private def triangleIntegrand (U : Ω → Ω → ℝ) (p : (Ω × Ω) × Ω) : ℝ :=
  U p.1.1 p.1.2 * U p.1.2 p.2 * U p.2 p.1.1

private lemma triangleIntegrand_measurable {U : Ω → Ω → ℝ}
    (hU : IsGraphon U μ) : Measurable (triangleIntegrand U) := by
  have hxy : Measurable (fun p : (Ω × Ω) × Ω => U p.1.1 p.1.2) :=
    hU.meas.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_fst))
  have hyz : Measurable (fun p : (Ω × Ω) × Ω => U p.1.2 p.2) :=
    hU.meas.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hzx : Measurable (fun p : (Ω × Ω) × Ω => U p.2 p.1.1) :=
    hU.meas.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
  exact (hxy.mul hyz).mul hzx

private lemma triangleIntegrand_integrable {U : Ω → Ω → ℝ}
    (hU : IsGraphon U μ) :
    Integrable (triangleIntegrand U) ((μ.prod μ).prod μ) := by
  apply (integrable_const (1 : ℝ)).mono'
    (triangleIntegrand_measurable hU).aestronglyMeasurable
  refine ae_of_all _ fun p => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · have hab : U p.1.1 p.1.2 * U p.1.2 p.2 ≤ 1 :=
      mul_le_one₀ (hU.le_one _ _) (hU.nonneg _ _) (hU.le_one _ _)
    exact mul_le_one₀ hab (hU.nonneg _ _) (hU.le_one _ _)
  · exact mul_nonneg (mul_nonneg (hU.nonneg _ _) (hU.nonneg _ _))
      (hU.nonneg _ _)

private lemma graphon_row_integrable {U : Ω → Ω → ℝ}
    (hU : IsGraphon U μ) (x : Ω) :
    Integrable (fun y => U x y) μ :=
  (goodK_of_isGraphon hU).integrable_row x

/-- The cyclic trace used by the interface is the usual nested triangle
integral. -/
theorem trace_compPow_two_eq_triangleIntegral
    {U : Ω → Ω → ℝ} (hU : IsGraphon U μ) :
    trace μ (compPow μ U 2) =
      ∫ x, ∫ y, ∫ z, U x y * U y z * U z x ∂μ ∂μ ∂μ := by
  simp only [compPow, trace, comp]
  apply integral_congr_ae
  refine ae_of_all _ fun x => integral_congr_ae (ae_of_all _ fun y => ?_)
  change U x y * (∫ z, U y z * U z x ∂μ) =
    ∫ z, U x y * U y z * U z x ∂μ
  conv_rhs =>
    enter [2, z]
    rw [show U x y * U y z * U z x = U x y * (U y z * U z x) by ring]
  rw [integral_const_mul]

private theorem trace_compPow_two_eq_integral_triangleIntegrand
    {U : Ω → Ω → ℝ} (hU : IsGraphon U μ) :
    trace μ (compPow μ U 2) =
      ∫ p, triangleIntegrand U p ∂((μ.prod μ).prod μ) := by
  rw [trace_compPow_two_eq_triangleIntegral hU]
  have hint := triangleIntegrand_integrable hU
  rw [integral_prod _ hint,
    integral_prod _ hint.integral_prod_left]
  rfl

private lemma abs_graphon_sub_le_one {U W : Ω → Ω → ℝ}
    (hU : IsGraphon U μ) (hW : IsGraphon W μ) (x y : Ω) :
    |U x y - W x y| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [hU.nonneg x y, hU.le_one x y,
    hW.nonneg x y, hW.le_one x y]

private lemma abs_mul_three_sub_mul_three_le
    {a b c d e f : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (he : 0 ≤ e) (he1 : e ≤ 1) (hf : 0 ≤ f) (hf1 : f ≤ 1) :
    |a * b * c - d * e * f| ≤ |a - d| + |b - e| + |c - f| := by
  let x := (a - d) * b * c
  let y := d * (b - e) * c
  let z := d * e * (c - f)
  have hsplit : a * b * c - d * e * f = x + y + z := by
    dsimp [x, y, z]
    ring
  have htri : |x + y + z| ≤ |x| + |y| + |z| := by
    linarith [abs_add_le (x + y) z, abs_add_le x y]
  have hx : |x| ≤ |a - d| := by
    dsimp [x]
    rw [abs_mul, abs_mul, abs_of_nonneg hb, abs_of_nonneg hc]
    calc
      |a - d| * b * c ≤ |a - d| * 1 * 1 := by gcongr
      _ = |a - d| := by ring
  have hy : |y| ≤ |b - e| := by
    dsimp [y]
    rw [abs_mul, abs_mul, abs_of_nonneg hd, abs_of_nonneg hc]
    calc
      d * |b - e| * c ≤ 1 * |b - e| * 1 := by gcongr
      _ = |b - e| := by ring
  have hz : |z| ≤ |c - f| := by
    dsimp [z]
    rw [abs_mul, abs_mul, abs_of_nonneg hd, abs_of_nonneg he]
    calc
      d * e * |c - f| ≤ 1 * 1 * |c - f| := by gcongr
      _ = |c - f| := by ring
  rw [hsplit]
  exact htri.trans (add_le_add (add_le_add hx hy) hz)

private def triangleDiffX (U W : Ω → Ω → ℝ) (p : (Ω × Ω) × Ω) : ℝ :=
  |U p.1.1 p.1.2 - W p.1.1 p.1.2|

private def triangleDiffY (U W : Ω → Ω → ℝ) (p : (Ω × Ω) × Ω) : ℝ :=
  |U p.1.2 p.2 - W p.1.2 p.2|

private def triangleDiffZ (U W : Ω → Ω → ℝ) (p : (Ω × Ω) × Ω) : ℝ :=
  |U p.1.1 p.2 - W p.1.1 p.2|

private lemma triangleDiffX_integrable {U W : Ω → Ω → ℝ}
    (hU : IsGraphon U μ) (hW : IsGraphon W μ) :
    Integrable (triangleDiffX U W) ((μ.prod μ).prod μ) := by
  have hm : Measurable (triangleDiffX U W) :=
    (hU.meas.sub hW.meas).abs.comp
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_fst))
  exact (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]
      simpa [triangleDiffX] using abs_graphon_sub_le_one hU hW p.1.1 p.1.2)

private lemma triangleDiffY_integrable {U W : Ω → Ω → ℝ}
    (hU : IsGraphon U μ) (hW : IsGraphon W μ) :
    Integrable (triangleDiffY U W) ((μ.prod μ).prod μ) := by
  have hm : Measurable (triangleDiffY U W) :=
    (hU.meas.sub hW.meas).abs.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  exact (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]
      simpa [triangleDiffY] using abs_graphon_sub_le_one hU hW p.1.2 p.2)

private lemma triangleDiffZ_integrable {U W : Ω → Ω → ℝ}
    (hU : IsGraphon U μ) (hW : IsGraphon W μ) :
    Integrable (triangleDiffZ U W) ((μ.prod μ).prod μ) := by
  have hm : Measurable (triangleDiffZ U W) :=
    (hU.meas.sub hW.meas).abs.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  exact (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]
      simpa [triangleDiffZ] using abs_graphon_sub_le_one hU hW p.1.1 p.2)

private lemma integral_triangleDiffX {U W : Ω → Ω → ℝ}
    (hU : IsGraphon U μ) (hW : IsGraphon W μ) :
    (∫ p, triangleDiffX U W p ∂((μ.prod μ).prod μ)) =
      kernelL1Dist (μ := μ) U W := by
  have hint := triangleDiffX_integrable hU hW
  rw [integral_prod _ hint, integral_prod _ hint.integral_prod_left]
  simp [triangleDiffX, kernelL1Dist]

private lemma integral_triangleDiffY {U W : Ω → Ω → ℝ}
    (hU : IsGraphon U μ) (hW : IsGraphon W μ) :
    (∫ p, triangleDiffY U W p ∂((μ.prod μ).prod μ)) =
      kernelL1Dist (μ := μ) U W := by
  have hint := triangleDiffY_integrable hU hW
  rw [integral_prod _ hint, integral_prod _ hint.integral_prod_left]
  simp [triangleDiffY, kernelL1Dist]

private lemma integral_triangleDiffZ {U W : Ω → Ω → ℝ}
    (hU : IsGraphon U μ) (hW : IsGraphon W μ) :
    (∫ p, triangleDiffZ U W p ∂((μ.prod μ).prod μ)) =
      kernelL1Dist (μ := μ) U W := by
  have hint := triangleDiffZ_integrable hU hW
  rw [integral_prod _ hint, integral_prod _ hint.integral_prod_left]
  simp [triangleDiffZ, kernelL1Dist]

/-- Triangle density is `3`-Lipschitz in nested `L¹`. -/
theorem abs_triangleDensity_sub_le_three_mul_kernelL1Dist
    {U W : Ω → Ω → ℝ} (hU : IsGraphon U μ) (hW : IsGraphon W μ) :
    |trace μ (compPow μ U 2) - trace μ (compPow μ W 2)| ≤
      3 * kernelL1Dist (μ := μ) U W := by
  rw [trace_compPow_two_eq_integral_triangleIntegrand hU,
    trace_compPow_two_eq_integral_triangleIntegrand hW]
  have hIU := triangleIntegrand_integrable hU
  have hIW := triangleIntegrand_integrable hW
  rw [← integral_sub hIU hIW]
  calc
    |∫ p, triangleIntegrand U p - triangleIntegrand W p
        ∂((μ.prod μ).prod μ)| ≤
      ∫ p, |triangleIntegrand U p - triangleIntegrand W p|
        ∂((μ.prod μ).prod μ) := abs_integral_le_integral_abs
    _ ≤ ∫ p, triangleDiffX U W p + triangleDiffY U W p + triangleDiffZ U W p
        ∂((μ.prod μ).prod μ) := by
      apply integral_mono (hIU.sub hIW).abs
        ((triangleDiffX_integrable hU hW).add
          (triangleDiffY_integrable hU hW) |>.add
            (triangleDiffZ_integrable hU hW))
      intro p
      simpa [triangleIntegrand, triangleDiffX, triangleDiffY, triangleDiffZ,
        Pi.sub_apply, Pi.add_apply, hU.symm p.2 p.1.1, hW.symm p.2 p.1.1] using
        (abs_mul_three_sub_mul_three_le
          (hU.nonneg p.1.1 p.1.2) (hU.le_one p.1.1 p.1.2)
          (hU.nonneg p.1.2 p.2) (hU.le_one p.1.2 p.2)
          (hU.nonneg p.2 p.1.1) (hU.le_one p.2 p.1.1)
          (hW.nonneg p.1.1 p.1.2) (hW.le_one p.1.1 p.1.2)
          (hW.nonneg p.1.2 p.2) (hW.le_one p.1.2 p.2)
          (hW.nonneg p.2 p.1.1) (hW.le_one p.2 p.1.1))
    _ = 3 * kernelL1Dist (μ := μ) U W := by
      rw [integral_add, integral_add,
        integral_triangleDiffX hU hW, integral_triangleDiffY hU hW,
        integral_triangleDiffZ hU hW]
      · ring
      · exact triangleDiffX_integrable hU hW
      · exact triangleDiffY_integrable hU hW
      · exact (triangleDiffX_integrable hU hW).add
          (triangleDiffY_integrable hU hW)
      · exact triangleDiffZ_integrable hU hW

/-- Edge density is `1`-Lipschitz in nested `L¹`. -/
theorem abs_edgeDensity_sub_le_kernelL1Dist
    {U W : Ω → Ω → ℝ} (hU : IsGraphon U μ) (hW : IsGraphon W μ) :
    |edgeDensity U μ - edgeDensity W μ| ≤ kernelL1Dist (μ := μ) U W := by
  have hdegU : Integrable (degree U μ) μ :=
    (good_degree (μ := μ) hU).integrable
  have hdegW : Integrable (degree W μ) μ :=
    (good_degree (μ := μ) hW).integrable
  rw [edgeDensity, edgeDensity, mean, mean, ← integral_sub hdegU hdegW]
  calc
    |∫ x, degree U μ x - degree W μ x ∂μ| ≤
        ∫ x, |degree U μ x - degree W μ x| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, ∫ y, |U x y - W x y| ∂μ ∂μ := by
      apply integral_mono (hdegU.sub hdegW).abs
      · have hmeas : StronglyMeasurable
            (fun x => ∫ y, |U x y - W x y| ∂μ) := by
          have hjoint : StronglyMeasurable
              (fun p : Ω × Ω => |U p.1 p.2 - W p.1 p.2|) :=
            (hU.meas.sub hW.meas).abs.stronglyMeasurable
          exact hjoint.integral_prod_right'
        exact (integrable_const (2 : ℝ)).mono' hmeas.aestronglyMeasurable
          (ae_of_all _ fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
            calc
              ∫ y, |U x y - W x y| ∂μ ≤ ∫ _y, (2 : ℝ) ∂μ := by
                apply integral_mono
                  ((graphon_row_integrable hU x).sub
                    (graphon_row_integrable hW x)).abs
                  (integrable_const 2)
                intro y
                change |U x y - W x y| ≤ 2
                rw [abs_le]
                constructor <;> linarith [hU.nonneg x y, hU.le_one x y,
                  hW.nonneg x y, hW.le_one x y]
              _ = 2 := by simp)
      · intro x
        change |(∫ y, U x y ∂μ) - ∫ y, W x y ∂μ| ≤ _
        rw [← integral_sub (graphon_row_integrable hU x)
          (graphon_row_integrable hW x)]
        exact abs_integral_le_integral_abs
    _ = kernelL1Dist (μ := μ) U W := rfl

/-- Closed-limit package for density inequalities.  Once finite/step graphons
are supplied with `L¹` error tending to zero, no further graphon-density
continuity work is needed. -/
theorem density_inequality_of_kernelL1_approx
    {W : Ω → Ω → ℝ} (hW : IsGraphon W μ)
    (A : ℕ → Ω → Ω → ℝ) (hA : ∀ n, IsGraphon (A n) μ)
    (happrox : Tendsto
      (fun n => kernelL1Dist (μ := μ) (A n) W) atTop (𝓝 0))
    (F : ℝ → ℝ) (hF : ContinuousAt F (edgeDensity W μ))
    (hineq : ∀ n,
      F (edgeDensity (A n) μ) ≤ trace μ (compPow μ (A n) 2)) :
    F (edgeDensity W μ) ≤ trace μ (compPow μ W 2) := by
  have hedgeDist : Tendsto
      (fun n => dist (edgeDensity (A n) μ) (edgeDensity W μ))
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun n => by
        simpa [Real.dist_eq] using
          abs_edgeDensity_sub_le_kernelL1Dist (hA n) hW)
      happrox
  have hedge : Tendsto (fun n => edgeDensity (A n) μ) atTop
      (𝓝 (edgeDensity W μ)) :=
    tendsto_iff_dist_tendsto_zero.mpr hedgeDist
  have hthree : Tendsto
      (fun n => 3 * kernelL1Dist (μ := μ) (A n) W) atTop (𝓝 0) := by
    simpa using happrox.const_mul 3
  have htriangleDist : Tendsto
      (fun n => dist (trace μ (compPow μ (A n) 2))
        (trace μ (compPow μ W 2))) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun n => by
        simpa [Real.dist_eq] using
          abs_triangleDensity_sub_le_three_mul_kernelL1Dist (hA n) hW)
      hthree
  have htriangle : Tendsto (fun n => trace μ (compPow μ (A n) 2)) atTop
      (𝓝 (trace μ (compPow μ W 2))) :=
    tendsto_iff_dist_tendsto_zero.mpr htriangleDist
  exact le_of_tendsto_of_tendsto' (hF.tendsto.comp hedge) htriangle hineq

end OddCycleBound
