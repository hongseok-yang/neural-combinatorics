import OddCycleBound.IntermediateRegion.OneSidedPolynomial
import OddCycleBound.IntermediateRegion.TracePowers

/-!
# Direct kernel block decomposition

This file develops the kernel analogue of the hub/body block decomposition.
It works on the project's arbitrary probability-space interface and therefore
does not depend on choosing a concrete step partition.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.Spectral.L2Kernel

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {K : Omega → Omega → Real}

/-- The centered degree of a general bounded measurable kernel is good. -/
lemma good_degCentered_of_goodK (hK : GoodK K) :
    Good (degCentered K mu) := by
  have hdegree : Good (degree K mu) := by
    have heq : degree K mu = kernelOp K mu (fun _ : Omega => 1) := by
      funext x
      simp [degree, kernelOp]
    rw [heq]
    exact good_kernelOp_goodK (mu := mu) hK good_one
  exact good_sub hdegree
    (OddCycleBound.DenseRegion.good_const (Omega := Omega) (edgeDensity K mu))

/-- The centered degree has mean zero for every good kernel. -/
lemma mean_degCentered_of_goodK (hK : GoodK K) :
    mean mu (degCentered K mu) = 0 := by
  have hdegree : Good (degree K mu) := by
    have heq : degree K mu = kernelOp K mu (fun _ : Omega => 1) := by
      funext x
      simp [degree, kernelOp]
    rw [heq]
    exact good_kernelOp_goodK (mu := mu) hK good_one
  simp [mean, degCentered, edgeDensity, integral_sub, hdegree.integrable]

/-- The centered kernel of an arbitrary good kernel is again good. -/
lemma centeredKernel_goodK_of_goodK (hK : GoodK K) :
    GoodK (centeredKernel K mu) := by
  have hdegree : Good (degree K mu) := by
    have heq : degree K mu = kernelOp K mu (fun _ : Omega => 1) := by
      funext x
      simp [degree, kernelOp]
    rw [heq]
    exact good_kernelOp_goodK (mu := mu) hK good_one
  refine ⟨?_, ?_⟩
  · exact (((hK.meas.sub (hdegree.meas.measurable.comp measurable_fst)).sub
      (hdegree.meas.measurable.comp measurable_snd)).add measurable_const)
  · obtain ⟨C, hC0, hKC⟩ := hK.bdd
    refine ⟨3 * C + |edgeDensity K mu|,
      add_nonneg (mul_nonneg (by norm_num) hC0) (abs_nonneg _), ?_⟩
    intro x y
    unfold centeredKernel
    have hdegx : |degree K mu x| ≤ C := by
      unfold degree
      calc
        |∫ z, K x z ∂mu| ≤ ∫ z, |K x z| ∂mu :=
          abs_integral_le_integral_abs
        _ ≤ ∫ _z, C ∂mu := by
              exact integral_mono
                (hK.integrable_row x).abs (integrable_const _)
                (fun z => hKC x z)
        _ = C := by simp
    have hdegy : |degree K mu y| ≤ C := by
      unfold degree
      calc
        |∫ z, K y z ∂mu| ≤ ∫ z, |K y z| ∂mu :=
          abs_integral_le_integral_abs
        _ ≤ ∫ _z, C ∂mu := by
              exact integral_mono
                (hK.integrable_row y).abs (integrable_const _)
                (fun z => hKC y z)
        _ = C := by simp
    calc
      |K x y - degree K mu x - degree K mu y + edgeDensity K mu| ≤
          |K x y| + |degree K mu x| + |degree K mu y| +
            |edgeDensity K mu| := by
              calc
                _ ≤ |K x y - degree K mu x - degree K mu y| +
                    |edgeDensity K mu| := abs_add_le _ _
                _ ≤ (|K x y - degree K mu x| + |degree K mu y|) +
                    |edgeDensity K mu| :=
                      add_le_add (abs_sub _ _) (le_refl _)
                _ ≤ (|K x y| + |degree K mu x| + |degree K mu y|) +
                    |edgeDensity K mu| :=
                      add_le_add (add_le_add (abs_sub _ _) (le_refl _))
                        (le_refl _)
      _ ≤ C + C + C + |edgeDensity K mu| := by linarith [hKC x y]
      _ = 3 * C + |edgeDensity K mu| := by ring

/-- Pointwise reconstruction from the hub scalar, centered degree, and
centered body kernel. -/
theorem kernel_eq_block_decomposition (K : Omega → Omega → Real) (x y : Omega) :
    K x y = edgeDensity K mu + degCentered K mu x +
      degCentered K mu y + centeredKernel K mu x y := by
  unfold degCentered centeredKernel
  ring

/-- Every row of a centered good kernel has integral zero. -/
theorem integral_centeredKernel_row (hK : GoodK K) (x : Omega) :
    ∫ y, centeredKernel K mu x y ∂mu = 0 := by
  have hdegree : Good (degree K mu) := by
    have heq : degree K mu = kernelOp K mu (fun _ : Omega => 1) := by
      funext z
      simp [degree, kernelOp]
    rw [heq]
    exact good_kernelOp_goodK (mu := mu) hK good_one
  unfold centeredKernel
  have hrow : Integrable (fun y => K x y) mu := hK.integrable_row x
  have hdegreeX : Integrable (fun _ : Omega => degree K mu x) mu :=
    integrable_const _
  have hedge : Integrable (fun _ : Omega => edgeDensity K mu) mu :=
    integrable_const _
  calc
    (∫ y, K x y - degree K mu x - degree K mu y +
        edgeDensity K mu ∂mu) =
        (∫ y, K x y - degree K mu x - degree K mu y ∂mu) +
          ∫ _y : Omega, edgeDensity K mu ∂mu := by
            exact integral_add
              ((hrow.sub hdegreeX).sub hdegree.integrable) hedge
    _ = ((∫ y, K x y - degree K mu x ∂mu) -
          ∫ y, degree K mu y ∂mu) +
          ∫ _y : Omega, edgeDensity K mu ∂mu := by
            exact congrArg
              (fun z : Real => z + ∫ _y : Omega, edgeDensity K mu ∂mu)
              (integral_sub (hrow.sub hdegreeX) hdegree.integrable)
    _ = (((∫ y, K x y ∂mu) -
          ∫ _y : Omega, degree K mu x ∂mu) -
          ∫ y, degree K mu y ∂mu) +
          ∫ _y : Omega, edgeDensity K mu ∂mu := by
            exact congrArg
              (fun z : Real => (z - ∫ y, degree K mu y ∂mu) +
                ∫ _y : Omega, edgeDensity K mu ∂mu)
              (integral_sub hrow hdegreeX)
    _ = 0 := by
      simp [degree, edgeDensity, mean]

/-- For a symmetric good kernel, every centered column also has integral
zero. -/
theorem integral_centeredKernel_col
    (hK : GoodK K) (hsymm : ∀ x y, K x y = K y x) (y : Omega) :
    ∫ x, centeredKernel K mu x y ∂mu = 0 := by
  have hcentSymm : ∀ x y, centeredKernel K mu x y = centeredKernel K mu y x := by
    intro x z
    unfold centeredKernel
    rw [hsymm x z]
    ring
  calc
    (∫ x, centeredKernel K mu x y ∂mu) =
        ∫ x, centeredKernel K mu y x ∂mu := by
          exact integral_congr_ae (ae_of_all _ fun x => hcentSymm x y)
    _ = 0 := integral_centeredKernel_row hK y

/-- Centering removes exactly the scalar hub contribution from the kernel
trace. -/
theorem trace_centeredKernel (hK : GoodK K) :
    trace mu (centeredKernel K mu) = trace mu K - edgeDensity K mu := by
  have hg := good_degCentered_of_goodK (mu := mu) hK
  have hmean := mean_degCentered_of_goodK (mu := mu) hK
  unfold trace
  calc
    (∫ x, centeredKernel K mu x x ∂mu) =
        ∫ x, K x x - edgeDensity K mu -
          2 * degCentered K mu x ∂mu := by
            refine integral_congr_ae (ae_of_all _ fun x => ?_)
            unfold centeredKernel degCentered
            ring
    _ = (∫ x, K x x ∂mu) - edgeDensity K mu -
          2 * ∫ x, degCentered K mu x ∂mu := by
            have hdiag : Integrable (fun x => K x x) mu := hK.diag_integrable
            have hconst : Integrable (fun _x : Omega => edgeDensity K mu) mu :=
              integrable_const _
            have htwo : Integrable (fun x => 2 * degCentered K mu x) mu :=
              hg.integrable.const_mul 2
            calc
              (∫ x, K x x - edgeDensity K mu -
                  2 * degCentered K mu x ∂mu) =
                  (∫ x, K x x - edgeDensity K mu ∂mu) -
                    ∫ x, 2 * degCentered K mu x ∂mu := by
                      exact integral_sub (hdiag.sub hconst) htwo
              _ = ((∫ x, K x x ∂mu) -
                    ∫ _x : Omega, edgeDensity K mu ∂mu) -
                    ∫ x, 2 * degCentered K mu x ∂mu := by
                      rw [integral_sub hdiag hconst]
              _ = (∫ x, K x x ∂mu) - edgeDensity K mu -
                    2 * ∫ x, degCentered K mu x ∂mu := by
                      rw [integral_const, integral_const_mul]
                      simp
    _ = (∫ x, K x x ∂mu) - edgeDensity K mu := by
          change (∫ x, K x x ∂mu) - edgeDensity K mu - 2 *
            mean mu (degCentered K mu) = _
          rw [hmean]
          ring

/-- Trace form of the hub/body split. -/
theorem trace_eq_edgeDensity_add_centeredTrace (hK : GoodK K) :
    trace mu K = edgeDensity K mu + trace mu (centeredKernel K mu) := by
  rw [trace_centeredKernel hK]
  ring

end OddCycleBound.IntermediateRegion
