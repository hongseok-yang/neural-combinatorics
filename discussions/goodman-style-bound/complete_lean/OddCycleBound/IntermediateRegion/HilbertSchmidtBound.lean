import OddCycleBound.IntermediateRegion.CenteredKernel

/-!
# The centered Hilbert--Schmidt bound

This file proves the analytic identity behind the intermediate-region block decomposition.
For a graphon `W`, put `q = edgeDensity W mu`, `g = degree W mu - q`, and let
`K` be the kernel of `P T_W P`.  Then

`||K||_HS^2 + 2 ||g||_2^2 + q^2 = ||W||_HS^2`.

The pointwise bound `0 <= W <= 1` then gives the sharp bound

`||K||_HS^2 + 2 ||g||_2^2 <= q * (1 - q)`.
-/

open MeasureTheory

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.DenseRegion
open OddCycleBound.Spectral.L2Kernel

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega -> Omega -> Real}

private lemma integral_mul_self_sub
    {f g : Omega -> Real} (hf : Good f) (hg : Good g) :
    (∫ x, (f x - g x) * (f x - g x) ∂mu) =
      (∫ x, f x * f x ∂mu) + (∫ x, g x * g x ∂mu) -
        2 * (∫ x, f x * g x ∂mu) := by
  have hff : Integrable (fun x => f x * f x) mu := (hf.mul hf).integrable
  have hgg : Integrable (fun x => g x * g x) mu := (hg.mul hg).integrable
  have hfg : Integrable (fun x => f x * g x) mu := (hf.mul hg).integrable
  calc
    (∫ x, (f x - g x) * (f x - g x) ∂mu) =
        ∫ x, f x * f x + g x * g x - 2 * (f x * g x) ∂mu := by
      refine integral_congr_ae (ae_of_all _ fun x => by ring)
    _ = (∫ x, f x * f x + g x * g x ∂mu) -
          ∫ x, 2 * (f x * g x) ∂mu :=
      integral_sub (hff.add hgg) (hfg.const_mul 2)
    _ = ((∫ x, f x * f x ∂mu) + (∫ x, g x * g x ∂mu)) -
          ∫ x, 2 * (f x * g x) ∂mu := by
      rw [integral_add hff hgg]
    _ = _ := by rw [integral_const_mul]

private lemma centeredVariance_eq_degreeSquare_sub
    (hW : IsGraphon W mu) :
    (∫ x, degCentered W mu x * degCentered W mu x ∂mu) =
      (∫ x, degree W mu x * degree W mu x ∂mu) -
        edgeDensity W mu ^ 2 := by
  have h := integral_mul_self_sub (mu := mu) (good_degree hW)
    (DenseRegion.good_const (Omega := Omega) (edgeDensity W mu))
  have hdegree : (∫ x, degree W mu x ∂mu) = edgeDensity W mu := by
    rfl
  have hcross :
      (∫ x, degree W mu x * edgeDensity W mu ∂mu) =
        edgeDensity W mu ^ 2 := by
    rw [integral_mul_const, hdegree]
    ring
  have hconst :
      (∫ _x : Omega, edgeDensity W mu * edgeDensity W mu ∂mu) =
        edgeDensity W mu ^ 2 := by simp [pow_two]
  rw [hcross, hconst] at h
  have halg :
      (∫ x, degree W mu x * degree W mu x ∂mu) +
          edgeDensity W mu ^ 2 - 2 * edgeDensity W mu ^ 2 =
        (∫ x, degree W mu x * degree W mu x ∂mu) -
          edgeDensity W mu ^ 2 := by ring
  rw [halg] at h
  simpa only [degCentered] using h

private lemma centeredKernel_row_square
    (hW : IsGraphon W mu) (x : Omega) :
    (∫ y, centeredKernel W mu x y * centeredKernel W mu x y ∂mu) =
      (∫ y, W x y * W x y ∂mu) - degree W mu x ^ 2 +
        (∫ y, degCentered W mu y * degCentered W mu y ∂mu) -
          2 * kernelOp W mu (degCentered W mu) x := by
  let r : Omega -> Real := fun y => W x y - degree W mu x
  let g : Omega -> Real := degCentered W mu
  have hrow : Good (fun y => W x y) :=
    goodK_row (goodK_of_isGraphon hW) x
  have hr : Good r :=
    good_sub hrow
      (DenseRegion.good_const (Omega := Omega) (degree W mu x))
  have hg : Good g := good_degCentered hW
  have hKpoint : forall y, centeredKernel W mu x y = r y - g y := by
    intro y
    simp only [centeredKernel, r, g, degCentered]
    ring
  have hrSquare :
      (∫ y, r y * r y ∂mu) =
        (∫ y, W x y * W x y ∂mu) - degree W mu x ^ 2 := by
    have hs := integral_mul_self_sub (mu := mu) hrow
      (DenseRegion.good_const (Omega := Omega) (degree W mu x))
    have hdegreeRow : (∫ y, W x y ∂mu) = degree W mu x := by
      rfl
    have hcross : (∫ y, W x y * degree W mu x ∂mu) =
        degree W mu x ^ 2 := by
      rw [integral_mul_const, hdegreeRow]
      ring
    have hconst : (∫ _y : Omega, degree W mu x * degree W mu x ∂mu) =
        degree W mu x ^ 2 := by simp [pow_two]
    rw [hcross, hconst] at hs
    have halg :
        (∫ y, W x y * W x y ∂mu) + degree W mu x ^ 2 -
            2 * degree W mu x ^ 2 =
          (∫ y, W x y * W x y ∂mu) - degree W mu x ^ 2 := by ring
    rw [halg] at hs
    simpa only [r] using hs
  have hmeanG : mean mu g = 0 := by
    simpa only [g, compressIter_zero] using mean_compressIter hW 0
  have hcross :
      (∫ y, r y * g y ∂mu) = kernelOp W mu g x := by
    have hWg : Integrable (fun y => W x y * g y) mu := integrable_Uf hW hg x
    have hxg : Integrable (fun y => degree W mu x * g y) mu :=
      hg.integrable.const_mul _
    calc
      (∫ y, r y * g y ∂mu) =
          ∫ y, W x y * g y - degree W mu x * g y ∂mu := by
        refine integral_congr_ae (ae_of_all _ fun y => by simp only [r]; ring)
      _ = (∫ y, W x y * g y ∂mu) -
          ∫ y, degree W mu x * g y ∂mu := integral_sub hWg hxg
      _ = kernelOp W mu g x - degree W mu x * mean mu g := by
        rw [integral_const_mul]
        rfl
      _ = kernelOp W mu g x := by rw [hmeanG]; ring
  have hs := integral_mul_self_sub (mu := mu) hr hg
  rw [hrSquare, hcross] at hs
  calc
    (∫ y, centeredKernel W mu x y * centeredKernel W mu x y ∂mu) =
        ∫ y, (r y - g y) * (r y - g y) ∂mu := by
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      change centeredKernel W mu x y * centeredKernel W mu x y =
        (r y - g y) * (r y - g y)
      rw [hKpoint y]
    _ = _ := hs

/-- Exact block-energy decomposition for the graphon kernel. -/
theorem centeredKernel_energy_identity (hW : IsGraphon W mu) :
    kernelSqNorm mu (centeredKernel W mu) +
          2 * (∫ x, degCentered W mu x * degCentered W mu x ∂mu) +
          edgeDensity W mu ^ 2 =
      kernelSqNorm mu W := by
  let V : Real := ∫ x, degCentered W mu x * degCentered W mu x ∂mu
  let D : Real := ∫ x, degree W mu x * degree W mu x ∂mu
  let E : Omega -> Real := fun x => ∫ y, W x y * W x y ∂mu
  let H : Omega -> Real := fun x => kernelOp W mu (degCentered W mu) x
  change kernelSqNorm mu (centeredKernel W mu) + 2 * V +
      edgeDensity W mu ^ 2 = kernelSqNorm mu W
  have hE : Integrable E mu := by
    let F : Omega × Omega -> Real :=
      fun z => W z.1 z.2 * W z.1 z.2
    have hF : Integrable F (mu.prod mu) :=
      integrable_uncurry_mul_self_of_goodK (mu := mu) (goodK_of_isGraphon hW)
    simpa only [E, F] using hF.integral_prod_left
  have hD : Integrable (fun x => degree W mu x * degree W mu x) mu :=
    ((good_degree hW).mul (good_degree hW)).integrable
  have hH : Integrable H mu := by
    exact (good_kernelOp hW (good_degCentered hW)).integrable
  have hmeanH : (∫ x, H x ∂mu) = V := by
    change mean mu (kernelOp W mu (degCentered W mu)) = V
    rw [mean_kernelOp_eq hW (good_degCentered hW), pathIter_one hW]
    unfold pairing V
    have hmeanG : mean mu (degCentered W mu) = 0 := by
      simpa only [compressIter_zero] using mean_compressIter hW 0
    calc
      (∫ x, degree W mu x * degCentered W mu x ∂mu) =
          ∫ x, (edgeDensity W mu + degCentered W mu x) *
            degCentered W mu x ∂mu := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        change degree W mu x * degCentered W mu x =
          (edgeDensity W mu + degCentered W mu x) * degCentered W mu x
        rw [degree_eq]
      _ = (∫ x, edgeDensity W mu * degCentered W mu x ∂mu) +
          ∫ x, degCentered W mu x * degCentered W mu x ∂mu := by
        rw [← integral_add
          ((good_degCentered hW).integrable.const_mul _)
          ((good_degCentered hW).mul (good_degCentered hW)).integrable]
        refine integral_congr_ae (ae_of_all _ fun x => by ring)
      _ = _ := by
        have hmeanG' : (∫ x, degCentered W mu x ∂mu) = 0 := hmeanG
        rw [integral_const_mul, hmeanG']
        ring
  have hvar : V = D - edgeDensity W mu ^ 2 := by
    exact centeredVariance_eq_degreeSquare_sub hW
  have hkernel :
      kernelSqNorm mu (centeredKernel W mu) =
        kernelSqNorm mu W - D + V - 2 * V := by
    unfold kernelSqNorm
    have hpoint : forall x,
        (∫ y, centeredKernel W mu x y * centeredKernel W mu x y ∂mu) =
          E x - degree W mu x ^ 2 + V - 2 * H x := by
      intro x
      exact centeredKernel_row_square hW x
    rw [integral_congr_ae (ae_of_all _ hpoint)]
    have hleft : Integrable (fun x => E x - degree W mu x ^ 2 + V) mu := by
      exact (hE.sub (by simpa only [pow_two] using hD)).add (integrable_const V)
    have hEeq : (∫ x, E x ∂mu) = kernelSqNorm mu W := by rfl
    have hDeq : (∫ x, degree W mu x ^ 2 ∂mu) = D := by
      simp only [D, pow_two]
    rw [integral_sub hleft (hH.const_mul 2)]
    have hbase :
        (∫ x, E x - degree W mu x ^ 2 + V ∂mu) =
          kernelSqNorm mu W - D + V := by
      calc
        (∫ x, E x - degree W mu x ^ 2 + V ∂mu) =
            (∫ x, E x - degree W mu x ^ 2 ∂mu) +
              ∫ _x : Omega, V ∂mu :=
          integral_add
            (hE.sub (by simpa only [pow_two] using hD)) (integrable_const V)
        _ = ((∫ x, E x ∂mu) - ∫ x, degree W mu x ^ 2 ∂mu) + V := by
          rw [integral_sub hE (by simpa only [pow_two] using hD),
            integral_const]
          simp
        _ = kernelSqNorm mu W - D + V := by rw [hEeq, hDeq]
    rw [hbase, integral_const_mul, hmeanH]
    change kernelSqNorm mu W - D + V - 2 * V =
      kernelSqNorm mu W - D + V - 2 * V
    rfl
  rw [hkernel, hvar]
  ring

/-- The graphon square integral is bounded by its edge density. -/
theorem kernelSqNorm_le_edgeDensity (hW : IsGraphon W mu) :
    kernelSqNorm mu W <= edgeDensity W mu := by
  have hrowEnergy : Integrable (fun x => ∫ y, W x y * W x y ∂mu) mu := by
    have hF := integrable_uncurry_mul_self_of_goodK
      (mu := mu) (goodK_of_isGraphon hW)
    simpa using hF.integral_prod_left
  have hdegree : Integrable (degree W mu) mu := (good_degree hW).integrable
  unfold kernelSqNorm edgeDensity mean
  refine integral_mono hrowEnergy hdegree ?_
  intro x
  have hrow : Good (fun y => W x y) :=
    goodK_row (goodK_of_isGraphon hW) x
  refine integral_mono (hrow.mul hrow).integrable hrow.integrable ?_
  intro y
  have h0 := hW.nonneg x y
  have h1 := hW.le_one x y
  nlinarith

/-- The sharp Hilbert--Schmidt bound for the centered compression. -/
theorem centeredKernel_hilbertSchmidt_bound (hW : IsGraphon W mu) :
    kernelSqNorm mu (centeredKernel W mu) +
        2 * ‖DenseRegion.centeredDegreeL2 hW‖ ^ 2 <=
      edgeDensity W mu * (1 - edgeDensity W mu) := by
  have hid := centeredKernel_energy_identity hW
  have hsq := kernelSqNorm_le_edgeDensity hW
  unfold DenseRegion.centeredDegreeL2
  rw [norm_goodL2_sq_eq_integral_mul (good_degCentered hW)]
  nlinarith

end OddCycleBound.IntermediateRegion
