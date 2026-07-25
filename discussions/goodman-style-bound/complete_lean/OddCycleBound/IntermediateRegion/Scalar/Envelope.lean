import OddCycleBound.IntermediateRegion.Scalar.EigenvalueAlgebra
import Mathlib.Topology.Order.Compact

/-!
# Exact Envelope minimum: compactness and dual certificates

The scalar envelope_value is defined as the actual infimum of the corrected Envelope
objective on `[0,1]`.  This file proves attainment and the sound direction of
the dual formula used by every scalar certificate.
-/

open Set

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

theorem continuous_envelopeObjective (xi rho : Real) :
    Continuous (envelopeObjective xi rho) := by
  unfold envelopeObjective
  fun_prop

theorem envelopeObjective_image_nonempty (xi rho : Real) :
    (envelopeObjective xi rho '' Icc (0 : Real) 1).Nonempty := by
  exact ⟨envelopeObjective xi rho 0, ⟨0, by constructor <;> norm_num, rfl⟩⟩

theorem envelopeObjective_nonneg {xi rho v : Real}
    (hrho : 0 ≤ rho) :
    0 ≤ envelopeObjective xi rho v := by
  unfold envelopeObjective
  exact add_nonneg (mul_nonneg hrho (sq_nonneg v)) (le_max_right _ _)

theorem envelopeObjective_image_bddBelow {xi rho : Real}
    (hrho : 0 ≤ rho) :
    BddBelow (envelopeObjective xi rho '' Icc (0 : Real) 1) := by
  refine ⟨0, ?_⟩
  intro y hy
  rcases hy with ⟨v, hv, rfl⟩
  exact envelopeObjective_nonneg hrho

/-- The `sInf` in the definition of `psi` is attained on `[0,1]`. -/
theorem exists_envelope_minimizer (xi rho : Real) :
    ∃ v ∈ Icc (0 : Real) 1,
      psi xi rho = envelopeObjective xi rho v := by
  have hcompact : IsCompact
      (envelopeObjective xi rho '' Icc (0 : Real) 1) :=
    isCompact_Icc.image (continuous_envelopeObjective xi rho)
  have hmem := hcompact.sInf_mem (envelopeObjective_image_nonempty xi rho)
  rcases hmem with ⟨v, hv, hvalue⟩
  refine ⟨v, hv, ?_⟩
  unfold psi
  exact hvalue.symm

theorem psi_le_envelopeObjective {xi rho v : Real}
    (hrho : 0 ≤ rho) (hv : v ∈ Icc (0 : Real) 1) :
    psi xi rho ≤ envelopeObjective xi rho v := by
  unfold psi
  exact csInf_le (envelopeObjective_image_bddBelow hrho) ⟨v, hv, rfl⟩

theorem psi_nonneg {xi rho : Real} (hrho : 0 <= rho) :
    0 <= psi xi rho := by
  rcases exists_envelope_minimizer xi rho with ⟨v, hv, hvalue⟩
  rw [hvalue]
  exact envelopeObjective_nonneg hrho

/-- The positive part dominates every interpolation `lambda*t` with
`lambda ∈ [0,1]`. -/
lemma mul_le_max_zero {lambda t : Real}
    (hlambda : lambda ∈ Icc (0 : Real) 1) :
    lambda * t ≤ max t 0 := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_left ht]
    nlinarith [mul_le_mul_of_nonneg_right hlambda.2 ht]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [max_eq_right ht']
    exact mul_nonpos_of_nonneg_of_nonpos hlambda.1 ht'

/-- Pointwise weak duality for the corrected Envelope objective. -/
theorem envelopeDual_le_envelopeObjective
    {xi rho lambda v : Real}
    (hrho : 0 ≤ rho)
    (hlambda : lambda ∈ Icc (0 : Real) 1) :
    envelopeDual xi rho lambda ≤ envelopeObjective xi rho v := by
  have hmax := mul_le_max_zero
    (t := xi - v + v ^ 2) hlambda
  by_cases ha : rho + lambda = 0
  · have hrho0 : rho = 0 := by nlinarith [hlambda.1]
    have hlambda0 : lambda = 0 := by nlinarith
    rw [hrho0, hlambda0]
    simp [envelopeDual, envelopeObjective, le_max_right]
  · have ha0 : 0 < rho + lambda := by
      have : 0 ≤ rho + lambda := add_nonneg hrho hlambda.1
      exact lt_of_le_of_ne this (Ne.symm ha)
    have hquad :
        -(lambda ^ 2) / (4 * (rho + lambda)) ≤
          (rho + lambda) * v ^ 2 - lambda * v := by
      rw [div_le_iff₀ (by positivity : 0 < 4 * (rho + lambda))]
      nlinarith [sq_nonneg (2 * (rho + lambda) * v - lambda)]
    unfold envelopeDual envelopeObjective
    calc
      lambda * xi - lambda ^ 2 / (4 * (rho + lambda)) ≤
          lambda * xi + ((rho + lambda) * v ^ 2 - lambda * v) := by
            calc
              lambda * xi - lambda ^ 2 / (4 * (rho + lambda)) =
                  lambda * xi + (-(lambda ^ 2) / (4 * (rho + lambda))) := by ring
              _ ≤ _ := by
                simpa [add_comm] using add_le_add_left hquad (lambda * xi)
      _ = rho * v ^ 2 +
          lambda * (xi - v + v ^ 2) := by ring
      _ ≤ rho * v ^ 2 + max (xi - v + v ^ 2) 0 :=
        by simpa [add_comm] using add_le_add_right hmax (rho * v ^ 2)

/-- Sound dual certificate: every `lambda ∈ [0,1]` gives a lower bound on
the true Envelope minimum. -/
theorem envelopeDual_le_psi
    {xi rho lambda : Real}
    (hrho : 0 ≤ rho)
    (hlambda : lambda ∈ Icc (0 : Real) 1) :
    envelopeDual xi rho lambda ≤ psi xi rho := by
  unfold psi
  apply le_csInf (envelopeObjective_image_nonempty xi rho)
  intro y hy
  rcases hy with ⟨v, hv, rfl⟩
  exact envelopeDual_le_envelopeObjective hrho hlambda

/-- The `lambda = 1` envelope witness. -/
theorem psi_ge_dual_one {xi rho : Real} (hrho : 0 ≤ rho) :
    xi - 1 / (4 * (rho + 1)) ≤ psi xi rho := by
  simpa [envelopeDual] using
    (envelopeDual_le_psi (xi := xi) (rho := rho) (lambda := 1) hrho
      (by constructor <;> norm_num))

/-- Exact second branch of the corrected piecewise formula for `psi`. -/
theorem psi_eq_linear_branch
    {xi rho : Real} (hrho : 0 ≤ rho)
    (hxi : xiCritical rho ≤ xi) :
    psi xi rho = xi - 1 / (4 * (rho + 1)) := by
  let vstar : Real := 1 / (2 * (rho + 1))
  have hden : 0 < rho + 1 := by linarith
  have hvstar : vstar ∈ Icc (0 : Real) 1 := by
    constructor
    · dsimp [vstar]
      positivity
    · dsimp [vstar]
      rw [div_le_one (by positivity : 0 < 2 * (rho + 1))]
      linarith
  have hcritical : xiCritical rho = vstar - vstar ^ 2 := by
    unfold xiCritical
    dsimp [vstar]
    field_simp
    ring
  have hactive : 0 ≤ xi - vstar + vstar ^ 2 := by
    linarith [hcritical, hxi]
  have hupper := psi_le_envelopeObjective (xi := xi) (rho := rho) hrho hvstar
  rw [envelopeObjective, max_eq_left hactive] at hupper
  have hvalue :
      rho * vstar ^ 2 + (xi - vstar + vstar ^ 2) =
        xi - 1 / (4 * (rho + 1)) := by
    dsimp [vstar]
    field_simp
    ring
  rw [hvalue] at hupper
  exact le_antisymm hupper (psi_ge_dual_one hrho)

/-- The `lambda = 2*rho*xi` certificate used in the small-eigenvalue branch. -/
theorem psi_ge_dual_two_rho_xi
    {xi rho : Real}
    (hrho : 0 < rho) (hxi : 0 ≤ xi)
    (hlambda : 2 * rho * xi ≤ 1) :
    rho * xi ^ 2 * (1 + 4 * xi) / (1 + 2 * xi) ≤ psi xi rho := by
  have hlambdaMem : 2 * rho * xi ∈ Icc (0 : Real) 1 := by
    exact ⟨mul_nonneg (mul_nonneg (by norm_num) hrho.le) hxi, hlambda⟩
  have hcert := envelopeDual_le_psi
    (xi := xi) (rho := rho) (lambda := 2 * rho * xi) hrho.le hlambdaMem
  have hdenXi : 1 + 2 * xi ≠ 0 := by linarith
  have hdenRho : rho ≠ 0 := ne_of_gt hrho
  have heq :
      envelopeDual xi rho (2 * rho * xi) =
        rho * xi ^ 2 * (1 + 4 * xi) / (1 + 2 * xi) := by
    unfold envelopeDual
    field_simp [hdenXi, hdenRho]
    ring
  rw [heq] at hcert
  exact hcert

lemma vMinus_mem_halfInterval {xi : Real}
    (hxi0 : 0 ≤ xi) (hxi4 : xi ≤ (1 : Real) / 4) :
    vMinus xi ∈ Icc (0 : Real) (1 / 2) := by
  have hrad0 : 0 ≤ 1 - 4 * xi := by linarith
  have hrad1 : 1 - 4 * xi ≤ 1 := by linarith
  have hsqrt_le : Real.sqrt (1 - 4 * xi) ≤ 1 := by
    have := Real.sqrt_le_sqrt hrad1
    simpa using this
  have hsqrt0 := Real.sqrt_nonneg (1 - 4 * xi)
  unfold vMinus
  constructor <;> linarith

lemma vMinus_sub_sq {xi : Real}
    (hxi0 : 0 ≤ xi) (hxi4 : xi ≤ (1 : Real) / 4) :
    vMinus xi - vMinus xi ^ 2 = xi := by
  have hrad0 : 0 ≤ 1 - 4 * xi := by linarith
  have hsqrtSq := Real.sq_sqrt hrad0
  unfold vMinus
  nlinarith

/-- Exact square-root branch of the corrected piecewise formula for `psi`. -/
theorem psi_eq_sqrt_branch
    {xi rho : Real} (hrho : 0 ≤ rho) (hxi0 : 0 ≤ xi)
    (hxi : xi < xiCritical rho) :
    psi xi rho = rho * vMinus xi ^ 2 := by
  have hden : 0 < rho + 1 := by linarith
  have hcritical_le : xiCritical rho ≤ (1 : Real) / 4 := by
    unfold xiCritical
    rw [div_le_iff₀ (by positivity : 0 < 4 * (rho + 1) ^ 2)]
    nlinarith [sq_nonneg rho]
  have hxi4 : xi ≤ (1 : Real) / 4 := by linarith
  have hvm := vMinus_mem_halfInterval hxi0 hxi4
  have hvmEq := vMinus_sub_sq hxi0 hxi4
  let vstar : Real := 1 / (2 * (rho + 1))
  have hvstar0 : 0 ≤ vstar := by
    dsimp [vstar]
    positivity
  have hvstarHalf : vstar ≤ (1 : Real) / 2 := by
    dsimp [vstar]
    rw [div_le_iff₀ (by positivity : 0 < 2 * (rho + 1))]
    linarith
  have hcritical : xiCritical rho = vstar - vstar ^ 2 := by
    unfold xiCritical
    dsimp [vstar]
    field_simp
    ring
  have hvmstar : vMinus xi < vstar := by
    by_contra hnot
    have hle : vstar ≤ vMinus xi := le_of_not_gt hnot
    have hfactor :
        0 ≤ (vMinus xi - vstar) * (1 - vMinus xi - vstar) :=
      mul_nonneg (sub_nonneg.mpr hle) (by linarith [hvm.2, hvstarHalf])
    have hmono : vstar - vstar ^ 2 ≤
        vMinus xi - vMinus xi ^ 2 := by nlinarith
    linarith [hcritical, hvmEq]
  have hpoint : ∀ v ∈ Icc (0 : Real) 1,
      rho * vMinus xi ^ 2 ≤ envelopeObjective xi rho v := by
    intro v hv
    by_cases hvorder : vMinus xi ≤ v
    · have hvSq : vMinus xi ^ 2 ≤ v ^ 2 :=
        pow_le_pow_left₀ hvm.1 hvorder 2
      unfold envelopeObjective
      have hmax0 : 0 ≤ max (xi - v + v ^ 2) 0 := le_max_right _ _
      nlinarith [mul_le_mul_of_nonneg_left hvSq hrho]
    · have hvlt : v < vMinus xi := lt_of_not_ge hvorder
      have htFactor :
          0 ≤ (vMinus xi - v) * (1 - vMinus xi - v) :=
        mul_nonneg (sub_nonneg.mpr hvlt.le) (by linarith [hvm.2, hv.1])
      have ht : 0 ≤ xi - v + v ^ 2 := by
        rw [← hvmEq]
        nlinarith
      have hvmv : vMinus xi + v < 2 * vstar := by linarith
      have hscale := mul_lt_mul_of_pos_left hvmv hden
      have hvstarScale : (rho + 1) * (2 * vstar) = 1 := by
        dsimp [vstar]
        field_simp
      rw [hvstarScale] at hscale
      have hpayFactor :
          0 ≤ (vMinus xi - v) *
            (1 - (rho + 1) * (vMinus xi + v)) :=
        mul_nonneg (sub_nonneg.mpr hvlt.le) (by linarith)
      unfold envelopeObjective
      rw [max_eq_left ht]
      nlinarith [hpayFactor, hvmEq]
  have hupper := psi_le_envelopeObjective (xi := xi) (rho := rho) hrho
    (show vMinus xi ∈ Icc (0 : Real) 1 from ⟨hvm.1, hvm.2.trans (by norm_num)⟩)
  have hzero : xi - vMinus xi + vMinus xi ^ 2 = 0 := by linarith [hvmEq]
  rw [envelopeObjective, hzero, max_self, add_zero] at hupper
  rcases exists_envelope_minimizer xi rho with ⟨v, hv, hpsi⟩
  have hlower := hpoint v hv
  apply le_antisymm hupper
  calc
    rho * vMinus xi ^ 2 ≤ envelopeObjective xi rho v := hlower
    _ = psi xi rho := hpsi.symm

/-- In the intermediate-region parameter range, the dual maximum is attained and pays
exactly `psi`. -/
theorem exists_envelopeDual_eq_psi
    {xi rho : Real} (hrho : 0 < rho) (hxi0 : 0 ≤ xi) :
    ∃ lambda ∈ Icc (0 : Real) 1,
      envelopeDual xi rho lambda = psi xi rho := by
  by_cases hbranch : xiCritical rho ≤ xi
  · refine ⟨1, by constructor <;> norm_num, ?_⟩
    rw [psi_eq_linear_branch hrho.le hbranch]
    unfold envelopeDual
    ring
  · have hxi : xi < xiCritical rho := lt_of_not_ge hbranch
    have hden : 0 < rho + 1 := by linarith
    have hcritical_le : xiCritical rho ≤ (1 : Real) / 4 := by
      unfold xiCritical
      rw [div_le_iff₀ (by positivity : 0 < 4 * (rho + 1) ^ 2)]
      nlinarith [sq_nonneg rho]
    have hxi4 : xi ≤ (1 : Real) / 4 := by linarith
    have hvm := vMinus_mem_halfInterval hxi0 hxi4
    have hvmEq := vMinus_sub_sq hxi0 hxi4
    let vstar : Real := 1 / (2 * (rho + 1))
    have hvstarHalf : vstar ≤ (1 : Real) / 2 := by
      dsimp [vstar]
      rw [div_le_iff₀ (by positivity : 0 < 2 * (rho + 1))]
      linarith
    have hcritical : xiCritical rho = vstar - vstar ^ 2 := by
      unfold xiCritical
      dsimp [vstar]
      field_simp
      ring
    have hvmstar : vMinus xi < vstar := by
      by_contra hnot
      have hle : vstar ≤ vMinus xi := le_of_not_gt hnot
      have hfactor :
          0 ≤ (vMinus xi - vstar) * (1 - vMinus xi - vstar) :=
        mul_nonneg (sub_nonneg.mpr hle) (by linarith [hvm.2, hvstarHalf])
      have hmono : vstar - vstar ^ 2 ≤
          vMinus xi - vMinus xi ^ 2 := by nlinarith
      linarith [hcritical, hvmEq]
    let lambda : Real := 2 * rho * vMinus xi / (1 - 2 * vMinus xi)
    have hdenVm : 0 < 1 - 2 * vMinus xi := by
      have : vMinus xi < (1 : Real) / 2 := hvmstar.trans_le hvstarHalf
      linarith
    have hlambda0 : 0 ≤ lambda := by
      dsimp [lambda]
      exact div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hrho.le) hvm.1) hdenVm.le
    have hlambda1 : lambda ≤ 1 := by
      dsimp [lambda]
      rw [div_le_one hdenVm]
      have hscaled := mul_lt_mul_of_pos_left hvmstar (by positivity : 0 < 2 * (rho + 1))
      have hvstarScaled : 2 * (rho + 1) * vstar = 1 := by
        dsimp [vstar]
        field_simp
      rw [hvstarScaled] at hscaled
      nlinarith
    refine ⟨lambda, ⟨hlambda0, hlambda1⟩, ?_⟩
    rw [psi_eq_sqrt_branch hrho.le hxi0 hxi]
    have hrhoNe : rho ≠ 0 := ne_of_gt hrho
    have hdenVmNe : 1 - 2 * vMinus xi ≠ 0 := ne_of_gt hdenVm
    unfold envelopeDual
    dsimp [lambda]
    field_simp [hrhoNe, hdenVmNe]
    nlinarith [hvmEq]

/-- Exact dual formula for the corrected Envelope envelope_value on its the intermediate region
domain. -/
theorem psi_eq_sSup_envelopeDual
    {xi rho : Real} (hrho : 0 < rho) (hxi0 : 0 ≤ xi) :
    psi xi rho = sSup (envelopeDual xi rho '' Icc (0 : Real) 1) := by
  have hnonempty : (envelopeDual xi rho '' Icc (0 : Real) 1).Nonempty :=
    ⟨envelopeDual xi rho 0, ⟨0, by constructor <;> norm_num, rfl⟩⟩
  have hbdd : BddAbove (envelopeDual xi rho '' Icc (0 : Real) 1) := by
    refine ⟨psi xi rho, ?_⟩
    intro y hy
    rcases hy with ⟨lambda, hlambda, rfl⟩
    exact envelopeDual_le_psi hrho.le hlambda
  obtain ⟨lambda, hlambda, heq⟩ := exists_envelopeDual_eq_psi hrho hxi0
  apply le_antisymm
  · rw [← heq]
    exact le_csSup hbdd ⟨lambda, hlambda, rfl⟩
  · apply csSup_le hnonempty
    intro y hy
    rcases hy with ⟨lambda, hlambda, rfl⟩
    exact envelopeDual_le_psi hrho.le hlambda

end OddCycleBound.IntermediateRegion.Scalar
