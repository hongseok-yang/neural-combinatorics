import OddCycleBound.IntermediateRegion.OneSidedPolynomial
import Mathlib.RingTheory.PowerSeries.Log

/-!
# Formal-power-series algebra for the one-sided shift

The intermediate-region shift is a finite coefficient of `-log (1-u)`.  This file
realizes that notation in `PowerSeries Real`, proves that its coefficients are
exactly the already-defined finite convolution sums, and records the formal
factorization separating the scalar hub from the centered body moments.

No analytic convergence or radius-of-convergence argument is used.
-/

open scoped BigOperators PowerSeries

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.DenseRegion
open PowerSeries

/-- The formal series `sum_{r >= 1} X^r / r = -log (1-X)`. -/
noncomputable def formalNegLogBase : PowerSeries Real :=
  PowerSeries.mk fun n => if n = 0 then 0 else (n : Real)⁻¹

/-- Formal `-log (1-u)` for a substitutable series `u`. -/
noncomputable def formalNegLog (u : PowerSeries Real) : PowerSeries Real :=
  formalNegLogBase.subst u

@[simp] theorem coeff_formalNegLogBase (n : Nat) :
    PowerSeries.coeff n formalNegLogBase =
      if n = 0 then 0 else (n : Real)⁻¹ := by
  simp [formalNegLogBase]

@[simp] theorem constantCoeff_formalNegLogBase :
    PowerSeries.constantCoeff formalNegLogBase = 0 := by
  simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- Coefficients of powers of `mk s` are the finite convolutions used by the
the intermediate region polynomial. -/
theorem coeff_mk_pow_eq_momentConv (s : Nat → Real) : ∀ r n : Nat,
    PowerSeries.coeff n ((PowerSeries.mk s) ^ r) = momentConv s r n
  | 0, n => by
      cases n <;> simp [momentConv]
  | r + 1, n => by
      rw [momentConv_succ, pow_succ', PowerSeries.coeff_mul]
      simp_rw [PowerSeries.coeff_mk, coeff_mk_pow_eq_momentConv s r]
      exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => s i * momentConv s r j) n

/-- If the input has zero constant coefficient, its `r`-th convolution power
has no terms below degree `r`. -/
theorem momentConv_eq_zero_of_lt
    {s : Nat → Real} (hs0 : s 0 = 0) : ∀ {r n : Nat}, n < r →
      momentConv s r n = 0
  | 0, n, h => by omega
  | r + 1, n, h => by
      rw [momentConv_succ]
      apply Finset.sum_eq_zero
      intro k hk
      by_cases hk0 : k = 0
      · subst k
        simp [hs0]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hnkr : n - k < r := by
          have hkn : k ≤ n := by
            have := Finset.mem_range.mp hk
            omega
          omega
        rw [momentConv_eq_zero_of_lt hs0 hnkr]
        simp

/-- The coefficient of formal `-log(1-mk s)` is exactly the finite logarithm
coefficient used by `oneSidedLogCoeff`. -/
theorem coeff_formalNegLog_mk
    {s : Nat → Real} (hs0 : s 0 = 0) (m : Nat) :
    PowerSeries.coeff m (formalNegLog (PowerSeries.mk s)) =
      ∑ k ∈ Finset.range m,
        momentConv s (k + 1) m / (k + 1 : Nat) := by
  have hu : PowerSeries.HasSubst (PowerSeries.mk s) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    simpa [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using hs0
  unfold formalNegLog
  rw [PowerSeries.coeff_subst' hu]
  rw [finsum_eq_sum_of_support_subset
    (s := Finset.range (m + 1))]
  · rw [Finset.sum_range_succ']
    simp only [PowerSeries.coeff_mk, coeff_formalNegLogBase,
      if_pos, zero_smul, zero_add, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : k + 1 ≠ 0 := Nat.succ_ne_zero k
    rw [if_neg hk1, coeff_mk_pow_eq_momentConv]
    norm_num [div_eq_mul_inv]
    ring
  · intro d hd
    simp only [Function.mem_support] at hd
    by_contra hmem
    have hmd : m < d := by
      have hnot : ¬ d < m + 1 := by
        intro hdlt
        exact hmem (Finset.mem_range.mpr hdlt)
      omega
    have hzero : PowerSeries.coeff m ((PowerSeries.mk s) ^ d) = 0 := by
      rw [coeff_mk_pow_eq_momentConv,
        momentConv_eq_zero_of_lt hs0 hmd]
    exact hd (by simp [hzero])

/-- The finite definition is the actual coefficient of the formal logarithm. -/
theorem oneSidedLogCoeff_eq_coeff_formalNegLog
    (p : Real) (s : Nat → Real)
    (hs0 : oneSidedUCoeff p s 0 = 0) (m : Nat) :
    oneSidedLogCoeff p s m =
      PowerSeries.coeff m
        (formalNegLog (PowerSeries.mk (oneSidedUCoeff p s))) := by
  unfold oneSidedLogCoeff
  exact (coeff_formalNegLog_mk hs0 m).symm

/-- The derivative of the base formal negative logarithm is the geometric
series with every coefficient equal to one. -/
theorem derivative_formalNegLogBase :
    PowerSeries.derivative Real formalNegLogBase =
      PowerSeries.mk (fun _ : Nat => (1 : Real)) := by
  ext n
  rw [PowerSeries.coeff_derivative]
  simp only [formalNegLogBase, PowerSeries.coeff_mk,
    Nat.succ_ne_zero, if_false]
  have hn : ((n + 1 : Nat) : Real) ≠ 0 := by positivity
  field_simp
  push_cast
  rfl

/-- Substituting a zero-constant series into the geometric series gives the
inverse of `1-u`. -/
theorem subst_geom_eq_inv_one_sub
    {u : PowerSeries Real} (hu0 : PowerSeries.constantCoeff u = 0) :
    (PowerSeries.mk (fun _ : Nat => (1 : Real))).subst u = (1 - u)⁻¹ := by
  have hu : PowerSeries.HasSubst u :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hu0
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp [hu0])).2
  have hsub : (1 - PowerSeries.X : PowerSeries Real).subst u = 1 - u := by
    rw [PowerSeries.subst_sub hu]
    rw [PowerSeries.subst_X hu]
    congr 1
    rw [← PowerSeries.coe_substAlgHom hu]
    exact map_one _
  rw [← hsub, ← PowerSeries.subst_mul hu,
    show PowerSeries.mk (fun _ : Nat => (1 : Real)) =
      PowerSeries.mk (1 : Nat → Real) by rfl,
    PowerSeries.mk_one_mul_one_sub_eq_one Real]
  rw [← PowerSeries.coe_substAlgHom hu]
  exact map_one _

/-- Formal logarithmic derivative: `(-log(1-u))' = u'/(1-u)`. -/
theorem derivative_formalNegLog
    {u : PowerSeries Real} (hu0 : PowerSeries.constantCoeff u = 0) :
    PowerSeries.derivative Real (formalNegLog u) =
      PowerSeries.derivative Real u * (1 - u)⁻¹ := by
  have hu : PowerSeries.HasSubst u :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hu0
  unfold formalNegLog
  rw [PowerSeries.derivative_subst Real hu, derivative_formalNegLogBase,
    subst_geom_eq_inv_one_sub hu0]
  ring

@[simp] theorem constantCoeff_formalNegLog
    {u : PowerSeries Real} (hu0 : PowerSeries.constantCoeff u = 0) :
    PowerSeries.constantCoeff (formalNegLog u) = 0 := by
  unfold formalNegLog
  exact PowerSeries.constantCoeff_subst_eq_zero hu0 _
    constantCoeff_formalNegLogBase

/-- Multiplicativity of the formal logarithm, written in its
`1-(a+b-ab)=(1-a)(1-b)` form. -/
theorem formalNegLog_add_sub_mul
    {a b : PowerSeries Real}
    (ha0 : PowerSeries.constantCoeff a = 0)
    (hb0 : PowerSeries.constantCoeff b = 0) :
    formalNegLog (a + b - a * b) = formalNegLog a + formalNegLog b := by
  have hc0 : PowerSeries.constantCoeff (a + b - a * b) = 0 := by
    simp [ha0, hb0]
  apply PowerSeries.derivative.ext
  · rw [map_add, derivative_formalNegLog hc0,
      derivative_formalNegLog ha0, derivative_formalNegLog hb0,
      map_sub, map_add, Derivation.leibniz]
    simp only [smul_eq_mul]
    have hfactor :
        1 - (a + b - a * b) = (1 - a) * (1 - b) := by ring
    rw [hfactor, PowerSeries.mul_inv_rev]
    have haunit : PowerSeries.constantCoeff (1 - a) ≠ 0 := by simp [ha0]
    have hbunit : PowerSeries.constantCoeff (1 - b) ≠ 0 := by simp [hb0]
    have hA := PowerSeries.mul_inv_cancel (1 - a) haunit
    have hB := PowerSeries.mul_inv_cancel (1 - b) hbunit
    calc
      ((PowerSeries.derivative Real a + PowerSeries.derivative Real b -
          (a * PowerSeries.derivative Real b +
            b * PowerSeries.derivative Real a)) *
          ((1 - b)⁻¹ * (1 - a)⁻¹)) =
          PowerSeries.derivative Real a * (1 - a)⁻¹ *
              ((1 - b) * (1 - b)⁻¹) +
            PowerSeries.derivative Real b * (1 - b)⁻¹ *
              ((1 - a) * (1 - a)⁻¹) := by ring
      _ = PowerSeries.derivative Real a * (1 - a)⁻¹ +
          PowerSeries.derivative Real b * (1 - b)⁻¹ := by
            rw [hA, hB]
            ring
  · simp [ha0, hb0, hc0]

/-- The unsigned return coefficient used after the two parity signs in the
graphon compression moments cancel. -/
noncomputable def unsignedUCoeff
    (p : Real) (s : Nat → Real) (n : Nat) : Real :=
  if 2 ≤ n then
    ∑ j ∈ Finset.range (n - 1), p ^ (n - 2 - j) * s j
  else 0

@[simp] theorem unsignedUCoeff_zero (p : Real) (s : Nat → Real) :
    unsignedUCoeff p s 0 = 0 := by simp [unsignedUCoeff]

@[simp] theorem unsignedUCoeff_one (p : Real) (s : Nat → Real) :
    unsignedUCoeff p s 1 = 0 := by simp [unsignedUCoeff]

/-- Return-coefficient recurrence, equivalently
`(1-pX) u = X^2 S`. -/
theorem unsignedUCoeff_succ_succ
    (p : Real) (s : Nat → Real) (n : Nat) :
    unsignedUCoeff p s (n + 2) =
      p * unsignedUCoeff p s (n + 1) + s n := by
  cases n with
  | zero => simp [unsignedUCoeff]
  | succ n =>
      unfold unsignedUCoeff
      rw [if_pos (by omega : 2 ≤ n + 1 + 2),
        if_pos (by omega : 2 ≤ n + 1 + 1)]
      simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left]
      change (∑ j ∈ Finset.range (n + 2), p ^ (n + 1 - j) * s j) =
        p * (∑ j ∈ Finset.range (n + 1), p ^ (n - j) * s j) + s (n + 1)
      rw [Finset.sum_range_succ]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjle : j ≤ n := by
          exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        rw [show n + 1 - j = (n - j) + 1 by omega, pow_succ]
        ring
      · simp

/-- The return series satisfies the exact Schur-complement factor. -/
theorem one_sub_hub_mul_unsignedUSeries
    (p : Real) (s : Nat → Real) :
    (1 - PowerSeries.C p * PowerSeries.X) *
        PowerSeries.mk (unsignedUCoeff p s) =
      PowerSeries.X ^ 2 * PowerSeries.mk s := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero =>
          simp only [sub_mul, one_mul, mul_assoc, map_sub,
            PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
            PowerSeries.coeff_succ_X_mul]
          simp [unsignedUCoeff, PowerSeries.coeff_X_pow_mul']
      | succ n =>
          simp only [sub_mul, one_mul, mul_assoc, map_sub,
            PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
            PowerSeries.coeff_succ_X_mul]
          rw [unsignedUCoeff_succ_succ]
          have hshift := PowerSeries.coeff_X_pow_mul (PowerSeries.mk s) 2 n
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hshift

/-- Formal factorization of the hub and body return series. -/
theorem one_sub_primitiveSeries_factor
    (p : Real) (s : Nat → Real) :
    1 - (PowerSeries.C p * PowerSeries.X +
        PowerSeries.X ^ 2 * PowerSeries.mk s) =
      (1 - PowerSeries.C p * PowerSeries.X) *
        (1 - PowerSeries.mk (unsignedUCoeff p s)) := by
  rw [mul_sub, mul_one, one_sub_hub_mul_unsignedUSeries]
  ring

/-- The formal negative logarithm splits into the pure hub term and the
one-sided return shift. -/
theorem formalNegLog_primitiveSeries
    (p : Real) (s : Nat → Real) :
    formalNegLog (PowerSeries.C p * PowerSeries.X +
        PowerSeries.X ^ 2 * PowerSeries.mk s) =
      formalNegLog (PowerSeries.C p * PowerSeries.X) +
        formalNegLog (PowerSeries.mk (unsignedUCoeff p s)) := by
  let a : PowerSeries Real := PowerSeries.C p * PowerSeries.X
  let b : PowerSeries Real := PowerSeries.mk (unsignedUCoeff p s)
  have ha0 : PowerSeries.constantCoeff a = 0 := by simp [a]
  have hb0 : PowerSeries.constantCoeff b = 0 := by
    simp [b, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hlog := formalNegLog_add_sub_mul ha0 hb0
  have hreturn : b - a * b = PowerSeries.X ^ 2 * PowerSeries.mk s := by
    dsimp [a, b]
    have hfactor := one_sub_hub_mul_unsignedUSeries p s
    calc
      PowerSeries.mk (unsignedUCoeff p s) -
          (PowerSeries.C p * PowerSeries.X) *
            PowerSeries.mk (unsignedUCoeff p s) =
          (1 - PowerSeries.C p * PowerSeries.X) *
            PowerSeries.mk (unsignedUCoeff p s) := by ring
      _ = _ := hfactor
  calc
    formalNegLog (PowerSeries.C p * PowerSeries.X +
        PowerSeries.X ^ 2 * PowerSeries.mk s) =
        formalNegLog (a + (b - a * b)) := by rw [hreturn]
    _ = formalNegLog (a + b - a * b) := by congr 1 <;> ring
    _ = formalNegLog a + formalNegLog b := hlog

/-- Pure hub coefficient of the formal logarithm. -/
theorem nat_mul_coeff_formalNegLog_hub
    (p : Real) {m : Nat} (hm : 0 < m) :
    (m : Real) * PowerSeries.coeff m
        (formalNegLog (PowerSeries.C p * PowerSeries.X)) = p ^ m := by
  have hsubst :
      formalNegLog (PowerSeries.C p * PowerSeries.X) =
        PowerSeries.rescale p formalNegLogBase := by
    unfold formalNegLog
    rw [PowerSeries.rescale_eq_subst]
    congr 2
    simp [smul_eq_C_mul]
  rw [hsubst, PowerSeries.coeff_rescale, coeff_formalNegLogBase,
    if_neg (Nat.ne_of_gt hm)]
  have hm0 : (m : Real) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  field_simp

end OddCycleBound.IntermediateRegion
