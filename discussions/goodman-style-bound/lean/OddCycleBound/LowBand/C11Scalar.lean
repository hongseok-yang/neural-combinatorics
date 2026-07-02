import OddCycleBound.Kernel

/-!
# C11 low-band scalar arithmetic

This file contains the real-variable part of the `C11` near-bipartite
triangle/spectral argument.  It does not construct the spectral decomposition;
it proves the scalar comparison consumed once the analytic input has produced
the endpoint estimates for the principal root and the negative eleventh-power
mass bound.
-/

open MeasureTheory

namespace OddCycleBound
namespace LowBand
namespace C11

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
variable {W : Omega -> Omega -> Real}

/-- The final scalar comparison for the C11 low-band proof.

Here `B` abbreviates `p^3 - alpha_0^3`, `Delta` abbreviates
`p*q - alpha_0^2`, and `theta` is the Razborov/Reiher triangle-density lower
bound.  The two endpoint estimates are the rational bounds checked in
`odd_cycle_c11_checker.py`.
-/
lemma scalar_final {eps theta B Delta : Real}
    (heps0 : 0 <= eps)
    (htheta :
      (3 / 2) * ((64 / 65) ^ 2) * (eps + (3 / 2) * eps ^ 2) <= theta)
    (hB : B <= (139 / 100) * eps)
    (hDelta0 : 0 <= Delta)
    (hDelta : Delta <= (9 / 11) * eps) :
    B + Real.sqrt Delta * Delta <= theta := by
  let t := Real.sqrt eps
  let a : Real := (3 / 2) * ((64 / 65) ^ 2)
  let b : Real := (90 / 121)
  have ht0 : 0 <= t := Real.sqrt_nonneg eps
  have ht2 : t ^ 2 = eps := by
    dsimp [t]
    exact Real.sq_sqrt heps0
  have hsqrtDelta : Real.sqrt Delta <= (10 / 11) * t := by
    have hright0 : 0 <= (10 / 11) * t := by
      exact mul_nonneg (by norm_num) ht0
    rw [Real.sqrt_le_left hright0]
    calc
      Delta <= (9 / 11) * eps := hDelta
      _ <= ((10 / 11) * t) ^ 2 := by
        rw [mul_pow, ht2]
        nlinarith [heps0]
  have hDelta' : Delta <= (9 / 11) * eps := hDelta
  have hrootTerm :
      Real.sqrt Delta * Delta <= b * t * eps := by
    calc
      Real.sqrt Delta * Delta <= ((10 / 11) * t) * ((9 / 11) * eps) := by
        exact mul_le_mul hsqrtDelta hDelta' hDelta0
          (mul_nonneg (by norm_num) ht0)
      _ = b * t * eps := by
        dsimp [b]
        ring
  have hyoung : b * t <= (3 * a / 2) * t ^ 2 + b ^ 2 / (6 * a) := by
    have hsq : 0 <= (3 * a * t - b) ^ 2 := sq_nonneg _
    have ha : 0 < a := by
      dsimp [a]
      norm_num
    have hden : 0 < 6 * a := by nlinarith
    have hmul :
        (6 * a) * (b * t) <=
          (6 * a) * ((3 * a / 2) * t ^ 2 + b ^ 2 / (6 * a)) := by
      field_simp [ne_of_gt hden]
      nlinarith [hsq]
    nlinarith [hmul, hden]
  have hmargin : (139 / 100) + b ^ 2 / (6 * a) <= a := by
    dsimp [a, b]
    norm_num
  have hquad :
      (139 / 100) * eps + b * t * eps <=
        a * (eps + (3 / 2) * eps ^ 2) := by
    have hyoung_mul := mul_le_mul_of_nonneg_right hyoung heps0
    rw [ht2] at hyoung_mul
    nlinarith [hmargin]
  nlinarith

/-- The C11 target follows from the spectral negative-mass estimate.

In the paper, `ell` is the principal eigenvalue and `N11` is the eleventh-power
mass of the negative non-principal eigenvalues.  The analytic spectral proof
supplies `trace >= ell^11 - N11` and
`N11 <= ell^11 - p^11 + p*q^10`; this lemma performs the final graphon-level
algebraic step.
-/
theorem cycle_bound_of_negative_mass_bound
    {ell N11 q : Real}
    (hq : q = 1 - edgeDensity W mu)
    (htrace : ell ^ 11 - N11 <= trace mu (compPow mu W 10))
    (hN11 :
      N11 <= ell ^ 11 - edgeDensity W mu ^ 11 +
        edgeDensity W mu * q ^ 10) :
    trace mu (compPow mu W 10) >=
      edgeDensity W mu ^ 11 - edgeDensity W mu * (1 - edgeDensity W mu) ^ 10 := by
  rw [hq] at hN11
  nlinarith

end C11
end LowBand
end OddCycleBound
