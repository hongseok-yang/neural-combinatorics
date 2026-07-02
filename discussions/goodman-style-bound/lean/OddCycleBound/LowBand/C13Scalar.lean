import OddCycleBound.Kernel

/-!
# C13 near-bipartite scalar arithmetic

This file contains the scalar comparison for the rational near-bipartite
`C13` triangle/spectral interval `1 / 2 < p <= 51 / 100`.  The endpoint
estimates themselves are the exact Sturm-certified inequalities recorded in
`c13_near_bipartite_checker.py`; this module proves the final real-variable
step once those estimates are available.
-/

open MeasureTheory

namespace OddCycleBound
namespace LowBand
namespace C13

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
variable {W : Omega -> Omega -> Real}

/-- The final scalar comparison for the C13 rational near-bipartite interval.

Here `B` abbreviates `p^3 - alpha_0^3`, `Delta` abbreviates
`p*q - alpha_0^2`, and `theta` is the Razborov/Reiher triangle-density lower
bound.  The two endpoint estimates are the rational bounds checked in
`c13_near_bipartite_checker.py`.
-/
lemma scalar_final {eps theta B Delta : Real}
    (heps0 : 0 <= eps)
    (htheta :
      (3 / 2) * ((97 / 98) ^ 2) * (eps + (3 / 2) * eps ^ 2) <= theta)
    (hB : B <= (7 / 5) * eps)
    (hDelta0 : 0 <= Delta)
    (hDelta : Delta <= (11 / 13) * eps) :
    B + Real.sqrt Delta * Delta <= theta := by
  let t := Real.sqrt eps
  let a : Real := (3 / 2) * ((97 / 98) ^ 2)
  let b : Real := (132 / 169)
  have ht0 : 0 <= t := Real.sqrt_nonneg eps
  have ht2 : t ^ 2 = eps := by
    dsimp [t]
    exact Real.sq_sqrt heps0
  have hsqrtDelta : Real.sqrt Delta <= (12 / 13) * t := by
    have hright0 : 0 <= (12 / 13) * t := by
      exact mul_nonneg (by norm_num) ht0
    rw [Real.sqrt_le_left hright0]
    calc
      Delta <= (11 / 13) * eps := hDelta
      _ <= ((12 / 13) * t) ^ 2 := by
        rw [mul_pow, ht2]
        nlinarith [heps0]
  have hDelta' : Delta <= (11 / 13) * eps := hDelta
  have hrootTerm :
      Real.sqrt Delta * Delta <= b * t * eps := by
    calc
      Real.sqrt Delta * Delta <= ((12 / 13) * t) * ((11 / 13) * eps) := by
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
  have hmargin : (7 / 5) + b ^ 2 / (6 * a) <= a := by
    dsimp [a, b]
    norm_num
  have hquad :
      (7 / 5) * eps + b * t * eps <=
        a * (eps + (3 / 2) * eps ^ 2) := by
    have hyoung_mul := mul_le_mul_of_nonneg_right hyoung heps0
    rw [ht2] at hyoung_mul
    nlinarith [hmargin]
  nlinarith

/-- The C13 target follows from the spectral negative-mass estimate.

This is the same final algebraic step as in the C9/C11 low-band arguments,
with exponent `13`.
-/
theorem cycle_bound_of_negative_mass_bound
    {ell N13 q : Real}
    (hq : q = 1 - edgeDensity W mu)
    (htrace : ell ^ 13 - N13 <= trace mu (compPow mu W 12))
    (hN13 :
      N13 <= ell ^ 13 - edgeDensity W mu ^ 13 +
        edgeDensity W mu * q ^ 12) :
    trace mu (compPow mu W 12) >=
      edgeDensity W mu ^ 13 - edgeDensity W mu * (1 - edgeDensity W mu) ^ 12 := by
  rw [hq] at hN13
  nlinarith

end C13
end LowBand
end OddCycleBound
