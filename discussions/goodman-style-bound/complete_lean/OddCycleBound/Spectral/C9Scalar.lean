import OddCycleBound.Kernel

/-!
# C9 low-band analytic arithmetic

This module formalizes the scalar arithmetic used in the paper's
triangle-density/spectral closure for the missing C9 band
`1 / 2 < p <= 1003 / 2000`.

It does not construct the Hilbert-Schmidt spectral decomposition of a graphon.
Instead it proves the exact real-variable estimates that the spectral argument
uses once that analytic layer has supplied the quantities `theta`, `Delta`,
and the negative ninth-power mass bound.
-/

open MeasureTheory

namespace OddCycleBound
namespace Spectral
namespace C9

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
variable {W : Omega -> Omega -> Real}

/-- The rational triangle-density coefficient used in the C9 band proof. -/
lemma theta_coeff_bound :
    (149 : Real) / 100 <= (3 / 2) * ((499 / 500) ^ 2) := by
  norm_num

/-- Exact rational derivative bound for `p^3 - alpha^3` on the C9 band. -/
lemma deriv_F_bound :
    3 * ((1003 : Real) / 2000) ^ 2
        + (1 / 24) * (8 / ((997 : Real) / 2000) - 1 / ((1003 : Real) / 2000))
      <= 27 / 20 := by
  norm_num

/-- Exact rational derivative bound for `Delta = p*q - alpha^2` on the C9 band. -/
lemma deriv_Delta_bound :
    (1 / 18) * (8 / ((997 : Real) / 2000) - 1 / ((1003 : Real) / 2000))
      <= 4 / 5 := by
  norm_num

/-- The endpoint `eps <= 3/2000` is small enough that `sqrt eps <= 1/20`. -/
lemma sqrt_eps_le_one_twentieth {eps : Real}
    (heps1 : eps <= 3 / 2000) :
    Real.sqrt eps <= 1 / 20 := by
  rw [Real.sqrt_le_left (by norm_num : (0 : Real) <= 1 / 20)]
  nlinarith

/-- Final scalar comparison in the C9 low-band proof.

Here `B` stands for `p^3 - alpha_0^3`, `Delta` stands for
`p*q - alpha_0^2`, and `theta` stands for the triangle-density lower bound.
The hypotheses are exactly the rational estimates checked by
`odd_cycle_c9_gap_checker.py`, now in Lean form. -/
lemma scalar_final {eps theta B Delta : Real}
    (heps0 : 0 <= eps) (heps1 : eps <= 3 / 2000)
    (htheta : (149 / 100) * eps <= theta)
    (hB : B <= (27 / 20) * eps)
    (hDelta0 : 0 <= Delta) (hDelta : Delta <= (4 / 5) * eps) :
    B + Real.sqrt Delta ^ 3 <= theta := by
  have hDelta_eps : Delta <= eps := by nlinarith
  have hsqrt_eps : Real.sqrt eps <= 1 / 20 :=
    sqrt_eps_le_one_twentieth heps1
  have hsqrt_Delta : Real.sqrt Delta <= 1 / 20 :=
    (Real.sqrt_le_sqrt hDelta_eps).trans hsqrt_eps
  have hDelta_sqrt : Delta * Real.sqrt Delta <= eps * (1 / 20) := by
    exact mul_le_mul hDelta_eps hsqrt_Delta (Real.sqrt_nonneg Delta) heps0
  have hpow : Real.sqrt Delta ^ 3 = Delta * Real.sqrt Delta := by
    calc
      Real.sqrt Delta ^ 3 = (Real.sqrt Delta ^ 2) * Real.sqrt Delta := by ring
      _ = Delta * Real.sqrt Delta := by rw [Real.sq_sqrt hDelta0]
  nlinarith

private lemma endpoint_F_bracket_nonneg {eps : Real}
    (he0 : 0 <= eps) (he1 : eps <= 3 / 2000) :
    0 <=
      25 - 1570 * eps + 13012 * eps ^ 2 - 50440 * eps ^ 3 +
        87040 * eps ^ 4 - 59200 * eps ^ 5 + 1600 * eps ^ 6 -
          256000 * eps ^ 7 := by
  have he3 : eps ^ 3 <= (3 / 2000 : Real) ^ 2 * eps := by
    nlinarith [mul_nonneg (sq_nonneg eps) he0,
      sq_nonneg ((3 / 2000 : Real) - eps)]
  have he5 : eps ^ 5 <= (3 / 2000 : Real) ^ 4 * eps := by
    nlinarith [mul_nonneg (sq_nonneg (eps ^ 2)) he0,
      sq_nonneg ((3 / 2000 : Real) ^ 2 - eps ^ 2),
      sq_nonneg ((3 / 2000 : Real) - eps)]
  have he7 : eps ^ 7 <= (3 / 2000 : Real) ^ 6 * eps := by
    nlinarith [mul_nonneg (sq_nonneg (eps ^ 3)) he0,
      sq_nonneg ((3 / 2000 : Real) ^ 3 - eps ^ 3),
      sq_nonneg ((3 / 2000 : Real) - eps)]
  nlinarith

/-- Endpoint bound `p^3 - alpha^3 <= 27/20 eps` for the C9 scalar proof,
proved by an exact polynomial comparison rather than by calculus. -/
lemma endpoint_F_bound {eps p q alpha : Real}
    (he0 : 0 <= eps) (he1 : eps <= 3 / 2000)
    (hp : p = 1 / 2 + eps) (hq : q = 1 / 2 - eps)
    (halpha0 : 0 <= alpha)
    (halpha9 : alpha ^ 9 = p * q ^ 8) :
    p ^ 3 - alpha ^ 3 <= (27 / 20) * eps := by
  have hbase0 : 0 <= p ^ 3 - (27 / 20) * eps := by
    rw [hp]
    ring_nf
    nlinarith
  have hpow :
      (p ^ 3 - (27 / 20) * eps) ^ 3 <= (alpha ^ 3) ^ 3 := by
    rw [show (alpha ^ 3) ^ 3 = alpha ^ 9 by ring, halpha9]
    have hb := endpoint_F_bracket_nonneg he0 he1
    rw [hp, hq]
    ring_nf
    nlinarith [mul_nonneg he0 hb]
  have hle := (pow_le_pow_iff_left₀ hbase0 (pow_nonneg halpha0 3)
    (by norm_num : (3 : Nat) ≠ 0)).1 hpow
  linarith

private lemma endpoint_D_bracket_nonneg {eps : Real}
    (he0 : 0 <= eps) (he1 : eps <= 3 / 2000) :
    0 <=
      390625 + 11406250 * eps - 418500000 * eps ^ 2 +
      4713800000 * eps ^ 3 - 25437160000 * eps ^ 4 +
      61253808000 * eps ^ 5 + 15256537600 * eps ^ 6 -
      414828078080 * eps ^ 7 + 762484688384 * eps ^ 8 -
      342687687680 * eps ^ 9 + 244104601600 * eps ^ 10 +
      447756288000 * eps ^ 11 - 6511912960000 * eps ^ 12 +
      8293068800000 * eps ^ 13 - 1714176000000 * eps ^ 14 +
      5509120000000 * eps ^ 15 + 25600000000 * eps ^ 16 +
      256000000000 * eps ^ 17 := by
  have he1' : eps <= 1 := by nlinarith
  have he2 : eps ^ 2 <= (3 / 2000 : Real) ^ 2 := by
    nlinarith [sq_nonneg ((3 / 2000 : Real) - eps)]
  have he3_le1 : eps ^ 3 <= 1 := by
    have h := pow_le_pow_left₀ he0 he1' 3
    simpa using h
  have he4 : eps ^ 4 <= (3 / 2000 : Real) ^ 4 := by
    nlinarith [sq_nonneg ((3 / 2000 : Real) ^ 2 - eps ^ 2)]
  have he7le4 : eps ^ 7 <= eps ^ 4 := by
    have hnon : 0 <= eps ^ 4 * (1 - eps ^ 3) :=
      mul_nonneg (pow_nonneg he0 4) (by linarith)
    nlinarith
  have he9le4 : eps ^ 9 <= eps ^ 4 := by
    have h := pow_le_pow_left₀ he0 he1' 5
    have hnon : 0 <= eps ^ 4 * (1 - eps ^ 5) :=
      mul_nonneg (pow_nonneg he0 4) (by simpa using sub_nonneg.mpr h)
    nlinarith
  have he12le4 : eps ^ 12 <= eps ^ 4 := by
    have h := pow_le_pow_left₀ he0 he1' 8
    have hnon : 0 <= eps ^ 4 * (1 - eps ^ 8) :=
      mul_nonneg (pow_nonneg he0 4) (by simpa using sub_nonneg.mpr h)
    nlinarith
  have he14le4 : eps ^ 14 <= eps ^ 4 := by
    have h := pow_le_pow_left₀ he0 he1' 10
    have hnon : 0 <= eps ^ 4 * (1 - eps ^ 10) :=
      mul_nonneg (pow_nonneg he0 4) (by simpa using sub_nonneg.mpr h)
    nlinarith
  nlinarith

/-- Endpoint bound `pq - alpha^2 <= 4/5 eps` for the C9 scalar proof,
again proved by a polynomial comparison. -/
lemma endpoint_Delta_upper {eps p q alpha : Real}
    (he0 : 0 <= eps) (he1 : eps <= 3 / 2000)
    (hp : p = 1 / 2 + eps) (hq : q = 1 / 2 - eps)
    (halpha0 : 0 <= alpha)
    (halpha9 : alpha ^ 9 = p * q ^ 8) :
    p * q - alpha ^ 2 <= (4 / 5) * eps := by
  have hpq0 : 0 <= p * q - (4 / 5) * eps := by
    rw [hp, hq]
    ring_nf
    nlinarith [he0, he1]
  have hpow :
      (p * q - (4 / 5) * eps) ^ 9 <= (alpha ^ 2) ^ 9 := by
    rw [show (alpha ^ 2) ^ 9 = (alpha ^ 9) ^ 2 by ring, halpha9]
    have hb := endpoint_D_bracket_nonneg he0 he1
    rw [hp, hq]
    ring_nf
    nlinarith [mul_nonneg he0 hb]
  have hle := (pow_le_pow_iff_left₀ hpq0 (pow_nonneg halpha0 2)
    (by norm_num : (9 : Nat) ≠ 0)).1 hpow
  linarith

/-- The endpoint `Delta = pq - alpha^2` is nonnegative for
`alpha^9 = p q^8` in the C9 band. -/
lemma endpoint_Delta_nonneg {eps p q alpha : Real}
    (he0 : 0 <= eps) (he1 : eps <= 3 / 2000)
    (hp : p = 1 / 2 + eps) (hq : q = 1 / 2 - eps)
    (halpha0 : 0 <= alpha)
    (halpha9 : alpha ^ 9 = p * q ^ 8) :
    0 <= p * q - alpha ^ 2 := by
  have hp0 : 0 <= p := by rw [hp]; nlinarith
  have hq0 : 0 <= q := by rw [hq]; nlinarith
  have hqle : q <= p := by rw [hp, hq]; nlinarith
  have hpq0 : 0 <= p * q := mul_nonneg hp0 hq0
  have hqpow : q ^ 7 <= p ^ 7 := pow_le_pow_left₀ hq0 hqle 7
  have hpow_nonneg : 0 <= p ^ 2 * q ^ 9 * (p ^ 7 - q ^ 7) :=
    mul_nonneg (mul_nonneg (sq_nonneg p) (pow_nonneg hq0 9)) (by linarith)
  have hpow :
      (alpha ^ 2) ^ 9 <= (p * q) ^ 9 := by
    rw [show (alpha ^ 2) ^ 9 = (alpha ^ 9) ^ 2 by ring, halpha9]
    nlinarith
  have hle := (pow_le_pow_iff_left₀ (pow_nonneg halpha0 2) hpq0
    (by norm_num : (9 : Nat) ≠ 0)).1 hpow
  linarith

/-- The full one-variable endpoint estimate at `ell = p` used by the C9
low-band scalar proof. -/
lemma endpoint_scalar_bound {eps p q alpha : Real}
    (he0 : 0 <= eps) (he1 : eps <= 3 / 2000)
    (hp : p = 1 / 2 + eps) (hq : q = 1 / 2 - eps)
    (halpha0 : 0 <= alpha)
    (halpha9 : alpha ^ 9 = p * q ^ 8) :
    p ^ 3 - alpha ^ 3 +
        Real.sqrt (p * q - alpha ^ 2) * (p * q - alpha ^ 2) <=
      (149 / 100) * eps := by
  have hF := endpoint_F_bound he0 he1 hp hq halpha0 halpha9
  have hD := endpoint_Delta_upper he0 he1 hp hq halpha0 halpha9
  have hD0 := endpoint_Delta_nonneg he0 he1 hp hq halpha0 halpha9
  have hpow :
      Real.sqrt (p * q - alpha ^ 2) * (p * q - alpha ^ 2) =
        Real.sqrt (p * q - alpha ^ 2) ^ 3 := by
    calc
      Real.sqrt (p * q - alpha ^ 2) * (p * q - alpha ^ 2)
          = Real.sqrt (p * q - alpha ^ 2) *
              Real.sqrt (p * q - alpha ^ 2) ^ 2 := by
            rw [Real.sq_sqrt hD0]
      _ = Real.sqrt (p * q - alpha ^ 2) ^ 3 := by ring
  rw [hpow]
  exact scalar_final he0 he1 (by linarith) hF hD0 hD

private lemma sqrt_mul_self_mono {x y : Real}
    (hx0 : 0 <= x) (hxy : x <= y) :
    Real.sqrt x * x <= Real.sqrt y * y := by
  have hy0 : 0 <= y := hx0.trans hxy
  exact mul_le_mul (Real.sqrt_le_sqrt hxy) hxy hx0 (Real.sqrt_nonneg y)

private lemma cube_increment_strict_mono
    {d b x y : Real}
    (hd0 : 0 <= d) (hdb : d <= b) (hy0 : 0 <= y) (hyx : y < x) :
    (d + y) ^ 3 - d ^ 3 < (b + x) ^ 3 - b ^ 3 := by
  have hx0 : 0 <= x := by linarith
  have hb0 : 0 <= b := hd0.trans hdb
  have hbase :
      (d + y) ^ 3 - d ^ 3 <= (b + y) ^ 3 - b ^ 3 := by
    have hbd : 0 <= b - d := by linarith
    have hsum : 0 <= b + d + y := by linarith
    have hfactor : 0 <= 3 * y * (b - d) * (b + d + y) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hy0) hbd) hsum
    nlinarith
  have hstep :
      (b + y) ^ 3 - b ^ 3 < (b + x) ^ 3 - b ^ 3 := by
    have hsum0 : 0 <= b + y := by linarith
    have hsumlt : b + y < b + x := by linarith
    have hpow := pow_lt_pow_left₀ hsumlt hsum0 (by norm_num : (3 : Nat) ≠ 0)
    nlinarith
  exact lt_of_le_of_lt hbase hstep

private lemma cube_increment_le_of_cube_increment_eq
    {D B C A : Real}
    (hD0 : 0 <= D) (hDB : D <= B) (_hBA : B <= A) (hDC : D <= C)
    (heq : A ^ 3 - B ^ 3 = C ^ 3 - D ^ 3) :
    A - B <= C - D := by
  by_contra hnot
  have hyx : C - D < A - B := by linarith
  have hstrict := cube_increment_strict_mono
    (d := D) (b := B) (x := A - B) (y := C - D)
    hD0 hDB (by linarith) hyx
  have hA : B + (A - B) = A := by ring
  have hC : D + (C - D) = C := by ring
  rw [hA, hC] at hstrict
  linarith

private lemma cubic_increment_bound
    {alpha0 alpha p ell : Real}
    (ha00 : 0 <= alpha0) (ha0p : alpha0 <= p)
    (hpell : p <= ell) (ha0a : alpha0 <= alpha)
    (h9 : alpha ^ 9 - alpha0 ^ 9 = ell ^ 9 - p ^ 9) :
    ell ^ 3 - p ^ 3 <= alpha ^ 3 - alpha0 ^ 3 := by
  have hD0 : 0 <= alpha0 ^ 3 := pow_nonneg ha00 3
  have hDB : alpha0 ^ 3 <= p ^ 3 := pow_le_pow_left₀ ha00 ha0p 3
  have hBA : p ^ 3 <= ell ^ 3 := by
    exact pow_le_pow_left₀ (ha00.trans ha0p) hpell 3
  have hDC : alpha0 ^ 3 <= alpha ^ 3 := pow_le_pow_left₀ ha00 ha0a 3
  have heq : (ell ^ 3) ^ 3 - (p ^ 3) ^ 3 =
      (alpha ^ 3) ^ 3 - (alpha0 ^ 3) ^ 3 := by
    nlinarith
  have h := cube_increment_le_of_cube_increment_eq hD0 hDB hBA hDC heq
  nlinarith

/-- Algebraic replacement for the paper's derivative-based reduction from
`ell` to the endpoint `ell = p`. -/
lemma ell_reduction_bound
    {p q ell alpha0 alpha : Real}
    (hp0 : 0 <= p) (ha00 : 0 <= alpha0) (ha0p : alpha0 <= p)
    (hpell : p <= ell)
    (ha09 : alpha0 ^ 9 = p * q ^ 8)
    (ha9 : alpha ^ 9 = ell ^ 9 - p ^ 9 + p * q ^ 8)
    (hDelta : 0 <= p - ell ^ 2 - alpha ^ 2) :
    ell ^ 3 - alpha ^ 3 +
        Real.sqrt (p - ell ^ 2 - alpha ^ 2) *
          (p - ell ^ 2 - alpha ^ 2) <=
      p ^ 3 - alpha0 ^ 3 +
        Real.sqrt (p - p ^ 2 - alpha0 ^ 2) *
          (p - p ^ 2 - alpha0 ^ 2) := by
  have ha0a : alpha0 <= alpha := by
    have hpow : alpha0 ^ 9 <= alpha ^ 9 := by
      rw [ha09, ha9]
      have hpell9 : p ^ 9 <= ell ^ 9 := pow_le_pow_left₀ hp0 hpell 9
      nlinarith
    exact (show Odd (9 : Nat) by norm_num).pow_le_pow.mp hpow
  have h9diff : alpha ^ 9 - alpha0 ^ 9 = ell ^ 9 - p ^ 9 := by
    rw [ha09, ha9]
    ring
  have hcubic := cubic_increment_bound ha00 ha0p hpell ha0a h9diff
  have hDelta_le :
      p - ell ^ 2 - alpha ^ 2 <= p - p ^ 2 - alpha0 ^ 2 := by
    have hp2 : p ^ 2 <= ell ^ 2 := pow_le_pow_left₀ hp0 hpell 2
    have ha2 : alpha0 ^ 2 <= alpha ^ 2 := pow_le_pow_left₀ ha00 ha0a 2
    nlinarith
  have hsqrt := sqrt_mul_self_mono hDelta hDelta_le
  nlinarith

/-- The cubic capacity
`sqrt (S - z^2) * (S - z^2) - z^3` is strictly decreasing in the
nonnegative root parameter `z`, as long as the remaining square bound is
nonnegative.

This is the scalar step used in the C9 low-band proof after the negative
ninth mass gives a root `z` strictly larger than the threshold `alpha`. -/
lemma cubic_capacity_strict_decreases
    {S alpha z : Real}
    (halpha0 : 0 <= alpha) (_hz0 : 0 <= z)
    (hlt : alpha < z)
    (hbound : 0 <= S - z ^ 2) :
    Real.sqrt (S - z ^ 2) * (S - z ^ 2) - z ^ 3 <
      Real.sqrt (S - alpha ^ 2) * (S - alpha ^ 2) - alpha ^ 3 := by
  have hzsq0 : 0 <= z ^ 2 := sq_nonneg z
  have hsq_lt : alpha ^ 2 < z ^ 2 := by
    exact pow_lt_pow_left₀ hlt halpha0 (by norm_num : (2 : Nat) ≠ 0)
  have hbound_le : S - z ^ 2 <= S - alpha ^ 2 := by
    nlinarith
  have hbound_mono :
      Real.sqrt (S - z ^ 2) * (S - z ^ 2) <=
        Real.sqrt (S - alpha ^ 2) * (S - alpha ^ 2) :=
    sqrt_mul_self_mono hbound hbound_le
  have hcube_lt : alpha ^ 3 < z ^ 3 := by
    exact pow_lt_pow_left₀ hlt halpha0 (by norm_num : (3 : Nat) ≠ 0)
  nlinarith

/-- Same monotonicity step, phrased in the ninth-power comparison that arises
from `alpha^9 < z^9`. -/
lemma cubic_capacity_strict_decreases_of_ninth
    {S alpha z : Real}
    (halpha0 : 0 <= alpha) (hz0 : 0 <= z)
    (hninth : alpha ^ 9 < z ^ 9)
    (hbound : 0 <= S - z ^ 2) :
    Real.sqrt (S - z ^ 2) * (S - z ^ 2) - z ^ 3 <
      Real.sqrt (S - alpha ^ 2) * (S - alpha ^ 2) - alpha ^ 3 := by
  have hlt : alpha < z := by
    exact (show Odd (9 : Nat) by norm_num).pow_lt_pow.mp hninth
  exact cubic_capacity_strict_decreases halpha0 hz0 hlt hbound

/-- The C9 target follows from the spectral negative-mass estimate.

In the paper, `ell` is the principal eigenvalue and `N9` is the ninth-power
mass of the negative non-principal eigenvalues.  The analytic spectral proof
supplies `trace >= ell^9 - N9` and
`N9 <= ell^9 - p^9 + p*q^8`; this lemma performs the final algebraic step in
the graphon notation. -/
theorem cycle_bound_of_negative_mass_bound
    {ell N9 q : Real}
    (hq : q = 1 - edgeDensity W mu)
    (htrace : ell ^ 9 - N9 <= trace mu (compPow mu W 8))
    (hN9 : N9 <= ell ^ 9 - edgeDensity W mu ^ 9 + edgeDensity W mu * q ^ 8) :
    trace mu (compPow mu W 8) >=
      edgeDensity W mu ^ 9 - edgeDensity W mu * (1 - edgeDensity W mu) ^ 8 := by
  rw [hq] at hN9
  nlinarith

end C9
end Spectral
end OddCycleBound
