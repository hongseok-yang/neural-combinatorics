import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `K₄` with a two-edge tail: the scalar supporting plane

`notes/k4_two_edge_tail.tex` Lemma 3.2.  Conditioning the three non-tail clique
vertices through the link at `x` and applying Goodman there reduces the whole
row to one inequality between real numbers.  With

```
T_p = p³(2p-1)(3p-2),
L_p(d,a) = T_p + p²(30p²-21p+2)(d-p) + p(20p²-15p+2)(a-d²),
```

the claim is that `L_p` lies under the rooted-`K₄` bound at every feasible
`(d,a) = (d(x), A(x))`.  `L_p` is the unique plane through `(p,p²)` in the
coordinates `(d, a-d²)` whose integral is exactly `T_p`, because `∫d = p` and
`∫A = ∫d²`; the slopes are therefore forced, and so is the tangency.

**The route here differs from the note's.**  The note treats
`G_{p,d}(a) = d(F_p(d,a) - L_p(d,a))` as a cubic in `a`, factors its
discriminant as `-4dp(d-p)²K(p,d)`, and certifies `K > 0` by an explicit
degree-`(7,6)` Bernstein expansion with an 8×7 integer matrix; it then argues
that a real cubic with positive leading coefficient and one real root is
positive to the right of that root.  None of that is formalized here.

Instead, in the coordinate `w = 4a - 2p - d²` (so that `d·F_p = ½·a·w·(w+d²)`),
the cubic in `w` is factored *explicitly*:

```
(11p-4)³·8·(a(2a-p)w - d·L_p) =
    ((11p-4)w - R)²·((11p-4)w + 2R + 2(11p-4)(p+d²))
  + (11p-4)(d-p)²·LIN·w
  + (d-p)²·CON,
```

a `ring` identity, where `R = (11p-4)·r` and `r(p,d)` is the tangent line of the
double root at `d = p`.  Both remainder coefficients are nonnegative:

* `LIN = ((11p-4)d + 23p²-22p+4)² + (1658p⁴-1850p³+647p²-60p-4)`, a square plus
  a quartic in `p` alone;
* `CON = A d² + B d + C` with `A ≤ 0`, so the feasibility `d² ≤ 4d-2p` gives
  `CON ≥ (4A+B)d + C - 2Ap`, and then `d ≥ p/2` with `4A+B ≥ 0` gives
  `CON ≥ Bp/2 + C`, a polynomial in `p` alone.

Every one-variable fact left over has *all coefficients nonnegative* after the
substitution `p = 2/3 + u`, so each is a one-line `nlinarith`.  The cubic-root
theory and the Bernstein matrix are both replaced by that single factorization.
-/

namespace Taeyoung.Methods.K4Tail

/-! ### The target and the supporting plane -/

/-- `T_p = p³(2p-1)(3p-2)`, the catalogue target of `K₄` with a two-edge tail. -/
noncomputable def targetT (p : ℝ) : ℝ := p ^ 3 * (2 * p - 1) * (3 * p - 2)

/-- `L_p(d,a)`, the supporting plane in the coordinates `(d, a - d²)`. -/
noncomputable def plane (p d a : ℝ) : ℝ :=
  targetT p + p ^ 2 * (30 * p ^ 2 - 21 * p + 2) * (d - p) +
    p * (20 * p ^ 2 - 15 * p + 2) * (a - d ^ 2)

/-- The switching-point quadratic: `-8d·L_p(d,a₀) = 2dp·S_p(d)` at
`a₀ = (2p+d²)/4`. -/
noncomputable def Sfun (p d : ℝ) : ℝ :=
  3 * (20 * p ^ 2 - 15 * p + 2) * d ^ 2 - (120 * p ^ 3 - 84 * p ^ 2 + 8 * p) * d +
    (96 * p ^ 4 - 96 * p ^ 3 + 30 * p ^ 2 - 4 * p)

/-! ### One-variable facts on `[2/3, 1]`

Each of these is a polynomial in `p` all of whose coefficients are nonnegative
after `p = 2/3 + u`, so `nlinarith` needs only the powers of `u`. -/

section OneVariable

variable {p : ℝ}

private lemma upow (hp : (2 : ℝ) / 3 ≤ p) (k : ℕ) : 0 ≤ (p - 2 / 3) ^ k :=
  pow_nonneg (by linarith) k

lemma pos_linear (hp : (2 : ℝ) / 3 ≤ p) : 0 < 11 * p - 4 := by linarith

lemma pos_quartic (hp : (2 : ℝ) / 3 ≤ p) :
    0 < 1658 * p ^ 4 - 1850 * p ^ 3 + 647 * p ^ 2 - 60 * p - 4 := by
  nlinarith [upow hp 1, upow hp 2, upow hp 3, upow hp 4]

lemma pos_fourAB (hp : (2 : ℝ) / 3 ≤ p) :
    0 < 75288 * p ^ 6 - 135021 * p ^ 5 + 95412 * p ^ 4 - 34843 * p ^ 3 +
      7282 * p ^ 2 - 900 * p + 56 := by
  nlinarith [upow hp 1, upow hp 2, upow hp 3, upow hp 4, upow hp 5, upow hp 6]

lemma pos_BpC (hp : (2 : ℝ) / 3 ≤ p) :
    0 < 35922 * p ^ 6 - 40125 * p ^ 5 - 1878 * p ^ 4 + 19677 * p ^ 3 -
      10122 * p ^ 2 + 2060 * p - 152 := by
  nlinarith [upow hp 1, upow hp 2, upow hp 3, upow hp 4, upow hp 5, upow hp 6]

lemma pos_Sdisc (hp : (2 : ℝ) / 3 ≤ p) :
    0 < 120 * p ^ 3 - 120 * p ^ 2 + 34 * p - 3 := by
  nlinarith [upow hp 1, upow hp 2, upow hp 3]

lemma pos_Slead (hp : (2 : ℝ) / 3 ≤ p) : 0 < 20 * p ^ 2 - 15 * p + 2 := by
  nlinarith [upow hp 1, upow hp 2]

lemma pos_c27 (hp : (2 : ℝ) / 3 ≤ p) : 0 < 27 * p ^ 2 - 14 * p + 2 := by
  nlinarith [upow hp 1, upow hp 2]

lemma pos_twelve (hp : (2 : ℝ) / 3 ≤ p) : 0 < 12 * p - 7 := by linarith

lemma pos_facDisc (hp : (2 : ℝ) / 3 ≤ p) :
    0 < 1152 * p ^ 4 - 940 * p ^ 3 + 207 * p ^ 2 + 4 * p - 4 := by
  nlinarith [upow hp 1, upow hp 2, upow hp 3, upow hp 4]

end OneVariable

/-! ### The switching quadratic is nonnegative -/

theorem Sfun_nonneg {p : ℝ} (hp : (2 : ℝ) / 3 ≤ p) (d : ℝ) : 0 ≤ Sfun p d := by
  have hlead := pos_Slead hp
  have hdisc := pos_Sdisc hp
  have hppos : (0 : ℝ) < p := by linarith
  have hkey : 12 * (20 * p ^ 2 - 15 * p + 2) * Sfun p d =
      (6 * (20 * p ^ 2 - 15 * p + 2) * d - (120 * p ^ 3 - 84 * p ^ 2 + 8 * p)) ^ 2 +
        8 * p * (3 * p - 2) ^ 2 * (120 * p ^ 3 - 120 * p ^ 2 + 34 * p - 3) := by
    simp only [Sfun]
    ring
  nlinarith [hkey, sq_nonneg (6 * (20 * p ^ 2 - 15 * p + 2) * d -
    (120 * p ^ 3 - 84 * p ^ 2 + 8 * p)),
    mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 8 * p) (sq_nonneg (3 * p - 2)))
      hdisc.le, hlead]

/-! ### The inactive case: below the switching point the plane is nonpositive -/

theorem plane_nonpos {p d a : ℝ} (hp : (2 : ℝ) / 3 ≤ p)
    (hw : 4 * a - 2 * p - d ^ 2 ≤ 0) : plane p d a ≤ 0 := by
  have hppos : (0 : ℝ) < p := by linarith
  have hgam : 0 < p * (20 * p ^ 2 - 15 * p + 2) :=
    mul_pos hppos (pos_Slead hp)
  have hsplit : plane p d a =
      -(p * Sfun p d) / 4 +
        p * (20 * p ^ 2 - 15 * p + 2) * ((4 * a - 2 * p - d ^ 2) / 4) := by
    simp only [plane, targetT, Sfun]
    ring
  have h1 : p * (20 * p ^ 2 - 15 * p + 2) * ((4 * a - 2 * p - d ^ 2) / 4) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hgam.le (by linarith)
  have h2 : -(p * Sfun p d) / 4 ≤ 0 := by
    have := Sfun_nonneg hp d
    nlinarith [hppos]
  rw [hsplit]
  linarith

/-! ### The active case -/

set_option maxHeartbeats 1000000 in
theorem plane_le_active {p d a : ℝ} (hp : (2 : ℝ) / 3 ≤ p) (hp1 : p ≤ 1)
    (hd0 : 0 ≤ d) (had : a ≤ d) (hw : 0 ≤ 4 * a - 2 * p - d ^ 2) :
    d * plane p d a ≤ a * (2 * a - p) * (4 * a - 2 * p - d ^ 2) := by
  have hM : 0 < 11 * p - 4 := pos_linear hp
  have hppos : (0 : ℝ) < p := by linarith
  -- feasibility gives `d ≥ p/2` and `d² ≤ 4d - 2p`
  have hdd : 0 ≤ 4 * d - 2 * p - d ^ 2 := by nlinarith [hw, had]
  have hdp : p / 2 ≤ d := by nlinarith [hdd, sq_nonneg d]
  -- the two remainder coefficients
  have hLIN : 0 ≤ ((11 * p - 4) * d + 23 * p ^ 2 - 22 * p + 4) ^ 2 +
      (1658 * p ^ 4 - 1850 * p ^ 3 + 647 * p ^ 2 - 60 * p - 4) := by
    have := pos_quartic hp
    positivity
  have hA : -2 * (11 * p - 4) * (6 * p ^ 2 - 9 * p + 2) ^ 2 ≤ 0 := by
    nlinarith [hM, sq_nonneg (6 * p ^ 2 - 9 * p + 2)]
  have hCON : 0 ≤ -2 * (11 * p - 4) * (6 * p ^ 2 - 9 * p + 2) ^ 2 * d ^ 2 +
      2 * (75288 * p ^ 6 - 133437 * p ^ 5 + 90084 * p ^ 4 - 28495 * p ^ 3 +
        4018 * p ^ 2 - 148 * p - 8) * d -
      2 * p * (27 * p ^ 2 - 25 * p + 6) ^ 2 * (27 * p ^ 2 - 14 * p + 2) := by
    have hstep1 : 0 ≤ -(-2 * (11 * p - 4) * (6 * p ^ 2 - 9 * p + 2) ^ 2) *
        (4 * d - 2 * p - d ^ 2) :=
      mul_nonneg (by linarith) hdd
    have hstep2 : 0 ≤ 2 * (75288 * p ^ 6 - 135021 * p ^ 5 + 95412 * p ^ 4 -
        34843 * p ^ 3 + 7282 * p ^ 2 - 900 * p + 56) * (d - p / 2) :=
      mul_nonneg (by linarith [pos_fourAB hp]) (by linarith)
    have hstep3 : 0 ≤ p * (35922 * p ^ 6 - 40125 * p ^ 5 - 1878 * p ^ 4 +
        19677 * p ^ 3 - 10122 * p ^ 2 + 2060 * p - 152) :=
      mul_nonneg hppos.le (pos_BpC hp).le
    nlinarith [hstep1, hstep2, hstep3]
  -- the cubic factor stays nonnegative
  have hfac : 0 ≤ (11 * p - 4) * (4 * a - 2 * p - d ^ 2) +
      2 * (6 * d * p ^ 2 - 9 * d * p + 2 * d + 27 * p ^ 3 - 25 * p ^ 2 + 6 * p) +
      2 * (11 * p - 4) * (p + d ^ 2) := by
    have hbase : 0 < 11 * d ^ 2 * p - 4 * d ^ 2 + 6 * d * p ^ 2 - 9 * d * p +
        2 * d + 27 * p ^ 3 - 14 * p ^ 2 + 2 * p := by
      have hid : 4 * (11 * p - 4) *
          (11 * d ^ 2 * p - 4 * d ^ 2 + 6 * d * p ^ 2 - 9 * d * p + 2 * d +
            27 * p ^ 3 - 14 * p ^ 2 + 2 * p) =
          (2 * (11 * p - 4) * d + (6 * p ^ 2 - 9 * p + 2)) ^ 2 +
            (1152 * p ^ 4 - 940 * p ^ 3 + 207 * p ^ 2 + 4 * p - 4) := by ring
      nlinarith [hid, sq_nonneg (2 * (11 * p - 4) * d + (6 * p ^ 2 - 9 * p + 2)),
        pos_facDisc hp, hM]
    nlinarith [mul_nonneg hM.le hw, hbase]
  -- the ring identity
  have key : (11 * p - 4) ^ 3 * 8 *
      (a * (2 * a - p) * (4 * a - 2 * p - d ^ 2) - d * plane p d a) =
      ((11 * p - 4) * (4 * a - 2 * p - d ^ 2) -
          (6 * d * p ^ 2 - 9 * d * p + 2 * d + 27 * p ^ 3 - 25 * p ^ 2 + 6 * p)) ^ 2 *
        ((11 * p - 4) * (4 * a - 2 * p - d ^ 2) +
          2 * (6 * d * p ^ 2 - 9 * d * p + 2 * d + 27 * p ^ 3 - 25 * p ^ 2 + 6 * p) +
          2 * (11 * p - 4) * (p + d ^ 2)) +
      (11 * p - 4) * (d - p) ^ 2 *
        (((11 * p - 4) * d + 23 * p ^ 2 - 22 * p + 4) ^ 2 +
          (1658 * p ^ 4 - 1850 * p ^ 3 + 647 * p ^ 2 - 60 * p - 4)) *
        (4 * a - 2 * p - d ^ 2) +
      (d - p) ^ 2 *
        (-2 * (11 * p - 4) * (6 * p ^ 2 - 9 * p + 2) ^ 2 * d ^ 2 +
          2 * (75288 * p ^ 6 - 133437 * p ^ 5 + 90084 * p ^ 4 - 28495 * p ^ 3 +
            4018 * p ^ 2 - 148 * p - 8) * d -
          2 * p * (27 * p ^ 2 - 25 * p + 6) ^ 2 * (27 * p ^ 2 - 14 * p + 2)) := by
    simp only [plane, targetT]
    ring
  have hrhs : 0 ≤ (11 * p - 4) ^ 3 * 8 *
      (a * (2 * a - p) * (4 * a - 2 * p - d ^ 2) - d * plane p d a) := by
    rw [key]
    have t1 : 0 ≤ ((11 * p - 4) * (4 * a - 2 * p - d ^ 2) -
        (6 * d * p ^ 2 - 9 * d * p + 2 * d + 27 * p ^ 3 - 25 * p ^ 2 + 6 * p)) ^ 2 *
        ((11 * p - 4) * (4 * a - 2 * p - d ^ 2) +
          2 * (6 * d * p ^ 2 - 9 * d * p + 2 * d + 27 * p ^ 3 - 25 * p ^ 2 + 6 * p) +
          2 * (11 * p - 4) * (p + d ^ 2)) := mul_nonneg (sq_nonneg _) hfac
    have t2 : 0 ≤ (11 * p - 4) * (d - p) ^ 2 *
        (((11 * p - 4) * d + 23 * p ^ 2 - 22 * p + 4) ^ 2 +
          (1658 * p ^ 4 - 1850 * p ^ 3 + 647 * p ^ 2 - 60 * p - 4)) *
        (4 * a - 2 * p - d ^ 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg hM.le (sq_nonneg _)) hLIN) hw
    have t3 : 0 ≤ (d - p) ^ 2 *
        (-2 * (11 * p - 4) * (6 * p ^ 2 - 9 * p + 2) ^ 2 * d ^ 2 +
          2 * (75288 * p ^ 6 - 133437 * p ^ 5 + 90084 * p ^ 4 - 28495 * p ^ 3 +
            4018 * p ^ 2 - 148 * p - 8) * d -
          2 * p * (27 * p ^ 2 - 25 * p + 6) ^ 2 * (27 * p ^ 2 - 14 * p + 2)) :=
      mul_nonneg (sq_nonneg _) hCON
    linarith
  have hpos : 0 < (11 * p - 4) ^ 3 * 8 := by positivity
  rcases le_total 0
    (a * (2 * a - p) * (4 * a - 2 * p - d ^ 2) - d * plane p d a) with h | h
  · linarith
  · nlinarith [hrhs, hpos]

/-! ### The two cases combined -/

/-- **The scalar supporting plane.**  `u = (2a-p)_+` and `v = (2u-d²)_+` are the
truncations produced by Goodman in the link; `a·u·v` is `d` times the rooted
`K₄` lower bound, and it dominates `d·L_p(d,a)` on the whole feasible region. -/
theorem plane_le_trunc {p d a : ℝ} (hp : (2 : ℝ) / 3 ≤ p) (hp1 : p ≤ 1)
    (hd0 : 0 ≤ d) (ha0 : 0 ≤ a) (had : a ≤ d) :
    d * plane p d a ≤
      a * max (2 * a - p) 0 * max (2 * max (2 * a - p) 0 - d ^ 2) 0 := by
  rcases le_total (2 * a - p) 0 with hu | hu
  · -- `u = 0`
    rw [max_eq_right hu]
    simp only [mul_zero, zero_mul]
    have : plane p d a ≤ 0 := plane_nonpos hp (by nlinarith [sq_nonneg d])
    exact mul_nonpos_of_nonneg_of_nonpos hd0 this
  · rw [max_eq_left hu]
    rcases le_total (2 * (2 * a - p) - d ^ 2) 0 with hv | hv
    · -- `v = 0`
      rw [max_eq_right hv]
      simp only [mul_zero]
      have : plane p d a ≤ 0 := plane_nonpos hp (by linarith)
      exact mul_nonpos_of_nonneg_of_nonpos hd0 this
    · rw [max_eq_left hv]
      have := plane_le_active hp hp1 hd0 had (by linarith)
      calc d * plane p d a
          ≤ a * (2 * a - p) * (4 * a - 2 * p - d ^ 2) := this
        _ = a * (2 * a - p) * (2 * (2 * a - p) - d ^ 2) := by ring

end Taeyoung.Methods.K4Tail
