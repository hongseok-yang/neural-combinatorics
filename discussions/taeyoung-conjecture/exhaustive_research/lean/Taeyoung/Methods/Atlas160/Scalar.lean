import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Atlas 160: the scalar supporting plane

`notes/atlas160_k4_paw_edge_supporting_plane.tex` §3.  After the page reduction
`t(H,W) ≥ 2J - p·t(K₄,W)` and conditioning at a clique vertex, the row becomes
one inequality between real numbers.  With

```
T_p      = p²(2p-1)²(3p-2),
L_p(d,a) = T_p + p(2p-1)(30p²-15p-2)(d-p) + 4p(2p-1)(5p-3)(a-d²),
```

the claim is that `L_p` lies under the signed rooted bound at every feasible
`(d,a) = (d(x), A(x))`.  `L_p` is the unique plane through `(p,p²)` in the
coordinates `(d, a-d²)` whose integral is exactly `T_p`, because `∫d = p` and
`∫A = ∫d²`; the slopes are therefore forced, and so is the tangency.

**The route here differs from the note's, and needs none of its 144 Bernstein
coefficients.**  Write `s = 2a - p` and `w = 4a - 2p - d² = 2s - d²`.

* `s ≥ 0`, `w ≥ 0` — the active region.  The note treats `d(F_p - L_p)` as a
  cubic in `a`, factors its discriminant as `-256d²p(d-p)²(2p-1)K(p,d)`, and
  certifies `K > 0` by a degree-`(6,5)` Bernstein expansion with a 7×6 integer
  matrix.  Instead the cubic in `w` is factored *explicitly*, exactly as in
  `Methods/K4Tail/Scalar.lean`:
  ```
  (11p-6)³·4·(s²w - d·L_p) =
      ((11p-6)w - R)²·((11p-6)w + 2R + 2(11p-6)d²)
    + (11p-6)(d-p)²·LIN·w
    + (d-p)²·CON,
  ```
  a `ring` identity, where `R = 2d(3p²-7p+3) + p(27p²-26p+6)` is `11p-6` times
  the tangent line of the double root at `d = p`.
* `s ≥ 0`, `w ≤ 0` — the inactive region, where `L_p ≤ 0` because
  `L_p = -p(2p-1)·S_p(d) + γ_p·w/4` and the quadratic `S_p` has nonpositive
  discriminant.
* `s ≤ 0` — the negative region, where the bound is `d³s` rather than `0`.  The
  note checks four boundary faces there.  Only **two** are needed: the residual
  is affine in `a` with slope `2d³ - γ_p`, and the two lower bounds `a ≥ 0`,
  `a ≥ d+p-1` together with `a ≤ p/2` mean that the face `a = p/2` covers the
  slope-nonpositive case and the face `a = d+p-1` the slope-nonnegative one.
  Both faces are nonnegative on the whole box, and the second is only ever
  invoked where `2d³ ≥ γ_p`, which confines it to `p ≤ 4/5` and leaves a margin.

Every one-variable fact left over has *all coefficients nonnegative* after the
substitution `p = 2/3 + u`, so each is a one-line `nlinarith`.
-/

namespace Taeyoung.Methods.Atlas160

/-! ### The target and the supporting plane -/

/-- `T_p = p²(2p-1)²(3p-2)`, the catalogue target of Atlas 160. -/
noncomputable def targetT (p : ℝ) : ℝ := p ^ 2 * (2 * p - 1) ^ 2 * (3 * p - 2)

/-- `L_p(d,a)`, the supporting plane in the coordinates `(d, a - d²)`. -/
noncomputable def plane (p d a : ℝ) : ℝ :=
  targetT p + p * (2 * p - 1) * (30 * p ^ 2 - 15 * p - 2) * (d - p) +
    4 * p * (2 * p - 1) * (5 * p - 3) * (a - d ^ 2)

/-- The switching-point quadratic: `L_p(d,a) = -p(2p-1)·S_p(d)` at
`a = (2p+d²)/4`, the boundary `w = 0`. -/
noncomputable def Sfun (p d : ℝ) : ℝ :=
  15 * p * d ^ 2 - 9 * d ^ 2 - 30 * d * p ^ 2 + 15 * d * p + 2 * d +
    24 * p ^ 3 - 18 * p ^ 2 + 2 * p

/-! ### One-variable facts on `[2/3, 1]`

Each is a polynomial in `p` all of whose coefficients are nonnegative after
`p = 2/3 + u`, so `nlinarith` needs only the powers of `u`. -/

section OneVariable

variable {p : ℝ}

private lemma upow (hp : (2 : ℝ) / 3 ≤ p) (k : ℕ) : 0 ≤ (p - 2 / 3) ^ k :=
  pow_nonneg (by linarith) k

lemma pos_M (hp : (2 : ℝ) / 3 ≤ p) : 0 < 11 * p - 6 := by linarith

lemma pos_gam (hp : (2 : ℝ) / 3 ≤ p) : 0 < 5 * p - 3 := by linarith

lemma pos_Slead (hp : (2 : ℝ) / 3 ≤ p) : 0 < 15 * p - 9 := by linarith

lemma pos_Q1lead (hp : (2 : ℝ) / 3 ≤ p) : 0 < 20 * p - 12 := by linarith

lemma pos_Sdisc (hp : (2 : ℝ) / 3 ≤ p) : 0 < 60 * p ^ 2 - 36 * p - 1 := by
  nlinarith [upow hp 1, upow hp 2]

lemma pos_Q1disc (hp : (2 : ℝ) / 3 ≤ p) :
    0 < 510 * p ^ 3 - 591 * p ^ 2 + 164 * p + 4 := by
  nlinarith [upow hp 1, upow hp 2, upow hp 3]

lemma pos_LINq (hp : (2 : ℝ) / 3 ≤ p) :
    0 < 829 * p ^ 4 - 1324 * p ^ 3 + 646 * p ^ 2 - 60 * p - 18 := by
  nlinarith [upow hp 1, upow hp 2, upow hp 3, upow hp 4]

lemma pos_cubQ (hp : (2 : ℝ) / 3 ≤ p) :
    0 < 144 * p ^ 3 - 131 * p ^ 2 + 12 * p + 9 := by
  nlinarith [upow hp 1, upow hp 2, upow hp 3]

lemma pos_c27 (hp : (2 : ℝ) / 3 ≤ p) : 0 < 27 * p ^ 2 - 26 * p + 6 := by
  nlinarith [upow hp 1, upow hp 2]

/-- `A + B`, where `CON = A d² + B d + C`. -/
lemma pos_ApB (hp : (2 : ℝ) / 3 ≤ p) :
    0 ≤ 150576 * p ^ 6 - 399180 * p ^ 5 + 420380 * p ^ 4 - 219648 * p ^ 3 +
      56880 * p ^ 2 - 5832 * p := by
  nlinarith [upow hp 1, upow hp 2, upow hp 3, upow hp 4, upow hp 5, upow hp 6]

/-- `2((A+B)p/2 + C)`, the value of the `CON` chain at `d = p/2`. -/
lemma pos_ApBC (hp : (2 : ℝ) / 3 ≤ p) :
    0 ≤ 71844 * p ^ 7 - 171732 * p ^ 6 + 148868 * p ^ 5 - 48256 * p ^ 4 -
      3456 * p ^ 3 + 5400 * p ^ 2 - 864 * p := by
  nlinarith [upow hp 1, upow hp 2, upow hp 3, upow hp 4, upow hp 5, upow hp 6,
    upow hp 7]

end OneVariable

/-! ### The switching quadratic is nonnegative -/

theorem Sfun_nonneg {p : ℝ} (hp : (2 : ℝ) / 3 ≤ p) (d : ℝ) : 0 ≤ Sfun p d := by
  have hlead := pos_Slead hp
  have hdisc := pos_Sdisc hp
  have hkey : 4 * (15 * p - 9) * Sfun p d =
      (2 * (15 * p - 9) * d + (-30 * p ^ 2 + 15 * p + 2)) ^ 2 +
        (3 * p - 2) ^ 2 * (60 * p ^ 2 - 36 * p - 1) := by
    simp only [Sfun]
    ring
  have hnn : 0 ≤ 4 * (15 * p - 9) * Sfun p d := by
    rw [hkey]
    have h1 := sq_nonneg (2 * (15 * p - 9) * d + (-30 * p ^ 2 + 15 * p + 2))
    have h2 := mul_nonneg (sq_nonneg (3 * p - 2)) hdisc.le
    linarith
  rcases le_or_gt 0 (Sfun p d) with h | h
  · exact h
  · exfalso
    nlinarith [hnn, hlead, h]

/-! ### The inactive region: below the switching point the plane is nonpositive -/

theorem plane_nonpos {p d a : ℝ} (hp : (2 : ℝ) / 3 ≤ p)
    (hw : 4 * a - 2 * p - d ^ 2 ≤ 0) : plane p d a ≤ 0 := by
  have hppos : (0 : ℝ) < p := by linarith
  have h2p1 : (0 : ℝ) < 2 * p - 1 := by linarith
  have hgam : 0 < 4 * p * (2 * p - 1) * (5 * p - 3) :=
    mul_pos (mul_pos (by linarith) h2p1) (pos_gam hp)
  have hsplit : plane p d a =
      -(p * (2 * p - 1) * Sfun p d) +
        4 * p * (2 * p - 1) * (5 * p - 3) * ((4 * a - 2 * p - d ^ 2) / 4) := by
    simp only [plane, targetT, Sfun]
    ring
  have h1 : 4 * p * (2 * p - 1) * (5 * p - 3) * ((4 * a - 2 * p - d ^ 2) / 4) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hgam.le (by linarith)
  have h2 : -(p * (2 * p - 1) * Sfun p d) ≤ 0 := by
    have hS := Sfun_nonneg hp d
    have : 0 ≤ p * (2 * p - 1) * Sfun p d :=
      mul_nonneg (mul_nonneg hppos.le h2p1.le) hS
    linarith
  rw [hsplit]
  linarith

/-! ### The active region

`s = 2a - p ≥ 0` and `w = 4a - 2p - d² ≥ 0`.  The bound coming from Goodman in
the link is `s²w/d`, and the whole content is one factorization of the cubic in
`w`. -/

set_option maxHeartbeats 1000000 in
theorem plane_le_active {p d a : ℝ} (hp : (2 : ℝ) / 3 ≤ p) (hp1 : p ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (had : a ≤ d)
    (hw : 0 ≤ 4 * a - 2 * p - d ^ 2) :
    d * plane p d a ≤ (2 * a - p) ^ 2 * (4 * a - 2 * p - d ^ 2) := by
  have hM : 0 < 11 * p - 6 := pos_M hp
  have hppos : (0 : ℝ) < p := by linarith
  -- feasibility: `d² ≤ 4d - 2p`, hence `d ≥ p/2`
  have hdd : 0 ≤ 4 * d - 2 * p - d ^ 2 := by nlinarith [hw, had]
  have hdp : p / 2 ≤ d := by nlinarith [hdd, sq_nonneg d]
  -- the cubic factor
  have hZ : 0 ≤ (6 * d * p ^ 2 - 14 * d * p + 6 * d + 27 * p ^ 3 - 26 * p ^ 2 +
      6 * p) + (11 * p - 6) * d ^ 2 := by
    have hid : 4 * (11 * p - 6) *
        ((6 * d * p ^ 2 - 14 * d * p + 6 * d + 27 * p ^ 3 - 26 * p ^ 2 + 6 * p) +
          (11 * p - 6) * d ^ 2) =
        (2 * (11 * p - 6) * d + 2 * (3 * p ^ 2 - 7 * p + 3)) ^ 2 +
          4 * (2 * p - 1) * (144 * p ^ 3 - 131 * p ^ 2 + 12 * p + 9) := by ring
    nlinarith [hid, sq_nonneg (2 * (11 * p - 6) * d + 2 * (3 * p ^ 2 - 7 * p + 3)),
      mul_nonneg (by linarith : (0:ℝ) ≤ 2 * p - 1) (pos_cubQ hp).le, hM]
  have hfac : 0 ≤ (11 * p - 6) * (4 * a - 2 * p - d ^ 2) +
      2 * (6 * d * p ^ 2 - 14 * d * p + 6 * d + 27 * p ^ 3 - 26 * p ^ 2 + 6 * p) +
      2 * (11 * p - 6) * d ^ 2 := by
    nlinarith [mul_nonneg hM.le hw, hZ]
  -- the linear remainder coefficient
  have hLIN : 0 ≤ 121 * d ^ 2 * p ^ 2 - 132 * d ^ 2 * p + 36 * d ^ 2 +
      506 * d * p ^ 3 - 1024 * d * p ^ 2 + 672 * d * p - 144 * d +
      2187 * p ^ 4 - 4212 * p ^ 3 + 3000 * p ^ 2 - 936 * p + 108 := by
    have hid : 121 * d ^ 2 * p ^ 2 - 132 * d ^ 2 * p + 36 * d ^ 2 +
        506 * d * p ^ 3 - 1024 * d * p ^ 2 + 672 * d * p - 144 * d +
        2187 * p ^ 4 - 4212 * p ^ 3 + 3000 * p ^ 2 - 936 * p + 108 =
        ((11 * p - 6) * d + 23 * p ^ 2 - 34 * p + 12) ^ 2 +
          2 * (829 * p ^ 4 - 1324 * p ^ 3 + 646 * p ^ 2 - 60 * p - 18) := by ring
    rw [hid]
    have := pos_LINq hp
    positivity
  -- the constant remainder coefficient, via `d² ≤ d` and `d ≥ p/2`
  have hCON : 0 ≤ -8 * (11 * p - 6) * (3 * p ^ 2 - 7 * p + 3) ^ 2 * d ^ 2 +
      (150576 * p ^ 6 - 398388 * p ^ 5 + 416252 * p ^ 4 - 211736 * p ^ 3 +
        49968 * p ^ 2 - 3024 * p - 432) * d -
      2 * p * (27 * p ^ 2 - 26 * p + 6) ^ 3 := by
    have hAle : 0 ≤ 8 * (11 * p - 6) * (3 * p ^ 2 - 7 * p + 3) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have hsq : d ^ 2 ≤ d := by nlinarith [hd0, hd1]
    have hstep1 : -8 * (11 * p - 6) * (3 * p ^ 2 - 7 * p + 3) ^ 2 * d ^ 2 ≥
        -8 * (11 * p - 6) * (3 * p ^ 2 - 7 * p + 3) ^ 2 * d := by
      nlinarith [hAle, hsq]
    have hstep2 : 0 ≤ (150576 * p ^ 6 - 399180 * p ^ 5 + 420380 * p ^ 4 -
        219648 * p ^ 3 + 56880 * p ^ 2 - 5832 * p) * (d - p / 2) :=
      mul_nonneg (pos_ApB hp) (by linarith)
    have hstep3 := pos_ApBC hp
    nlinarith [hstep1, hstep2, hstep3]
  -- the factorization
  have key : (11 * p - 6) ^ 3 * 4 *
      ((2 * a - p) ^ 2 * (4 * a - 2 * p - d ^ 2) - d * plane p d a) =
      ((11 * p - 6) * (4 * a - 2 * p - d ^ 2) -
          (6 * d * p ^ 2 - 14 * d * p + 6 * d + 27 * p ^ 3 - 26 * p ^ 2 +
            6 * p)) ^ 2 *
        ((11 * p - 6) * (4 * a - 2 * p - d ^ 2) +
          2 * (6 * d * p ^ 2 - 14 * d * p + 6 * d + 27 * p ^ 3 - 26 * p ^ 2 +
            6 * p) + 2 * (11 * p - 6) * d ^ 2) +
      (11 * p - 6) * (d - p) ^ 2 *
        (121 * d ^ 2 * p ^ 2 - 132 * d ^ 2 * p + 36 * d ^ 2 +
          506 * d * p ^ 3 - 1024 * d * p ^ 2 + 672 * d * p - 144 * d +
          2187 * p ^ 4 - 4212 * p ^ 3 + 3000 * p ^ 2 - 936 * p + 108) *
        (4 * a - 2 * p - d ^ 2) +
      (d - p) ^ 2 *
        (-8 * (11 * p - 6) * (3 * p ^ 2 - 7 * p + 3) ^ 2 * d ^ 2 +
          (150576 * p ^ 6 - 398388 * p ^ 5 + 416252 * p ^ 4 - 211736 * p ^ 3 +
            49968 * p ^ 2 - 3024 * p - 432) * d -
          2 * p * (27 * p ^ 2 - 26 * p + 6) ^ 3) := by
    simp only [plane, targetT]
    ring
  have hrhs : 0 ≤ (11 * p - 6) ^ 3 * 4 *
      ((2 * a - p) ^ 2 * (4 * a - 2 * p - d ^ 2) - d * plane p d a) := by
    rw [key]
    have t1 : 0 ≤ ((11 * p - 6) * (4 * a - 2 * p - d ^ 2) -
        (6 * d * p ^ 2 - 14 * d * p + 6 * d + 27 * p ^ 3 - 26 * p ^ 2 +
          6 * p)) ^ 2 *
        ((11 * p - 6) * (4 * a - 2 * p - d ^ 2) +
          2 * (6 * d * p ^ 2 - 14 * d * p + 6 * d + 27 * p ^ 3 - 26 * p ^ 2 +
            6 * p) + 2 * (11 * p - 6) * d ^ 2) := mul_nonneg (sq_nonneg _) hfac
    have t2 : 0 ≤ (11 * p - 6) * (d - p) ^ 2 *
        (121 * d ^ 2 * p ^ 2 - 132 * d ^ 2 * p + 36 * d ^ 2 +
          506 * d * p ^ 3 - 1024 * d * p ^ 2 + 672 * d * p - 144 * d +
          2187 * p ^ 4 - 4212 * p ^ 3 + 3000 * p ^ 2 - 936 * p + 108) *
        (4 * a - 2 * p - d ^ 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg hM.le (sq_nonneg _)) hLIN) hw
    have t3 : 0 ≤ (d - p) ^ 2 *
        (-8 * (11 * p - 6) * (3 * p ^ 2 - 7 * p + 3) ^ 2 * d ^ 2 +
          (150576 * p ^ 6 - 398388 * p ^ 5 + 416252 * p ^ 4 - 211736 * p ^ 3 +
            49968 * p ^ 2 - 3024 * p - 432) * d -
          2 * p * (27 * p ^ 2 - 26 * p + 6) ^ 3) := mul_nonneg (sq_nonneg _) hCON
    linarith
  have hpos : 0 < (11 * p - 6) ^ 3 * 4 := by positivity
  rcases le_total 0
    ((2 * a - p) ^ 2 * (4 * a - 2 * p - d ^ 2) - d * plane p d a) with h | h
  · linarith
  · nlinarith [hrhs, hpos]

/-! ### The negative region

`s = 2a - p ≤ 0`.  The residual `d³s - L_p` is affine in `a` with slope
`2d³ - γ_p`, and the two faces `a = p/2` and `a = d + p - 1` cover the two
signs of that slope. -/

/-- The face `a = p/2`, where `s = 0`.  Nonnegative on the whole box. -/
theorem face_half {p d : ℝ} (hp : (2 : ℝ) / 3 ≤ p) :
    0 ≤ p * (2 * p - 1) *
      ((20 * p - 12) * d ^ 2 + (-30 * p ^ 2 + 15 * p + 2) * d +
        (24 * p ^ 3 - 18 * p ^ 2 + 2 * p)) := by
  have hlead := pos_Q1lead hp
  have hQ : 0 ≤ (20 * p - 12) * d ^ 2 + (-30 * p ^ 2 + 15 * p + 2) * d +
      (24 * p ^ 3 - 18 * p ^ 2 + 2 * p) := by
    have hid : 4 * (20 * p - 12) *
        ((20 * p - 12) * d ^ 2 + (-30 * p ^ 2 + 15 * p + 2) * d +
          (24 * p ^ 3 - 18 * p ^ 2 + 2 * p)) =
        (2 * (20 * p - 12) * d + (-30 * p ^ 2 + 15 * p + 2)) ^ 2 +
          (2 * p - 1) * (510 * p ^ 3 - 591 * p ^ 2 + 164 * p + 4) := by ring
    nlinarith [hid, sq_nonneg (2 * (20 * p - 12) * d + (-30 * p ^ 2 + 15 * p + 2)),
      mul_nonneg (by linarith : (0:ℝ) ≤ 2 * p - 1) (pos_Q1disc hp).le, hlead]
  have hpp : 0 ≤ p * (2 * p - 1) :=
    mul_nonneg (by linarith) (by linarith)
  exact mul_nonneg hpp hQ

set_option maxHeartbeats 4000000 in
/-- The face `a = d + p - 1`.  Only ever invoked where `2d³ ≥ γ_p`, which
confines the box to `d ≥ 1/2`, `p ≤ 5/6` and leaves a margin; the residual is
then a positive combination of Bernstein monomials on that box. -/
theorem face_low {p d : ℝ} (hp : (2 : ℝ) / 3 ≤ p) (hp1 : p ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hslope : 4 * p * (2 * p - 1) * (5 * p - 3) ≤ 2 * d ^ 3) :
    0 ≤ 2 * d ^ 4 + d ^ 3 * p - 2 * d ^ 3 + 40 * d ^ 2 * p ^ 3 -
      44 * d ^ 2 * p ^ 2 + 12 * d ^ 2 * p - 60 * d * p ^ 4 + 20 * d * p ^ 3 +
      33 * d * p ^ 2 - 14 * d * p + 48 * p ^ 5 - 80 * p ^ 4 + 84 * p ^ 3 -
      52 * p ^ 2 + 12 * p := by
  -- the slope hypothesis confines the box to `d ≥ 1/2` and `p ≤ 5/6`
  have hgamlo : (8 : ℝ) / 27 ≤ 4 * p * (2 * p - 1) * (5 * p - 3) := by
    nlinarith [upow hp 1, upow hp 2, upow hp 3]
  have hd2 : (1 : ℝ) / 2 ≤ d := by
    by_contra hcon
    push_neg at hcon
    have h8 : d ^ 3 < 1 / 8 := by
      nlinarith [mul_pos (show (0:ℝ) < 1 / 2 - d by linarith)
        (show (0:ℝ) < 1 / 4 + d / 2 + d ^ 2 by positivity)]
    linarith
  have hp56 : p ≤ (5 : ℝ) / 6 := by
    by_contra hcon
    push_neg at hcon
    have hbig : (2 : ℝ) < 4 * p * (2 * p - 1) * (5 * p - 3) := by
      nlinarith [pow_nonneg (show (0:ℝ) ≤ p - 5 / 6 by linarith) 1,
        pow_nonneg (show (0:ℝ) ≤ p - 5 / 6 by linarith) 2,
        pow_nonneg (show (0:ℝ) ≤ p - 5 / 6 by linarith) 3]
    have hd3 : d ^ 3 ≤ 1 := pow_le_one₀ hd0 hd1
    linarith
  have hu : (0 : ℝ) ≤ p - 2 / 3 := by linarith
  have hU : (0 : ℝ) ≤ 5 / 6 - p := by linarith
  have hv : (0 : ℝ) ≤ d - 1 / 2 := by linarith
  have hV : (0 : ℝ) ≤ 1 - d := by linarith
  have hkey : 2 * d ^ 4 + d ^ 3 * p - 2 * d ^ 3 + 40 * d ^ 2 * p ^ 3 -
      44 * d ^ 2 * p ^ 2 + 12 * d ^ 2 * p - 60 * d * p ^ 4 + 20 * d * p ^ 3 +
      33 * d * p ^ 2 - 14 * d * p + 48 * p ^ 5 - 80 * p ^ 4 + 84 * p ^ 3 -
      52 * p ^ 2 + 12 * p =
        48384 * (5 / 6 - p) ^ 6 * (1 - d) ^ 5 +
        20736 * (5 / 6 - p) ^ 6 * (d - 1 / 2) * (1 - d) ^ 4 +
        82944 * (5 / 6 - p) ^ 6 * (d - 1 / 2) ^ 2 * (1 - d) ^ 3 +
        1105920 * (5 / 6 - p) ^ 6 * (d - 1 / 2) ^ 3 * (1 - d) ^ 2 +
        1990656 * (5 / 6 - p) ^ 6 * (d - 1 / 2) ^ 4 * (1 - d) +
        995328 * (5 / 6 - p) ^ 6 * (d - 1 / 2) ^ 5 +
        745344 * (p - 2 / 3) * (5 / 6 - p) ^ 5 * (1 - d) ^ 5 +
        1525248 * (p - 2 / 3) * (5 / 6 - p) ^ 5 * (d - 1 / 2) * (1 - d) ^ 4 +
        2058624 * (p - 2 / 3) * (5 / 6 - p) ^ 5 * (d - 1 / 2) ^ 2 * (1 - d) ^ 3 +
        7494912 * (p - 2 / 3) * (5 / 6 - p) ^ 5 * (d - 1 / 2) ^ 3 * (1 - d) ^ 2 +
        12307968 * (p - 2 / 3) * (5 / 6 - p) ^ 5 * (d - 1 / 2) ^ 4 * (1 - d) +
        6091776 * (p - 2 / 3) * (5 / 6 - p) ^ 5 * (d - 1 / 2) ^ 5 +
        3431808 * (p - 2 / 3) ^ 2 * (5 / 6 - p) ^ 4 * (1 - d) ^ 5 +
        8411904 * (p - 2 / 3) ^ 2 * (5 / 6 - p) ^ 4 * (d - 1 / 2) * (1 - d) ^ 4 +
        9500544 * (p - 2 / 3) ^ 2 * (5 / 6 - p) ^ 4 * (d - 1 / 2) ^ 2 * (1 - d) ^ 3 +
        19968768 * (p - 2 / 3) ^ 2 * (5 / 6 - p) ^ 4 * (d - 1 / 2) ^ 3 * (1 - d) ^ 2 +
        30723840 * (p - 2 / 3) ^ 2 * (5 / 6 - p) ^ 4 * (d - 1 / 2) ^ 4 * (1 - d) +
        15275520 * (p - 2 / 3) ^ 2 * (5 / 6 - p) ^ 4 * (d - 1 / 2) ^ 5 +
        7407360 * (p - 2 / 3) ^ 3 * (5 / 6 - p) ^ 3 * (1 - d) ^ 5 +
        19293696 * (p - 2 / 3) ^ 3 * (5 / 6 - p) ^ 3 * (d - 1 / 2) * (1 - d) ^ 4 +
        19420416 * (p - 2 / 3) ^ 3 * (5 / 6 - p) ^ 3 * (d - 1 / 2) ^ 2 * (1 - d) ^ 3 +
        26836992 * (p - 2 / 3) ^ 3 * (5 / 6 - p) ^ 3 * (d - 1 / 2) ^ 3 * (1 - d) ^ 2 +
        39283200 * (p - 2 / 3) ^ 3 * (5 / 6 - p) ^ 3 * (d - 1 / 2) ^ 4 * (1 - d) +
        19980288 * (p - 2 / 3) ^ 3 * (5 / 6 - p) ^ 3 * (d - 1 / 2) ^ 5 +
        8416512 * (p - 2 / 3) ^ 4 * (5 / 6 - p) ^ 2 * (1 - d) ^ 5 +
        22604544 * (p - 2 / 3) ^ 4 * (5 / 6 - p) ^ 2 * (d - 1 / 2) * (1 - d) ^ 4 +
        21037824 * (p - 2 / 3) ^ 4 * (5 / 6 - p) ^ 2 * (d - 1 / 2) ^ 2 * (1 - d) ^ 3 +
        19427328 * (p - 2 / 3) ^ 4 * (5 / 6 - p) ^ 2 * (d - 1 / 2) ^ 3 * (1 - d) ^ 2 +
        26876160 * (p - 2 / 3) ^ 4 * (5 / 6 - p) ^ 2 * (d - 1 / 2) ^ 4 * (1 - d) +
        14298624 * (p - 2 / 3) ^ 4 * (5 / 6 - p) ^ 2 * (d - 1 / 2) ^ 5 +
        4910976 * (p - 2 / 3) ^ 5 * (5 / 6 - p) * (1 - d) ^ 5 +
        13519872 * (p - 2 / 3) ^ 5 * (5 / 6 - p) * (d - 1 / 2) * (1 - d) ^ 4 +
        12113280 * (p - 2 / 3) ^ 5 * (5 / 6 - p) * (d - 1 / 2) ^ 2 * (1 - d) ^ 3 +
        7471872 * (p - 2 / 3) ^ 5 * (5 / 6 - p) * (d - 1 / 2) ^ 3 * (1 - d) ^ 2 +
        9248256 * (p - 2 / 3) ^ 5 * (5 / 6 - p) * (d - 1 / 2) ^ 4 * (1 - d) +
        5280768 * (p - 2 / 3) ^ 5 * (5 / 6 - p) * (d - 1 / 2) ^ 5 +
        1166976 * (p - 2 / 3) ^ 6 * (1 - d) ^ 5 +
        3301632 * (p - 2 / 3) ^ 6 * (d - 1 / 2) * (1 - d) ^ 4 +
        2971008 * (p - 2 / 3) ^ 6 * (d - 1 / 2) ^ 2 * (1 - d) ^ 3 +
        1301760 * (p - 2 / 3) ^ 6 * (d - 1 / 2) ^ 3 * (1 - d) ^ 2 +
        1248768 * (p - 2 / 3) ^ 6 * (d - 1 / 2) ^ 4 * (1 - d) +
        783360 * (p - 2 / 3) ^ 6 * (d - 1 / 2) ^ 5 := by ring
  rw [hkey]
  have B : ∀ i j : ℕ,
      (0 : ℝ) ≤ (p - 2 / 3) ^ i * (5 / 6 - p) ^ (6 - i) *
        ((d - 1 / 2) ^ j * (1 - d) ^ (5 - j)) := fun i j ↦
    mul_nonneg (mul_nonneg (pow_nonneg hu i) (pow_nonneg hU (6 - i)))
      (mul_nonneg (pow_nonneg hv j) (pow_nonneg hV (5 - j)))
  linarith [B 0 0, B 0 1, B 0 2, B 0 3, B 0 4, B 0 5,
    B 1 0, B 1 1, B 1 2, B 1 3, B 1 4, B 1 5,
    B 2 0, B 2 1, B 2 2, B 2 3, B 2 4, B 2 5,
    B 3 0, B 3 1, B 3 2, B 3 3, B 3 4, B 3 5,
    B 4 0, B 4 1, B 4 2, B 4 3, B 4 4, B 4 5,
    B 5 0, B 5 1, B 5 2, B 5 3, B 5 4, B 5 5,
    B 6 0, B 6 1, B 6 2, B 6 3, B 6 4, B 6 5]

/-- **The negative region.** -/
theorem plane_le_neg {p d a : ℝ} (hp : (2 : ℝ) / 3 ≤ p) (hp1 : p ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hlo : d + p - 1 ≤ a)
    (hs : 2 * a - p ≤ 0) :
    plane p d a ≤ d ^ 3 * (2 * a - p) := by
  rcases le_total (4 * p * (2 * p - 1) * (5 * p - 3)) (2 * d ^ 3) with hsl | hsl
  · -- slope nonnegative: descend to `a = d + p - 1`
    have hface := face_low hp hp1 hd0 hd1 hsl
    have hmono : 0 ≤ (2 * d ^ 3 - 4 * p * (2 * p - 1) * (5 * p - 3)) *
        (a - (d + p - 1)) :=
      mul_nonneg (by linarith) (by linarith)
    have hid : d ^ 3 * (2 * a - p) - plane p d a =
        (2 * d ^ 4 + d ^ 3 * p - 2 * d ^ 3 + 40 * d ^ 2 * p ^ 3 -
          44 * d ^ 2 * p ^ 2 + 12 * d ^ 2 * p - 60 * d * p ^ 4 + 20 * d * p ^ 3 +
          33 * d * p ^ 2 - 14 * d * p + 48 * p ^ 5 - 80 * p ^ 4 + 84 * p ^ 3 -
          52 * p ^ 2 + 12 * p) +
        (2 * d ^ 3 - 4 * p * (2 * p - 1) * (5 * p - 3)) * (a - (d + p - 1)) := by
      simp only [plane, targetT]
      ring
    linarith
  · -- slope nonpositive: ascend to `a = p/2`
    have hface := face_half (p := p) (d := d) hp
    have hmono : 0 ≤ (4 * p * (2 * p - 1) * (5 * p - 3) - 2 * d ^ 3) *
        (p / 2 - a) :=
      mul_nonneg (by linarith) (by linarith)
    have hid : d ^ 3 * (2 * a - p) - plane p d a =
        p * (2 * p - 1) *
          ((20 * p - 12) * d ^ 2 + (-30 * p ^ 2 + 15 * p + 2) * d +
            (24 * p ^ 3 - 18 * p ^ 2 + 2 * p)) +
        (4 * p * (2 * p - 1) * (5 * p - 3) - 2 * d ^ 3) * (p / 2 - a) := by
      simp only [plane, targetT]
      ring
    linarith

end Taeyoung.Methods.Atlas160
