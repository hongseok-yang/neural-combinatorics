import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Atlas 178: the two half-degree supporting planes

`notes/atlas178_half_degree_weighted_k4.tex` Lemma 3.1, in the square-root
coordinates `D = √d`, `r = √p`, so that both planes are polynomial.  Writing
`c₃ = 2p-1` and `c₄ = 3p-2`, the note's two claims are

```
(2D - r)·t ≥ p r c₃ + (3/2) r (4p-1)(d-p) + (3/2) r (a - d²),
(t/D)(2t - d² - c₄ d) ≥ 3 p r c₃ (d-p) + 2 r c₃ (a - d²),
```

the second multiplied through by `D` so that no quotient appears.

**Neither plane needs a Bernstein certificate.**  The note proves them by
conditional subdivision trees of 500 and 406 boxes.  Both are in fact explicit
nonnegative combinations of the feasibility slacks, obtained from the exact
linear (respectively quadratic) programming dual.  With

```
g₅ = t - 2a + p,   g₆ = t - a + d - d²,   g₈ = d² - t,
```

the three identities below are `ring` facts:

```
res₁ = (3/2)r·g₅ + (7r/2 - 4D)·g₈ + Φ_U                   on  8D ≤ 7r
res₁ = (5r - 4D)·g₅ + (8D - 7r)·g₆ + 2(D - r)²·L          on  8D ≥ 7r
res₂ = 2Drc₃·g₆ + 2(t - θ)² + (D/8)(D - r)²·M,  θ = D(D+r)(D²-Dr+4r²-2)/4
```

Plane 1 is affine in `(a,t)`, so its minimum is attained at a vertex of the
feasible polygon; the two duals above already cover the whole band, one on each
side of the line `8D = 7r`.  Plane 2 is convex in `t`, and completing the square
after removing `2Drc₃·g₆` leaves a remainder nonnegative on the whole box, so it
needs no case split at all.  In both planes the tangency at the balanced
tripartite graphon appears as an explicit `(D-r)²`, exactly as in
`Methods/K4Tail/Scalar.lean` and `Methods/Atlas160/Scalar.lean`.

The two leftover scalar factors are settled here without any box subdivision:
`L` by one `nlinarith`, and `Φ_U` by the two exact identities

```
256·H = 2078r⁵ + 2471(7r-8D)r⁴ + (7r-8D)²(289r³ + 1064r²D + 832rD² + 512D³),
32·Φ_U = H + r(25r² - 16)(5r² - 6D²),  H = 128D⁵ - 16D⁴r - 234D²r³ + 131r⁵,
```

in which every summand is visibly nonnegative on `0 ≤ 8D ≤ 7r`, `r² ≥ 16/25`.
-/

namespace Taeyoung.Methods.Atlas178

/-! ### The two residuals -/

/-- Twice the residual of the first plane. -/
noncomputable def res₁ (r D a t : ℝ) : ℝ :=
  2 * (2 * D - r) * t - 2 * r ^ 3 * (2 * r ^ 2 - 1)
    - 3 * r * (4 * r ^ 2 - 1) * (D ^ 2 - r ^ 2) - 3 * r * (a - D ^ 4)

/-- `D` times the residual of the second plane. -/
noncomputable def res₂ (r D a t : ℝ) : ℝ :=
  t * (2 * t - D ^ 4 - (3 * r ^ 2 - 2) * D ^ 2)
    - D * (3 * r ^ 2 * r * (2 * r ^ 2 - 1) * (D ^ 2 - r ^ 2)
      + 2 * r * (2 * r ^ 2 - 1) * (a - D ^ 4))

/-- The stationary point of `res₂` in `t` after the slack `g₆` is removed. -/
noncomputable def theta (r D : ℝ) : ℝ :=
  D * (D + r) * (D ^ 2 - D * r + 4 * r ^ 2 - 2) / 4

/-- The cubic left over on the upper band `8D ≥ 7r`, after the double root
`(D-r)²`. -/
noncomputable def cubicL (r D : ℝ) : ℝ :=
  4 * D ^ 3 + 6 * D ^ 2 * r + 8 * D * r ^ 2 - 4 * D + 4 * r ^ 3 - 3 * r

/-- The quintic left over on the lower band `8D ≤ 7r`. -/
noncomputable def phiU (r D : ℝ) : ℝ :=
  (8 * D ^ 5 - D ^ 4 * r - 24 * D ^ 2 * r ^ 3 + 6 * D ^ 2 * r
    + 16 * r ^ 5 - 5 * r ^ 3) / 2

/-- The remainder of the second plane after completing the square in `t`. -/
noncomputable def bigM (r D : ℝ) : ℝ :=
  -D ^ 5 - 2 * D ^ 4 * r - 9 * D ^ 3 * r ^ 2 + 4 * D ^ 3
    + 40 * D ^ 2 * r ^ 3 - 20 * D ^ 2 * r + 80 * D * r ^ 4 - 32 * D * r ^ 2
    - 4 * D + 48 * r ^ 5 - 24 * r ^ 3

/-! ### `r` is bounded below by a rational number

`p ≥ 2/3` and `r = √p ≥ 0` force `r ≥ 4/5`, which is what the polynomial
arguments below actually use. -/

lemma four_fifths_le {r : ℝ} (hr0 : 0 ≤ r) (hrp : (2:ℝ)/3 ≤ r ^ 2) :
    (4:ℝ)/5 ≤ r := by
  nlinarith [hrp, hr0]

/-! ### The upper band `8D ≥ 7r` -/

set_option maxHeartbeats 1000000 in
/-- The cubic left after the double root `(D-r)²` on the upper band. -/
theorem cubicL_nonneg {r D : ℝ} (hr45 : (4:ℝ)/5 ≤ r) (hhigh : 7 * r ≤ 8 * D) :
    0 ≤ cubicL r D := by
  have hr0 : (0:ℝ) ≤ r := by linarith
  have hD0 : (0:ℝ) ≤ D := by linarith
  unfold cubicL
  nlinarith [hhigh, hD0, hr0, hr45, mul_nonneg hD0 hD0, mul_nonneg hr0 hr0,
    mul_nonneg (mul_nonneg hD0 hD0) hD0, mul_nonneg hD0 hr0,
    mul_nonneg (by linarith : (0:ℝ) ≤ 8 * D - 7 * r) hr0,
    mul_nonneg (by linarith : (0:ℝ) ≤ 8 * D - 7 * r) hD0,
    mul_nonneg (by linarith : (0:ℝ) ≤ 5 * r - 4) hr0]

/-! ### The lower band `8D ≤ 7r`

`Φ_U` is not homogeneous — it mixes degrees `5` and `3` — so the degree-3 part
is first traded against the degree-5 part using `25r² ≥ 16`.  What is left is
the homogeneous quintic `H`, and `H` has all-positive coefficients once written
in the band coordinates `7r - 8D` and `D`. -/

/-- The homogeneous quintic behind `Φ_U`. -/
theorem quinticH_nonneg {r D : ℝ} (hD0 : 0 ≤ D) (hr0 : 0 ≤ r)
    (hlow : 8 * D ≤ 7 * r) :
    0 ≤ 128 * D ^ 5 - 16 * D ^ 4 * r - 234 * D ^ 2 * r ^ 3 + 131 * r ^ 5 := by
  have hu : (0:ℝ) ≤ 7 * r - 8 * D := by linarith
  have key : 256 * (128 * D ^ 5 - 16 * D ^ 4 * r - 234 * D ^ 2 * r ^ 3
        + 131 * r ^ 5)
      = 2078 * r ^ 5 + 2471 * (7 * r - 8 * D) * r ^ 4
        + (7 * r - 8 * D) ^ 2
          * (289 * r ^ 3 + 1064 * r ^ 2 * D + 832 * r * D ^ 2
            + 512 * D ^ 3) := by
    ring
  have h1 : (0:ℝ) ≤ 2078 * r ^ 5 := by positivity
  have h2 : (0:ℝ) ≤ 2471 * (7 * r - 8 * D) * r ^ 4 := by positivity
  have h3 : (0:ℝ) ≤ (7 * r - 8 * D) ^ 2
      * (289 * r ^ 3 + 1064 * r ^ 2 * D + 832 * r * D ^ 2 + 512 * D ^ 3) := by
    positivity
  linarith [key, h1, h2, h3]

/-- `Φ_U ≥ 0` on the lower band.  No subdivision: two `ring` identities. -/
theorem phiU_nonneg {r D : ℝ} (hD0 : 0 ≤ D) (hr45 : (4:ℝ)/5 ≤ r)
    (hlow : 8 * D ≤ 7 * r) : 0 ≤ phiU r D := by
  have hr0 : (0:ℝ) ≤ r := by linarith
  have hsq : 64 * D ^ 2 ≤ 49 * r ^ 2 := by nlinarith [hD0, hr0, hlow]
  have h56 : (0:ℝ) ≤ 5 * r ^ 2 - 6 * D ^ 2 := by nlinarith [hsq, sq_nonneg r]
  have hr16 : (0:ℝ) ≤ 25 * r ^ 2 - 16 := by nlinarith [hr45, hr0]
  have hH := quinticH_nonneg hD0 hr0 hlow
  have hprod : (0:ℝ) ≤ r * (25 * r ^ 2 - 16) * (5 * r ^ 2 - 6 * D ^ 2) :=
    mul_nonneg (mul_nonneg hr0 hr16) h56
  have key : 32 * phiU r D
      = (128 * D ^ 5 - 16 * D ^ 4 * r - 234 * D ^ 2 * r ^ 3 + 131 * r ^ 5)
        + r * (25 * r ^ 2 - 16) * (5 * r ^ 2 - 6 * D ^ 2) := by
    unfold phiU; ring
  linarith [key, hH, hprod]

/-! ### The remainder of the second plane -/

set_option maxHeartbeats 1000000 in
/-- `M ≥ 0` on the whole box, which is why plane 2 needs no case split. -/
theorem bigM_nonneg {r D : ℝ} (hr45 : (4:ℝ)/5 ≤ r) (hr1 : r ≤ 1) (hD0 : 0 ≤ D)
    (hD1 : D ≤ 1) (hrp : (2:ℝ)/3 ≤ r ^ 2) : 0 ≤ bigM r D := by
  have hc3 : (0:ℝ) ≤ 2 * r ^ 2 - 1 := by linarith
  have hr0 : (0:ℝ) ≤ r := by linarith
  have h1 : (0:ℝ) ≤ 24 * r ^ 3 * (2 * r ^ 2 - 1) := mul_nonneg (by positivity) hc3
  have h2 : (0:ℝ) ≤ D * (80 * r ^ 4 - 41 * r ^ 2 - 7) := by
    refine mul_nonneg hD0 ?_
    nlinarith [hrp, hr45, hr1]
  have h3 : (0:ℝ) ≤ 20 * D ^ 2 * r * (2 * r ^ 2 - 1) :=
    mul_nonneg (by positivity) hc3
  have h4 : (0:ℝ) ≤ D * (4 * D ^ 2 + 9 * r ^ 2 + 3 - D ^ 4 - 2 * D ^ 3 * r
      - 9 * D ^ 2 * r ^ 2) := by
    refine mul_nonneg hD0 ?_
    nlinarith [hD0, hD1, hr1, hr45, mul_nonneg hD0 hD0,
      mul_nonneg (mul_nonneg hD0 hD0) hD0, mul_nonneg (mul_nonneg hD0 hD0) hr0]
  have key : bigM r D
      = 24 * r ^ 3 * (2 * r ^ 2 - 1) + D * (80 * r ^ 4 - 41 * r ^ 2 - 7)
        + 20 * D ^ 2 * r * (2 * r ^ 2 - 1)
        + D * (4 * D ^ 2 + 9 * r ^ 2 + 3 - D ^ 4 - 2 * D ^ 3 * r
          - 9 * D ^ 2 * r ^ 2) := by
    unfold bigM; ring
  linarith [key, h1, h2, h3, h4]

/-! ### The two planes -/

/-- The first supporting plane, in the form `0 ≤ res₁`.  The hypotheses are the
three feasibility slacks `g₅`, `g₆`, `g₈` and the box. -/
theorem res₁_nonneg {r D a t : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1)
    (hr45 : (4:ℝ)/5 ≤ r)
    (hg₅ : 0 ≤ t - 2 * a + r ^ 2) (hg₆ : 0 ≤ t - a + D ^ 2 - D ^ 4)
    (hg₈ : 0 ≤ D ^ 4 - t) : 0 ≤ res₁ r D a t := by
  have hr0 : (0:ℝ) ≤ r := by linarith
  rcases le_total (8 * D) (7 * r) with hlow | hhigh
  · have hU := phiU_nonneg hD0 hr45 hlow
    have h1 : (0:ℝ) ≤ 3 / 2 * r * (t - 2 * a + r ^ 2) :=
      mul_nonneg (by positivity) hg₅
    have h2 : (0:ℝ) ≤ (7 / 2 * r - 4 * D) * (D ^ 4 - t) :=
      mul_nonneg (by linarith) hg₈
    have key : res₁ r D a t
        = 3 / 2 * r * (t - 2 * a + r ^ 2) + (7 / 2 * r - 4 * D) * (D ^ 4 - t)
          + phiU r D := by
      unfold res₁ phiU; ring
    linarith [key, h1, h2, hU]
  · have hL := cubicL_nonneg hr45 hhigh
    have h1 : (0:ℝ) ≤ (5 * r - 4 * D) * (t - 2 * a + r ^ 2) :=
      mul_nonneg (by linarith) hg₅
    have h2 : (0:ℝ) ≤ (8 * D - 7 * r) * (t - a + D ^ 2 - D ^ 4) :=
      mul_nonneg (by linarith) hg₆
    have h3 : (0:ℝ) ≤ 2 * (D - r) ^ 2 * cubicL r D :=
      mul_nonneg (by positivity) hL
    have key : res₁ r D a t
        = (5 * r - 4 * D) * (t - 2 * a + r ^ 2)
          + (8 * D - 7 * r) * (t - a + D ^ 2 - D ^ 4)
          + 2 * (D - r) ^ 2 * cubicL r D := by
      unfold res₁ cubicL; ring
    linarith [key, h1, h2, h3]

/-- The second supporting plane, in the form `0 ≤ res₂`.  It needs only the
single slack `g₆`; no case split occurs. -/
theorem res₂_nonneg {r D a t : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1)
    (hr45 : (4:ℝ)/5 ≤ r) (hr1 : r ≤ 1) (hrp : (2:ℝ)/3 ≤ r ^ 2)
    (hg₆ : 0 ≤ t - a + D ^ 2 - D ^ 4) : 0 ≤ res₂ r D a t := by
  have hr0 : (0:ℝ) ≤ r := by linarith
  have hc3 : (0:ℝ) ≤ 2 * r ^ 2 - 1 := by linarith
  have hM := bigM_nonneg hr45 hr1 hD0 hD1 hrp
  have h1 : (0:ℝ) ≤ 2 * D * r * (2 * r ^ 2 - 1) * (t - a + D ^ 2 - D ^ 4) :=
    mul_nonneg (by positivity) hg₆
  have h2 : (0:ℝ) ≤ 2 * (t - theta r D) ^ 2 := by positivity
  have h3 : (0:ℝ) ≤ D / 8 * (D - r) ^ 2 * bigM r D :=
    mul_nonneg (by positivity) hM
  have key : res₂ r D a t
      = 2 * D * r * (2 * r ^ 2 - 1) * (t - a + D ^ 2 - D ^ 4)
        + 2 * (t - theta r D) ^ 2 + D / 8 * (D - r) ^ 2 * bigM r D := by
    unfold res₂ theta bigM; ring
  linarith [key, h1, h2, h3]

end Taeyoung.Methods.Atlas178
