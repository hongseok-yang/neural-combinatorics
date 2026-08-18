import Taeyoung.Methods.TriangleDensity

/-!
# Atlas 148: the scalar layer of the low-density interval

On `[1/2, 3/5]` the note bounds the density below by the square of the paw
density and the paw density below by `p·g(p)`, where `g` is the extremal
triangle profile.  Everything scalar in that chain is cleanest in the
parameter `y` of the extremal three-part graphon, where

```
p = paramEdge y = (1 + 2y - 3y²)/2,      g(p) = paramProfile y = (3/2)y(1-y)².
```

`TriangleDensity.fisherParam` inverts the first relation, so the passage
between the two coordinates is `fisherParam_quadratic`.

Three polynomial facts are needed, and none of them requires the note's
Bernstein data.

* `sq_paramProfile_le` — `6g(p)² ≤ p³`, which is the whole content of the
  branch above `s = 2/3`, where Goodman replaces the clique density theorem.
  It reduces to `108y²(1-y) ≤ (1+3y)³`, and that difference factors as
  `(3y-1)²(15y+1)`.
* `cross_mono` — the normalized monotonicity `g(s)/s^{3/2} ≥ g(p)/p^{3/2}`,
  cross-multiplied and squared into `s³g(p)² ≤ p³g(s)²`.  It reduces to
  `Q(y₁,y₂) ≤ 0` on `0 ≤ y₁ ≤ y₂ ≤ 1/3`, which `nlinarith` closes.
* `low_comparison` — the note's Lemma 4.1, `c²f ≤ p·g(p)²`.  The note gives
  seven Bernstein coefficients for it; `nlinarith` closes it directly.

The restriction `y ≤ 1/8` is the note's: `paramEdge` is increasing and
`paramEdge (1/8) = 77/128 > 3/5`, so `p ≤ 3/5` forces `y ≤ 1/8`.
-/

namespace Taeyoung.Methods.Atlas148

open Taeyoung.Methods.TriangleDensity

/-- `p` as a function of the extremal parameter. -/
noncomputable def paramEdge (y : ℝ) : ℝ := (1 + 2 * y - 3 * y ^ 2) / 2

/-- The extremal triangle profile, in the same parameter. -/
noncomputable def paramProfile (y : ℝ) : ℝ := 3 / 2 * y * (1 - y) ^ 2

lemma paramProfile_nonneg {y : ℝ} (hy0 : 0 ≤ y) : 0 ≤ paramProfile y := by
  rw [paramProfile]; positivity

lemma paramEdge_nonneg {y : ℝ} (hy0 : 0 ≤ y) (hy3 : y ≤ 1 / 3) : 0 ≤ paramEdge y := by
  rw [paramEdge]; nlinarith

/-! ### The two coordinates agree -/

lemma paramEdge_fisherParam {p : ℝ} (hhi : p ≤ 2 / 3) :
    paramEdge (fisherParam p) = p := by
  rw [paramEdge]; exact fisherParam_quadratic hhi

lemma fisherProfile_eq (p : ℝ) : fisherProfile p = paramProfile (fisherParam p) := by
  rw [fisherProfile, paramProfile]

/-- `paramEdge` is increasing where it matters, so `p ≤ 3/5` pins `y ≤ 1/8`. -/
lemma param_le_eighth {y : ℝ} (hy0 : 0 ≤ y) (hy3 : y ≤ 1 / 3)
    (h : paramEdge y ≤ 3 / 5) : y ≤ 1 / 8 := by
  by_contra hcon
  rw [not_le] at hcon
  rw [paramEdge] at h
  nlinarith [hcon, hy3]

/-- On the range in play, `paramEdge` reflects the order. -/
lemma le_of_paramEdge_le {y₁ y₂ : ℝ} (h1 : 0 ≤ y₁) (h8 : y₁ ≤ 1 / 8)
    (h2 : 0 ≤ y₂) (h3 : y₂ ≤ 1 / 3) (h : paramEdge y₁ ≤ paramEdge y₂) : y₁ ≤ y₂ := by
  by_contra hcon
  rw [not_le] at hcon
  rw [paramEdge, paramEdge] at h
  nlinarith [hcon, h8, h2]

/-! ### The three polynomial facts -/

/-- **The Goodman branch.**  `6g(p)² ≤ p³`, from `(1+3y)³ - 108y²(1-y)
= (3y-1)²(15y+1)`. -/
lemma sq_paramProfile_le {y : ℝ} (hy0 : 0 ≤ y) (hy3 : y ≤ 1 / 3) :
    6 * paramProfile y ^ 2 ≤ paramEdge y ^ 3 := by
  rw [paramProfile, paramEdge]
  nlinarith [mul_nonneg (mul_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ 1 - y) 3)
      (sq_nonneg (3 * y - 1))) (by linarith : (0:ℝ) ≤ 15 * y + 1)]

set_option maxHeartbeats 1000000 in
/-- **Normalized monotonicity**, cross-multiplied and squared. -/
lemma cross_mono {y₁ y₂ : ℝ} (h1 : 0 ≤ y₁) (h12 : y₁ ≤ y₂) (h3 : y₂ ≤ 1 / 3) :
    paramEdge y₂ ^ 3 * paramProfile y₁ ^ 2 ≤ paramEdge y₁ ^ 3 * paramProfile y₂ ^ 2 := by
  have hQ : 54 * y₁ ^ 2 * y₂ ^ 2 + 9 * y₁ ^ 2 * y₂ + y₁ ^ 2 + 9 * y₁ * y₂ ^ 2
      - 8 * y₁ * y₂ - y₁ + y₂ ^ 2 - y₂ ≤ 0 := by
    nlinarith [mul_nonneg h1 (by linarith : (0:ℝ) ≤ y₂ - y₁),
      mul_nonneg h1 (by linarith : (0:ℝ) ≤ 1 / 3 - y₂),
      mul_nonneg (by linarith : (0:ℝ) ≤ y₂) (by linarith : (0:ℝ) ≤ 1 / 3 - y₂),
      mul_nonneg (by linarith : (0:ℝ) ≤ y₂ - y₁) (by linarith : (0:ℝ) ≤ 1 / 3 - y₂),
      sq_nonneg (y₁ - y₂), sq_nonneg (3 * y₂ - 1), sq_nonneg (3 * y₁ - 1),
      mul_nonneg h1 (by linarith : (0:ℝ) ≤ 1 / 3 - y₁)]
  have hcube : (0:ℝ) ≤ (1 - y₁) ^ 3 * (1 - y₂) ^ 3 :=
    mul_nonneg (pow_nonneg (by linarith) 3) (pow_nonneg (by linarith) 3)
  rw [paramEdge, paramEdge, paramProfile, paramProfile]
  nlinarith [mul_nonneg (mul_nonneg hcube (by linarith : (0:ℝ) ≤ y₂ - y₁))
    (by linarith : (0:ℝ) ≤ -(54 * y₁ ^ 2 * y₂ ^ 2 + 9 * y₁ ^ 2 * y₂ + y₁ ^ 2 +
      9 * y₁ * y₂ ^ 2 - 8 * y₁ * y₂ - y₁ + y₂ ^ 2 - y₂))]

set_option maxHeartbeats 1000000 in
/-- **The low-interval comparison.**  `c²f ≤ p·g(p)²` for `p ∈ [1/2, 3/5]`. -/
lemma low_comparison {y : ℝ} (hy0 : 0 ≤ y) (hy8 : y ≤ 1 / 8) :
    (2 * paramEdge y - 1) ^ 2 * (3 * paramEdge y ^ 2 - 3 * paramEdge y + 1)
      ≤ paramEdge y * paramProfile y ^ 2 := by
  have hR : (0:ℝ) ≤ 1 + 6 * y - 159 * y ^ 2 + 756 * y ^ 3 - 1521 * y ^ 4
      + 1422 * y ^ 5 - 513 * y ^ 6 := by
    nlinarith [sq_nonneg y, sq_nonneg (y - 1 / 8),
      mul_nonneg hy0 (by linarith : (0:ℝ) ≤ 1 / 8 - y),
      mul_nonneg (mul_nonneg hy0 hy0) (by linarith : (0:ℝ) ≤ 1 / 8 - y),
      mul_nonneg (mul_nonneg hy0 hy0) (mul_nonneg hy0
        (by linarith : (0:ℝ) ≤ 1 / 8 - y))]
  rw [paramEdge, paramProfile]
  nlinarith [mul_nonneg (sq_nonneg y) hR]

/-! ### Feeding a triangle bound through the tilt

The note's paw estimate reads `G ≥ z·t(K₃,W;ν)` with `z = M³`, and the edge
density `s` of `W` under the tilted measure obeys `z²s³ ≥ p⁵` — that is the
fractional edge lemma, squared to stay polynomial.  Given any lower bound `T`
for the tilted triangle density, the two lemmas below turn it into
`p·g(p) ≤ z·T`.

The split is at `s = 2/3`: below it Fisher's theorem supplies the sharp
profile, above it Goodman `s(2s-1)` already suffices, and the two agree at
`s = 2/3` where both equal `2/9`. -/

lemma half_le_paramEdge {y : ℝ} (hy0 : 0 ≤ y) (hy3 : y ≤ 1 / 3) :
    1 / 2 ≤ paramEdge y := by
  rw [paramEdge]; nlinarith

/-- **The Goodman branch of the paw estimate**, for a tilted edge density
`s ≥ 2/3`. -/
lemma paw_scalar_goodman {y : ℝ} (hy0 : 0 ≤ y) (hy8 : y ≤ 1 / 8)
    {s z T : ℝ} (hs : 2 / 3 ≤ s) (hs1 : s ≤ 1) (hz0 : 0 ≤ z)
    (hkey : paramEdge y ^ 5 ≤ z ^ 2 * s ^ 3) (hT : s * (2 * s - 1) ≤ T) :
    paramEdge y * paramProfile y ≤ z * T := by
  have hy3 : y ≤ 1 / 3 := by linarith
  have hp0 : 1 / 2 ≤ paramEdge y := half_le_paramEdge hy0 hy3
  have hg0 : 0 ≤ paramProfile y := paramProfile_nonneg hy0
  have hgg := sq_paramProfile_le hy0 hy3
  have hs0 : (0:ℝ) < s := by linarith
  have hmid : paramEdge y * paramProfile y ≤ z * (s * (2 * s - 1)) := by
    refine le_of_pow_le_pow_left₀ (n := 2) two_ne_zero
      (mul_nonneg hz0 (by nlinarith)) ?_
    -- multiply through by `s`, then use `6g² ≤ p³` and `s ≤ 6(2s-1)²`
    have hsq : s * (paramEdge y * paramProfile y) ^ 2
        ≤ s * (z * (s * (2 * s - 1))) ^ 2 := by
      have h1 : paramEdge y ^ 5 * (2 * s - 1) ^ 2 ≤ z ^ 2 * s ^ 3 * (2 * s - 1) ^ 2 :=
        mul_le_mul_of_nonneg_right hkey (sq_nonneg _)
      have h2 : s * paramProfile y ^ 2 ≤ paramEdge y ^ 3 * (2 * s - 1) ^ 2 := by
        nlinarith [mul_nonneg (by nlinarith : (0:ℝ) ≤ 24 * s ^ 2 - 25 * s + 6)
          (sq_nonneg (paramProfile y)), hgg, sq_nonneg (paramProfile y)]
      nlinarith [h1, h2, sq_nonneg (paramEdge y), pow_pos (by linarith : (0:ℝ) < paramEdge y) 2]
    exact le_of_mul_le_mul_left (by linarith [hsq]) hs0
  calc paramEdge y * paramProfile y ≤ z * (s * (2 * s - 1)) := hmid
    _ ≤ z * T := mul_le_mul_of_nonneg_left hT hz0

/-- **The Fisher branch of the paw estimate**, for a tilted edge density
`s = paramEdge y₂ ≤ 2/3`. -/
lemma paw_scalar_fisher {y₁ y₂ : ℝ} (hy0 : 0 ≤ y₁) (hy8 : y₁ ≤ 1 / 8)
    (h20 : 0 ≤ y₂) (h23 : y₂ ≤ 1 / 3) {z T : ℝ} (hz0 : 0 ≤ z)
    (hzp : z ≤ paramEdge y₁)
    (hkey : paramEdge y₁ ^ 5 ≤ z ^ 2 * paramEdge y₂ ^ 3)
    (hT : paramProfile y₂ ≤ T) :
    paramEdge y₁ * paramProfile y₁ ≤ z * T := by
  have hy3 : y₁ ≤ 1 / 3 := by linarith
  have hp0 : 1 / 2 ≤ paramEdge y₁ := half_le_paramEdge hy0 hy3
  have hs0 : 1 / 2 ≤ paramEdge y₂ := half_le_paramEdge h20 h23
  have hg1 : 0 ≤ paramProfile y₁ := paramProfile_nonneg hy0
  have hg2 : 0 ≤ paramProfile y₂ := paramProfile_nonneg h20
  -- `p ≤ s`, hence `y₁ ≤ y₂`
  have hps : paramEdge y₁ ≤ paramEdge y₂ := by
    have hz2 : z ^ 2 ≤ paramEdge y₁ ^ 2 := by nlinarith
    have hstep : paramEdge y₁ ^ 2 * paramEdge y₁ ^ 3
        ≤ paramEdge y₁ ^ 2 * paramEdge y₂ ^ 3 := by
      calc paramEdge y₁ ^ 2 * paramEdge y₁ ^ 3 = paramEdge y₁ ^ 5 := by ring
        _ ≤ z ^ 2 * paramEdge y₂ ^ 3 := hkey
        _ ≤ paramEdge y₁ ^ 2 * paramEdge y₂ ^ 3 :=
            mul_le_mul_of_nonneg_right hz2
              (pow_nonneg (by linarith : (0:ℝ) ≤ paramEdge y₂) 3)
    have hcube : paramEdge y₁ ^ 3 ≤ paramEdge y₂ ^ 3 :=
      le_of_mul_le_mul_left hstep (pow_pos (by linarith) 2)
    exact le_of_pow_le_pow_left₀ (n := 3) three_ne_zero (by linarith) hcube
  have h12 : y₁ ≤ y₂ := le_of_paramEdge_le hy0 hy8 h20 h23 hps
  have hcross := cross_mono hy0 h12 h23
  have hmid : paramEdge y₁ * paramProfile y₁ ≤ z * paramProfile y₂ := by
    refine le_of_pow_le_pow_left₀ (n := 2) two_ne_zero (mul_nonneg hz0 hg2) ?_
    have hs3 : (0:ℝ) < paramEdge y₂ ^ 3 := by positivity
    refine le_of_mul_le_mul_right ?_ hs3
    have h1 : paramEdge y₁ ^ 5 * paramProfile y₂ ^ 2
        ≤ z ^ 2 * paramEdge y₂ ^ 3 * paramProfile y₂ ^ 2 :=
      mul_le_mul_of_nonneg_right hkey (sq_nonneg _)
    nlinarith [h1, hcross, sq_nonneg (paramEdge y₁), pow_pos
      (by linarith : (0:ℝ) < paramEdge y₁) 2]
  calc paramEdge y₁ * paramProfile y₁ ≤ z * paramProfile y₂ := hmid
    _ ≤ z * T := mul_le_mul_of_nonneg_left hT hz0

end Taeyoung.Methods.Atlas148
