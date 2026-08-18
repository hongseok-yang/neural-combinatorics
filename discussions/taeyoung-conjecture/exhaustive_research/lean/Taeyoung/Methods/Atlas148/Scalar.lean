import Mathlib.Tactic

/-!
# Atlas 148: the scalar supporting line of the high-density interval

`notes/atlas148_paw_bias_hilbert_projection.tex` reduces the high interval
`p ∈ [3/5, 1]` to one pointwise inequality between real numbers.  Writing
`q = 1-p`, `c = 2p-1`, `f = 3p²-3p+1`, the two quantities that appear in the
edge integrand are

```
z = √(d(x)d(y)),     s = S(x,y) = ∫ W(x,·)W(y,·),
```

and the note's Cauchy--Schwarz and product bounds confine them to
`(2z-1)₊ ≤ s ≤ z`, `0 ≤ z ≤ 1`.  The inequality to be proved is

```
F_p(z,s) := s(p²z + qz² - qs)  ≥  ℓ_p(z) := cf + m_p(z - p),
```

with `m_p = -2p³ + 15p² - 14p + 4`.  Integrating it against `W dμ²` and using
`∫∫W·√(d(x)d(y)) ≥ p²` is what gives the note's linear estimate
`p²G - qΔ ≥ pcf`.

The line `ℓ_p` is the tangent to `s = 2z-1` branch at `z = p`, which is why
that branch factors exactly:

```
F_p(z, 2z-1) - ℓ_p(z) = -(z-p)²(2p² + 2pz - 9p - 2z + 5),
```

the bracket being nonpositive for `z ≥ 1/2` because it decreases in `z` and is
`2(p²-4p+2) ≤ 0` at `z = 1/2` — the step that forces `p ≥ 2-√2`, and hence the
note's split at `3/5`.

The other branch, `s = z`, has no such factorization: `F_p(z,z) - ℓ_p(z)` is
strictly positive on the rectangle except at the corner `(p,z) = (1,1)`, with
an interior minimum of about `0.0044` along `p = 3/5`.  The note certifies it
with four Bernstein boxes in `z`.  Two suffice — split at `z = 7/10` and keep
the native bidegree `(4,3)` — so what appears below is forty nonnegative
rational coefficients rather than eighty.  Each box is closed by `linarith`
against the twenty products `aⁱ(1-a)⁴⁻ⁱbʲ(1-b)³⁻ʲ`, where `a` and `b` are the
affine box coordinates; no `Bernstein` certificate structure is needed.

Both branches are then combined by concavity of `F_p(z, ·)`, which is a
quadratic in `s` with leading coefficient `-q ≤ 0`, so on any interval it
dominates its chord and hence the smaller endpoint value.
-/

namespace Taeyoung.Methods.Atlas148

/-- `m_p`, the slope of the supporting line. -/
def slope (p : ℝ) : ℝ := -2 * p ^ 3 + 15 * p ^ 2 - 14 * p + 4

/-- `ℓ_p(z) = cf + m_p(z - p)`: the tangent at `z = p` to the lower branch. -/
def line (p z : ℝ) : ℝ :=
  (2 * p - 1) * (3 * p ^ 2 - 3 * p + 1) + slope p * (z - p)

/-- `F_p(z,s) = s(p²z + qz² - qs)`: the edge integrand of the note. -/
def edgeFn (p z s : ℝ) : ℝ := s * (p ^ 2 * z + (1 - p) * z ^ 2 - (1 - p) * s)

/-! ### Two facts about the coefficients -/

/-- `p² - 4p + 2 ≤ 0` on `[3/5, 1]`; the root `2-√2 ≈ 0.5858` is what puts the
note's interval split at `3/5`. -/
lemma quad_nonpos {p : ℝ} (hp0 : 3 / 5 ≤ p) (hp1 : p ≤ 1) :
    p ^ 2 - 4 * p + 2 ≤ 0 := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ p - 3 / 5) (by linarith : (0:ℝ) ≤ 1 - p)]

/-- The slope is nonnegative on `[3/5, 1]`, so `ℓ_p` is nondecreasing. -/
lemma slope_nonneg {p : ℝ} (hp0 : 3 / 5 ≤ p) (hp1 : p ≤ 1) : 0 ≤ slope p := by
  rw [slope]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ p - 3 / 5) (by linarith : (0:ℝ) ≤ 1 - p),
    sq_nonneg (p - 1), sq_nonneg p]

/-- The slope is at most `3` on `[3/5, 1]`. -/
lemma slope_le_three {p : ℝ} (hp0 : 3 / 5 ≤ p) (hp1 : p ≤ 1) : slope p ≤ 3 := by
  rw [slope]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - p)
    (by nlinarith : (0:ℝ) ≤ -2 * p ^ 2 + 13 * p - 1)]

/-- The intercept `cf` lies in `[0,1]` on `[3/5, 1]`. -/
lemma cf_bounds {p : ℝ} (hp0 : 3 / 5 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ (2 * p - 1) * (3 * p ^ 2 - 3 * p + 1) ∧
      (2 * p - 1) * (3 * p ^ 2 - 3 * p + 1) ≤ 1 := by
  have hf0 : (0:ℝ) ≤ 3 * p ^ 2 - 3 * p + 1 := by nlinarith [sq_nonneg (2 * p - 1)]
  have hf1 : 3 * p ^ 2 - 3 * p + 1 ≤ 1 := by nlinarith
  constructor
  · exact mul_nonneg (by linarith) hf0
  · nlinarith

/-! ### The lower branch, `s = (2z-1)₊` -/

/-- Below `z = 1/2` the line is already nonpositive, so the vanishing branch
value `F_p(z,0) = 0` clears it. -/
lemma line_nonpos_of_le_half {p z : ℝ} (hp0 : 3 / 5 ≤ p) (hp1 : p ≤ 1)
    (hz : z ≤ 1 / 2) : line p z ≤ 0 := by
  have hm := slope_nonneg hp0 hp1
  have hq := quad_nonpos hp0 hp1
  have hhalf : line p (1 / 2) ≤ 0 := by
    rw [line, slope]
    nlinarith [sq_nonneg (2 * p - 1), hq]
  have hmono : line p z ≤ line p (1 / 2) := by
    rw [line, line]
    nlinarith [mul_nonneg hm (by linarith : (0:ℝ) ≤ 1 / 2 - z)]
  linarith

/-- Above `z = 1/2` the lower branch meets the line with a perfect square. -/
lemma line_le_edgeFn_bot {p z : ℝ} (hp0 : 3 / 5 ≤ p) (hp1 : p ≤ 1)
    (hz : 1 / 2 ≤ z) : line p z ≤ edgeFn p z (2 * z - 1) := by
  have hbr : 2 * p ^ 2 + 2 * p * z - 9 * p - 2 * z + 5 ≤ 0 := by
    have hq := quad_nonpos hp0 hp1
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ z - 1 / 2)
      (by linarith : (0:ℝ) ≤ 1 - p)]
  rw [line, slope, edgeFn]
  nlinarith [mul_nonneg (sq_nonneg (z - p)) (by linarith : (0:ℝ) ≤
    -(2 * p ^ 2 + 2 * p * z - 9 * p - 2 * z + 5))]

/-! ### The upper branch, `s = z`

Two Bernstein boxes in `z`, split at `7/10`, at the native bidegree `(4,3)`.
The box coordinates are `a = (5p-3)/2` with `1 - a = (5-5p)/2`, and `b` the
affine coordinate of `z` in its box. -/

set_option maxHeartbeats 1600000 in
lemma line_le_edgeFn_top_low {p z : ℝ} (hp0 : 3 / 5 ≤ p) (hp1 : p ≤ 1)
    (hz0 : 0 ≤ z) (hz : z ≤ 7 / 10) : line p z ≤ edgeFn p z z := by
  have ha : (0:ℝ) ≤ (5 * p - 3) / 2 := by linarith
  have ha' : (0:ℝ) ≤ (5 - 5 * p) / 2 := by linarith
  have hb : (0:ℝ) ≤ 10 * z / 7 := by linarith
  have hb' : (0:ℝ) ≤ (7 - 10 * z) / 7 := by linarith
  rw [line, slope, edgeFn]
  linarith [
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 0) (pow_nonneg ha' 4)) (pow_nonneg hb 0)) (pow_nonneg hb' 3),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 0) (pow_nonneg ha' 4)) (pow_nonneg hb 1)) (pow_nonneg hb' 2),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 0) (pow_nonneg ha' 4)) (pow_nonneg hb 2)) (pow_nonneg hb' 1),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 0) (pow_nonneg ha' 4)) (pow_nonneg hb 3)) (pow_nonneg hb' 0),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 1) (pow_nonneg ha' 3)) (pow_nonneg hb 0)) (pow_nonneg hb' 3),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 1) (pow_nonneg ha' 3)) (pow_nonneg hb 1)) (pow_nonneg hb' 2),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 1) (pow_nonneg ha' 3)) (pow_nonneg hb 2)) (pow_nonneg hb' 1),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 1) (pow_nonneg ha' 3)) (pow_nonneg hb 3)) (pow_nonneg hb' 0),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 2) (pow_nonneg ha' 2)) (pow_nonneg hb 0)) (pow_nonneg hb' 3),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 2) (pow_nonneg ha' 2)) (pow_nonneg hb 1)) (pow_nonneg hb' 2),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 2) (pow_nonneg ha' 2)) (pow_nonneg hb 2)) (pow_nonneg hb' 1),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 2) (pow_nonneg ha' 2)) (pow_nonneg hb 3)) (pow_nonneg hb' 0),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 3) (pow_nonneg ha' 1)) (pow_nonneg hb 0)) (pow_nonneg hb' 3),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 3) (pow_nonneg ha' 1)) (pow_nonneg hb 1)) (pow_nonneg hb' 2),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 3) (pow_nonneg ha' 1)) (pow_nonneg hb 2)) (pow_nonneg hb' 1),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 3) (pow_nonneg ha' 1)) (pow_nonneg hb 3)) (pow_nonneg hb' 0),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 4) (pow_nonneg ha' 0)) (pow_nonneg hb 0)) (pow_nonneg hb' 3),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 4) (pow_nonneg ha' 0)) (pow_nonneg hb 1)) (pow_nonneg hb' 2),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 4) (pow_nonneg ha' 0)) (pow_nonneg hb 2)) (pow_nonneg hb' 1),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 4) (pow_nonneg ha' 0)) (pow_nonneg hb 3)) (pow_nonneg hb' 0)]

set_option maxHeartbeats 1600000 in
lemma line_le_edgeFn_top_high {p z : ℝ} (hp0 : 3 / 5 ≤ p) (hp1 : p ≤ 1)
    (hz : 7 / 10 ≤ z) (hz1 : z ≤ 1) : line p z ≤ edgeFn p z z := by
  have ha : (0:ℝ) ≤ (5 * p - 3) / 2 := by linarith
  have ha' : (0:ℝ) ≤ (5 - 5 * p) / 2 := by linarith
  have hb : (0:ℝ) ≤ (10 * z - 7) / 3 := by linarith
  have hb' : (0:ℝ) ≤ (10 - 10 * z) / 3 := by linarith
  rw [line, slope, edgeFn]
  linarith [
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 0) (pow_nonneg ha' 4)) (pow_nonneg hb 0)) (pow_nonneg hb' 3),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 0) (pow_nonneg ha' 4)) (pow_nonneg hb 1)) (pow_nonneg hb' 2),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 0) (pow_nonneg ha' 4)) (pow_nonneg hb 2)) (pow_nonneg hb' 1),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 0) (pow_nonneg ha' 4)) (pow_nonneg hb 3)) (pow_nonneg hb' 0),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 1) (pow_nonneg ha' 3)) (pow_nonneg hb 0)) (pow_nonneg hb' 3),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 1) (pow_nonneg ha' 3)) (pow_nonneg hb 1)) (pow_nonneg hb' 2),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 1) (pow_nonneg ha' 3)) (pow_nonneg hb 2)) (pow_nonneg hb' 1),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 1) (pow_nonneg ha' 3)) (pow_nonneg hb 3)) (pow_nonneg hb' 0),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 2) (pow_nonneg ha' 2)) (pow_nonneg hb 0)) (pow_nonneg hb' 3),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 2) (pow_nonneg ha' 2)) (pow_nonneg hb 1)) (pow_nonneg hb' 2),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 2) (pow_nonneg ha' 2)) (pow_nonneg hb 2)) (pow_nonneg hb' 1),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 2) (pow_nonneg ha' 2)) (pow_nonneg hb 3)) (pow_nonneg hb' 0),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 3) (pow_nonneg ha' 1)) (pow_nonneg hb 0)) (pow_nonneg hb' 3),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 3) (pow_nonneg ha' 1)) (pow_nonneg hb 1)) (pow_nonneg hb' 2),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 3) (pow_nonneg ha' 1)) (pow_nonneg hb 2)) (pow_nonneg hb' 1),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 3) (pow_nonneg ha' 1)) (pow_nonneg hb 3)) (pow_nonneg hb' 0),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 4) (pow_nonneg ha' 0)) (pow_nonneg hb 0)) (pow_nonneg hb' 3),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 4) (pow_nonneg ha' 0)) (pow_nonneg hb 1)) (pow_nonneg hb' 2),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 4) (pow_nonneg ha' 0)) (pow_nonneg hb 2)) (pow_nonneg hb' 1),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 4) (pow_nonneg ha' 0)) (pow_nonneg hb 3)) (pow_nonneg hb' 0)]

lemma line_le_edgeFn_top {p z : ℝ} (hp0 : 3 / 5 ≤ p) (hp1 : p ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : line p z ≤ edgeFn p z z := by
  rcases le_or_gt z (7 / 10) with hz | hz
  · exact line_le_edgeFn_top_low hp0 hp1 hz0 hz
  · exact line_le_edgeFn_top_high hp0 hp1 hz.le hz1

/-! ### Concavity in `s`, and the pointwise inequality -/

/-- `F_p(z, ·)` is a quadratic with leading coefficient `-q ≤ 0`, so on any
interval it dominates its chord, hence the smaller endpoint value. -/
lemma line_le_edgeFn_of_endpoints {p z s s₀ s₁ : ℝ} (hp1 : p ≤ 1)
    (h0 : s₀ ≤ s) (h1 : s ≤ s₁)
    (e0 : line p z ≤ edgeFn p z s₀) (e1 : line p z ≤ edgeFn p z s₁) :
    line p z ≤ edgeFn p z s := by
  rcases eq_or_lt_of_le (h0.trans h1) with heq | hlt
  · rw [← heq] at h1
    rw [le_antisymm h1 h0]
    exact e0
  · rw [edgeFn] at e0 e1 ⊢
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s₁ - s) (by linarith : (0:ℝ) ≤
        s₀ * (p ^ 2 * z + (1 - p) * z ^ 2 - (1 - p) * s₀) - line p z),
      mul_nonneg (by linarith : (0:ℝ) ≤ s - s₀) (by linarith : (0:ℝ) ≤
        s₁ * (p ^ 2 * z + (1 - p) * z ^ 2 - (1 - p) * s₁) - line p z),
      mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - p)
        (by linarith : (0:ℝ) ≤ s - s₀)) (by linarith : (0:ℝ) ≤ s₁ - s),
      sub_pos.mpr hlt]

/-- **The scalar core of the high interval.**  For `p ∈ [3/5,1]`, `z ∈ [0,1]`
and `(2z-1)₊ ≤ s ≤ z`, the edge integrand dominates the supporting line. -/
theorem line_le_edgeFn {p z s : ℝ} (hp0 : 3 / 5 ≤ p) (hp1 : p ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hs0 : 0 ≤ s) (hs1 : 2 * z - 1 ≤ s) (hs2 : s ≤ z) :
    line p z ≤ edgeFn p z s := by
  have htop := line_le_edgeFn_top hp0 hp1 hz0 hz1
  rcases le_or_gt z (1 / 2) with hz | hz
  · have hbot : line p z ≤ edgeFn p z 0 := by
      rw [edgeFn, zero_mul]
      exact line_nonpos_of_le_half hp0 hp1 hz
    exact line_le_edgeFn_of_endpoints hp1 hs0 hs2 hbot htop
  · exact line_le_edgeFn_of_endpoints hp1 hs1 hs2
      (line_le_edgeFn_bot hp0 hp1 hz.le) htop

end Taeyoung.Methods.Atlas148
