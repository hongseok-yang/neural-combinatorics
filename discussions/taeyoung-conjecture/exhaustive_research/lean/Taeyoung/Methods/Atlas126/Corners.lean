import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Atlas 126: the tangency corners

Two of the note's carve-outs are neighbourhoods of an exact contact, where no
subdivision can converge because the residual genuinely vanishes.  Both are
handled by factoring the contact out and certifying the leftover quadratic form.

On the face `a = (t+p)/2` the residual vanishes to second order at the
multipartite point `(d,t) = (p, p(2p-1))`, so in the shifted coordinates
`δ = d - p`, `τ = t - p(2p-1)` it is exactly

```
Φ = A·δ² + B·δτ + C·τ²
```

with `A`, `B`, `C` polynomial.  `quadratic_nonneg` then reduces nonnegativity to
three scalar facts — `A ≥ 0`, `C ≥ 0`, `4AC ≥ B²` — which hold with comfortable
margins on a tube around the contact (`0.59`, `0.10`, `0.23` for a tube of
radius `1/10` at `p ≤ 9/10`).  Outside the tube the residual is bounded away
from zero and ordinary box certificates apply.

The two coefficient relations that make the region-H plane tangent rather than
merely touching are recorded here as `ring` identities; they are the region-H
analogue of `β = 2γρ` in `Slab.lean`.
-/

namespace Taeyoung.Methods.Atlas126

/-! ### The discriminant criterion -/

/-- **A positive semidefinite binary quadratic form is nonnegative.**  The proof
is the completed square `4A(Aδ² + Bδτ + Cτ²) = (2Aδ + Bτ)² + (4AC - B²)τ²`,
with the degenerate case `A = 0` handled separately. -/
theorem quadratic_nonneg {A B C d t : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hdet : B ^ 2 ≤ 4 * A * C) :
    0 ≤ A * d ^ 2 + B * d * t + C * t ^ 2 := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · -- `A = 0` forces `B = 0`
    have hB : B = 0 := by nlinarith [sq_nonneg B, hdet, hA0]
    rw [← hA0, hB]
    simpa using mul_nonneg hC (sq_nonneg t)
  · have key : 4 * A * (A * d ^ 2 + B * d * t + C * t ^ 2)
        = (2 * A * d + B * t) ^ 2 + (4 * A * C - B ^ 2) * t ^ 2 := by ring
    have h1 : 0 ≤ (2 * A * d + B * t) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (4 * A * C - B ^ 2) * t ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg t)
    nlinarith [key, h1, h2, hApos]

/-! ### The region-H coefficients

`γ_H = 2p(9p² - 10p + 3)` and `β_H = p(30p³ - 29p² + 6p + 1)` are not chosen,
they are forced: `β_H` is exactly what makes the plane tangent to the face
`a = (t+p)/2` at the multipartite point. -/

/-- `β_H = 2γ_H·p + p(2p-1)(1-p)(3p-1)`: the tangency relation. -/
theorem betaH_eq (p : ℝ) :
    p * (30 * p ^ 3 - 29 * p ^ 2 + 6 * p + 1)
      = 2 * (2 * p * (9 * p ^ 2 - 10 * p + 3)) * p
        + p * (2 * p - 1) * (1 - p) * (3 * p - 1) := by
  ring

/-- `9p² - 10p + 3 > 0`: the discriminant is `-8`, so completing the square
gives `9(p - 5/9)² + 2/9`. -/
theorem quad_pos (p : ℝ) : 0 < 9 * p ^ 2 - 10 * p + 3 := by
  have h : 9 * p ^ 2 - 10 * p + 3 = 9 * (p - 5 / 9) ^ 2 + 2 / 9 := by ring
  rw [h]
  positivity

/-- Hence `γ_H > 0` on the region. -/
theorem gammaH_pos {p : ℝ} (hp : 0 < p) : 0 < 2 * p * (9 * p ^ 2 - 10 * p + 3) :=
  mul_pos (by linarith) (quad_pos p)

/-! ### The ternary criterion

The `x = 0` contact of region L is an interior critical point of the residual in
all three of `d`, `a`, `t`, with Hessian

```
[ 3/16   1/8  -1/4 ]
[ 1/8    1/2    0  ]
[ -1/4    0     1  ]
```

whose leading minors are `3/16`, `5/64`, `3/64` -- positive definite, so that
contact is nondegenerate too.  Certifying it needs the ternary analogue of
`quadratic_nonneg`, obtained by completing one square and appealing to the
binary case on what is left:

```
a·q = (a·x + u·y + v·z)^2 + (ab - u^2)y^2 + 2(aw - uv)yz + (ac - v^2)z^2.
```
-/

/-- **A positive semidefinite ternary quadratic form is nonnegative.** -/
theorem quadratic3_nonneg {a b c u v w x y z : ℝ} (ha : 0 < a)
    (h1 : 0 ≤ a * b - u ^ 2) (h2 : 0 ≤ a * c - v ^ 2)
    (hdet : (2 * (a * w - u * v)) ^ 2 ≤ 4 * (a * b - u ^ 2) * (a * c - v ^ 2)) :
    0 ≤ a * x ^ 2 + b * y ^ 2 + c * z ^ 2
        + 2 * u * x * y + 2 * v * x * z + 2 * w * y * z := by
  have key : a * (a * x ^ 2 + b * y ^ 2 + c * z ^ 2
        + 2 * u * x * y + 2 * v * x * z + 2 * w * y * z)
      = (a * x + u * y + v * z) ^ 2
        + ((a * b - u ^ 2) * y ^ 2 + (2 * (a * w - u * v)) * y * z
          + (a * c - v ^ 2) * z ^ 2) := by ring
  have hrem : 0 ≤ (a * b - u ^ 2) * y ^ 2 + (2 * (a * w - u * v)) * y * z
      + (a * c - v ^ 2) * z ^ 2 := quadratic_nonneg h1 h2 hdet
  have hsq : 0 ≤ (a * x + u * y + v * z) ^ 2 := sq_nonneg _
  nlinarith [key, hrem, hsq, ha]

/-- A ternary quadratic with two known off-diagonal signs and a bounded third
entry. This avoids computing high-degree principal minors after a constant
change of coordinates makes a local contact diagonally dominant. -/
theorem quadratic3_diagonal_nonneg {a b c u v w e x y z : ℝ}
    (hu : 0 ≤ u) (hv : v ≤ 0) (he : 0 ≤ e)
    (hw0 : -e ≤ w) (hw1 : w ≤ e)
    (ha : 0 ≤ a-u+v) (hb : 0 ≤ b-u-e) (hc : 0 ≤ c+v-e) :
    0 ≤ a*x^2+b*y^2+c*z^2+2*u*x*y+2*v*x*z+2*w*y*z := by
  have hA := mul_nonneg ha (sq_nonneg x)
  have hB := mul_nonneg hb (sq_nonneg y)
  have hC := mul_nonneg hc (sq_nonneg z)
  have hU := mul_nonneg hu (sq_nonneg (x+y))
  have hV := mul_nonneg (neg_nonneg.mpr hv) (sq_nonneg (x-z))
  have hW0 := mul_nonneg (show 0 ≤ (e+w)/2 by linarith) (sq_nonneg (y+z))
  have hW1 := mul_nonneg (show 0 ≤ (e-w)/2 by linarith) (sq_nonneg (y-z))
  nlinarith only [hA,hB,hC,hU,hV,hW0,hW1]

end Taeyoung.Methods.Atlas126
