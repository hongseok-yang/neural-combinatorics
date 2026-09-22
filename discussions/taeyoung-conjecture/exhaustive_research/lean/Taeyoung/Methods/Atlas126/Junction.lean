import Taeyoung.Methods.Atlas126.Coefficients
import Taeyoung.Methods.Atlas126.Convex

/-!
# Atlas 126: the quadratic junction plane

The polynomial transition plane `C` is used only through `x = 15/16`.
Approaching `x = 1` linearly changes the Hessian at the high-density contact
and gives a genuine negative residual.  The junction plane below approaches
the high-density plane quadratically and is used on `[15/16,1]`.

This file names the five polynomial candidates used by the scalar convexity
reduction.  Their Bernstein certificates live in `Cert/Junction*`.
-/

namespace Taeyoung.Methods.Atlas126

noncomputable def junctionFace1Target (x d u : ℝ) : ℝ :=
  let p := lowDensity x
  let t := d ^ 2 * u
  scalarResidual p (target p) (betaJ x) (gammaJ x) (lambdaJ x)
    (lowTriangle x) d ((t + p) / 2) t

noncomputable def junctionFace1Constraint0 (x d u : ℝ) : ℝ :=
  let p := lowDensity x
  let t := d ^ 2 * u
  d - (t + p) / 2

noncomputable def junctionFace1Constraint1 (x d u : ℝ) : ℝ :=
  let p := lowDensity x
  let t := d ^ 2 * u
  (t + p) / 2 - (d + p - 1)

noncomputable def junctionFace2Target (x d u : ℝ) : ℝ :=
  let p := lowDensity x
  let t := d ^ 2 * u
  scalarResidual p (target p) (betaJ x) (gammaJ x) (lambdaJ x)
    (lowTriangle x) d d t

noncomputable def junctionFace2Constraint (x d u : ℝ) : ℝ :=
  let p := lowDensity x
  let t := d ^ 2 * u
  (t + p) / 2 - d

noncomputable def junctionFace3Target (x d u : ℝ) : ℝ :=
  let p := lowDensity x
  let t := d ^ 2 * u
  scalarResidual p (target p) (betaJ x) (gammaJ x) (lambdaJ x)
    (lowTriangle x) d t t

noncomputable def junctionFace3Constraint0 (x d u : ℝ) : ℝ :=
  let p := lowDensity x
  let t := d ^ 2 * u
  (t + p) / 2 - t

noncomputable def junctionFace3Constraint1 (x d u : ℝ) : ℝ :=
  let p := lowDensity x
  let t := d ^ 2 * u
  t - (d + p - 1)

noncomputable def junctionFace4Target (x d u : ℝ) : ℝ :=
  let p := lowDensity x
  let a := d + p - 1
  let t := a * u
  scalarResidual p (target p) (betaJ x) (gammaJ x) (lambdaJ x)
    (lowTriangle x) d a t

noncomputable def junctionFace4Constraint0 (x d u : ℝ) : ℝ :=
  d + lowDensity x - 1

noncomputable def junctionFace4Constraint1 (x d u : ℝ) : ℝ :=
  d ^ 2 - (d + lowDensity x - 1) * u

noncomputable def junctionFace4Constraint2 (x d u : ℝ) : ℝ :=
  let p := lowDensity x
  let t := (d + p - 1) * u
  (t + p) / 2 - (d + p - 1)

/-- The lower face is needed only when the quadratic vertex is below it. -/
noncomputable def junctionFace4Constraint3 (x d u : ℝ) : ℝ :=
  let a := d + lowDensity x - 1
  let t := a*u
  2*t*(a-t) - (1-d)*gammaJ x

noncomputable def junctionInteriorTarget (x d u : ℝ) : ℝ :=
  let p := lowDensity x
  let t := d ^ 2 * u
  4 * t ^ 4 - d * (1 - d) * gammaJ x ^ 2 -
    4 * d * t *
      (target p + betaJ x * (d - p) + gammaJ x * (t - d ^ 2) +
        lambdaJ x * (t - lowTriangle x))

noncomputable def junctionInteriorConstraint0 (x d u : ℝ) : ℝ :=
  let t := d ^ 2 * u
  2 * t * (d - t) - (1 - d) * gammaJ x

noncomputable def junctionInteriorConstraint1 (x d u : ℝ) : ℝ :=
  let p := lowDensity x
  let t := d ^ 2 * u
  t * (p - t) - (1 - d) * gammaJ x

noncomputable def junctionInteriorConstraint2 (x d u : ℝ) : ℝ :=
  let p := lowDensity x
  let t := d ^ 2 * u
  (1 - d) * gammaJ x - 2 * t * (d + p - 1 - t)

end Taeyoung.Methods.Atlas126
