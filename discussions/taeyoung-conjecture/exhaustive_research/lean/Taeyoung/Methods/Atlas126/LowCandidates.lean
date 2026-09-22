import Taeyoung.Methods.Atlas126.JunctionSlack

/-! Generated definitions for the selected A/C scalar candidates. -/
namespace Taeyoung.Methods.Atlas126

noncomputable def aFace1Target (x d u : ℝ) : ℝ :=
  scalarResidual (lowDensity x) (target (lowDensity x)) (betaA x) (gammaA x) (lambdaA x) (lowTriangle x) d ((d^2*u+lowDensity x)/2) (d^2*u)

noncomputable def aFace1Constraint0 (x d u : ℝ) : ℝ :=
  d-(d^2*u+lowDensity x)/2

noncomputable def aFace1Constraint1 (x d u : ℝ) : ℝ :=
  (d^2*u+lowDensity x)/2-(d+lowDensity x-1)

noncomputable def aFace1Constraint2 (x d u : ℝ) : ℝ :=
  (1-d)*gammaA x-(d^2*u)*(lowDensity x-d^2*u)

noncomputable def aFace2Target (x d u : ℝ) : ℝ :=
  scalarResidual (lowDensity x) (target (lowDensity x)) (betaA x) (gammaA x) (lambdaA x) (lowTriangle x) d d (d^2*u)

noncomputable def aFace2Constraint0 (x d u : ℝ) : ℝ :=
  (d^2*u+lowDensity x)/2-d

noncomputable def aFace2Constraint1 (x d u : ℝ) : ℝ :=
  (1-d)*gammaA x-2*(d^2*u)*(d-d^2*u)

noncomputable def aFace4Target (x d u : ℝ) : ℝ :=
  scalarResidual (lowDensity x) (target (lowDensity x)) (betaA x) (gammaA x) (lambdaA x) (lowTriangle x) d (d+lowDensity x-1) ((d+lowDensity x-1)*u)

noncomputable def aFace4Constraint0 (x d u : ℝ) : ℝ :=
  d+lowDensity x-1

noncomputable def aFace4Constraint1 (x d u : ℝ) : ℝ :=
  d^2-(d+lowDensity x-1)*u

noncomputable def aFace4Constraint2 (x d u : ℝ) : ℝ :=
  ((d+lowDensity x-1)*u+lowDensity x)/2-(d+lowDensity x-1)

noncomputable def aFace4Constraint3 (x d u : ℝ) : ℝ :=
  2*((d+lowDensity x-1)*u)*(d+lowDensity x-1-(d+lowDensity x-1)*u)-(1-d)*gammaA x

noncomputable def aSlackTarget (x d u : ℝ) : ℝ :=
  slackPolynomial (lowDensity x) (target (lowDensity x)) (betaA x) (gammaA x) (lambdaA x) (lowTriangle x) d u

noncomputable def cFace1Target (x d u : ℝ) : ℝ :=
  scalarResidual (lowDensity x) (target (lowDensity x)) (betaC x) (gammaC x) (lambdaC x) (lowTriangle x) d ((d^2*u+lowDensity x)/2) (d^2*u)

noncomputable def cFace1Constraint0 (x d u : ℝ) : ℝ :=
  d-(d^2*u+lowDensity x)/2

noncomputable def cFace1Constraint1 (x d u : ℝ) : ℝ :=
  (d^2*u+lowDensity x)/2-(d+lowDensity x-1)

noncomputable def cFace1Constraint2 (x d u : ℝ) : ℝ :=
  (1-d)*gammaC x-(d^2*u)*(lowDensity x-d^2*u)

noncomputable def cFace2Target (x d u : ℝ) : ℝ :=
  scalarResidual (lowDensity x) (target (lowDensity x)) (betaC x) (gammaC x) (lambdaC x) (lowTriangle x) d d (d^2*u)

noncomputable def cFace2Constraint0 (x d u : ℝ) : ℝ :=
  (d^2*u+lowDensity x)/2-d

noncomputable def cFace2Constraint1 (x d u : ℝ) : ℝ :=
  (1-d)*gammaC x-2*(d^2*u)*(d-d^2*u)

noncomputable def cFace4Target (x d u : ℝ) : ℝ :=
  scalarResidual (lowDensity x) (target (lowDensity x)) (betaC x) (gammaC x) (lambdaC x) (lowTriangle x) d (d+lowDensity x-1) ((d+lowDensity x-1)*u)

noncomputable def cFace4Constraint0 (x d u : ℝ) : ℝ :=
  d+lowDensity x-1

noncomputable def cFace4Constraint1 (x d u : ℝ) : ℝ :=
  d^2-(d+lowDensity x-1)*u

noncomputable def cFace4Constraint2 (x d u : ℝ) : ℝ :=
  ((d+lowDensity x-1)*u+lowDensity x)/2-(d+lowDensity x-1)

noncomputable def cFace4Constraint3 (x d u : ℝ) : ℝ :=
  2*((d+lowDensity x-1)*u)*(d+lowDensity x-1-(d+lowDensity x-1)*u)-(1-d)*gammaC x

noncomputable def cSlackTarget (x d u : ℝ) : ℝ :=
  slackPolynomial (lowDensity x) (target (lowDensity x)) (betaC x) (gammaC x) (lambdaC x) (lowTriangle x) d u

end Taeyoung.Methods.Atlas126
