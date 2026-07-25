import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Scalar data for the intermediate-region proof

The definitions in this file follow the intermediate-region reduction of
`paper_new_region2_v2.tex` (§5–§7).  Keeping the admissibility hypotheses in one structure prevents
the analytic scalar files from silently changing the domain.
-/

open Set

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

/-- The exact upper leading_eigenvalue allowed by the forced-variance argument. -/
noncomputable def leadingEigenvalueRadius (q : Real) : Real :=
  (Real.sqrt (q ^ 2 + 4 * q) - q) / 2

/-- Parameters in the scalar theorem's admissible domain. -/
structure AdmissibleParams where
  q : Real
  alpha : Real
  m : Nat
  q_gt_third : 1 / 3 < q
  q_lt_half : q < 1 / 2
  alpha_gt_q : q < alpha
  alpha_le_radius : alpha <= leadingEigenvalueRadius q
  m_odd : Odd m
  m_ge_nine : 9 <= m

namespace AdmissibleParams

variable (P : AdmissibleParams)

def p : Real := 1 - P.q
def d : Real := P.alpha - P.q
def e : Real := 1 - 2 * P.alpha

noncomputable def L : Real :=
  Real.sqrt (P.p * P.q - P.alpha ^ 2)

noncomputable def f : Real := P.alpha - P.L

noncomputable def k (lambda : Real) : Real :=
  (P.p ^ (P.m - 1) - lambda ^ (P.m - 1)) / (P.p + lambda)

noncomputable def A : Real :=
  2 * P.L ^ (P.m - 2) + P.m * P.k P.alpha

noncomputable def B : Real :=
  2 * P.L ^ (P.m - 2) + P.m * P.k P.L

noncomputable def R : Real :=
  P.alpha ^ P.m + P.L ^ P.m - P.p * P.q ^ (P.m - 1)

noncomputable def C : Real :=
  P.B * P.f * Real.sqrt (2 * P.alpha) * P.e ^ 2 /
    (4 * P.alpha ^ 2)

noncomputable def xi : Real :=
  4 * P.alpha ^ 2 * P.d / P.e ^ 2

noncomputable def rho : Real :=
  (P.A / P.B) *
    (Real.sqrt P.alpha / (2 * Real.sqrt 2 * P.f))

def x : Real := P.alpha / P.p
def tau : Real := P.q / P.alpha

/-- The eigenvalue-gap coordinate used by the finite certificates. -/
def kappa : Real := P.d / P.e

end AdmissibleParams

/-- The convex objective whose minimum is the Envelope envelope_value. -/
noncomputable def envelopeObjective (xi rho v : Real) : Real :=
  rho * v ^ 2 + max (xi - v + v ^ 2) 0

/-- The paper's Envelope envelope_value, defined as the actual infimum over `[0,1]`.
Compactness and attainment are proved in `Envelope.lean`. -/
noncomputable def psi (xi rho : Real) : Real :=
  sInf (envelopeObjective xi rho '' Icc (0 : Real) 1)

/-- The dual objective used by the scalar branch analysis. -/
noncomputable def envelopeDual (xi rho lambda : Real) : Real :=
  lambda * xi - lambda ^ 2 / (4 * (rho + lambda))

/-- Transition point in the explicit piecewise formula for `psi`. -/
noncomputable def xiCritical (rho : Real) : Real :=
  (2 * rho + 1) / (4 * (rho + 1) ^ 2)

/-- The lower root of `v - v² = xi`. -/
noncomputable def vMinus (xi : Real) : Real :=
  (1 - Real.sqrt (1 - 4 * xi)) / 2

end OddCycleBound.IntermediateRegion.Scalar
