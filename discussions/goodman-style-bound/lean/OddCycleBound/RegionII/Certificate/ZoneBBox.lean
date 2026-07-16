import OddCycleBound.RegionII.Certificate.ChartIntervals
import OddCycleBound.RegionII.Certificate.Soundness

/-!
# Real semantics and evidence for Zone-B certificate boxes

This module gives names to the exact rational quantities computed by
`checkBVerified` and extracts a proposition-valued witness from a successful
Boolean check.  Later modules prove that these endpoint quantities enclose
the corresponding real functions.
-/

noncomputable section

namespace OddCycleBound.RegionII.Certificate

open OddCycleBound.RegionII.Scalar

def bXMin (b : RatBox) : ℚ := chartXQ b.e2 b.k2
def bXMax (b : RatBox) : ℚ := chartXQ b.e1 b.k1
def bLamMin (b : RatBox) : ℚ := 1 - bXMax b
def bAMin (b : RatBox) : ℚ := bXMin b * (1 + b.k2) / b.k2
def bAMax (b : RatBox) : ℚ := bXMax b * (1 + b.k1) / b.k1
def bL2Up (b : RatBox) : ℚ := 2 * b.e2 / (1 - b.e2)
def bLUp (b : RatBox) : ℚ := sqrtUpB (bL2Up b)
def bL14Up (b : RatBox) : ℚ := min 1 (bL2Up b ^ 7)
def bTRho (b : RatBox) : ℚ := (1737 / 100) * (1 + b.k1) * b.e1
def bRhoLo (b : RatBox) : ℚ := (1 - expNegUpB (bTRho b)) / 4
def bEpsUp (b : RatBox) : ℚ :=
  min (1 / 4) (b.e2 /
    (4 * (1 - b.e2) ^ 2 * b.k1 * (1 + bRhoLo b)))
def bRootOneMinusE (b : RatBox) : ℚ := sqrtLoB (1 - b.e2)
def bPiLo (b : RatBox) : ℚ :=
  bRootOneMinusE b * (1 - bLUp b) * (1 - bL14Up b) *
    (1 - bEpsUp b) / (1 + bLUp b)
def bLambdaUp (b : RatBox) : ℚ :=
  bXMax b ^ 13 * bL2Up b ^ 6 * bLUp b * (1 - b.e1) ^ 2 /
    (15 * b.e1)
def bK1Up (b : RatBox) : ℚ :=
  bXMax b ^ 14 * max 0 (14 - bAMin b) / 15
def bOnlyK14 (b : RatBox) : Prop :=
  bAMax b < 14 ∧ 15 * (14 - bAMax b) * bLamMin b >= bAMax b + 1

instance (b : RatBox) : Decidable (bOnlyK14 b) := by
  unfold bOnlyK14
  infer_instance
def bPhiMin (b : RatBox) : ℚ :=
  2 * (1 - b.e2) * b.e1 * (1 + b.k2) ^ 2 /
    (b.k2 * (1 + b.e2 + 2 * b.k2 * b.e2) ^ 2)
def bDisc (b : RatBox) : ℚ := bPhiMin b ^ 2 + 4 * bPhiMin b
def bDiscLo (b : RatBox) : ℚ := sqrtLoB (bDisc b)
def bWLo (b : RatBox) : ℚ := max 0 ((bDiscLo b - bPhiMin b) / 2)
def bK2Up (b : RatBox) : ℚ := expNegUpB (bPhiMin b + 2 * bWLo b)

inductive BMaximumEvidence (box : RatBox) : Prop where
  | endpoint
      (gate : bOnlyK14 box)
      (battle : bPiLo box >= bK1Up box / (bXMin box * bXMin box) +
        bLambdaUp box)
  | interior
      (gate : ¬ bOnlyK14 box)
      (sqrtDisc : sqrtBracketOK (bDisc box) (bDiscLo box)
        (sqrtUpB (bDisc box)) = true)
      (battle : bPiLo box >=
        max (bK1Up box) (bK2Up box) / (bXMin box * bXMin box) +
          bLambdaUp box)

structure BVerifiedEvidence (box : RatBox) : Prop where
  sqrtL : sqrtBracketOK (bL2Up box) (sqrtLoB (bL2Up box))
    (bLUp box) = true
  lUp_lt_one : bLUp box < 1
  sqrtOneMinusE : sqrtBracketOK (1 - box.e2) (bRootOneMinusE box)
    (sqrtUpB (1 - box.e2)) = true
  piLo_pos : 0 < bPiLo box
  maximum : BMaximumEvidence box

lemma checkBVerified_evidence {box : RatBox}
    (hcheck : checkBVerified box = true) : BVerifiedEvidence box := by
  have hnorm :
      (sqrtBracketOK (bL2Up box) (sqrtLoB (bL2Up box)) (bLUp box) = true ∧
        bLUp box < 1) ∧
      sqrtBracketOK (1 - box.e2) (bRootOneMinusE box)
        (sqrtUpB (1 - box.e2)) = true ∧
      0 < bPiLo box ∧
      (if bOnlyK14 box then
        bPiLo box >= bK1Up box / (bXMin box * bXMin box) + bLambdaUp box
       else
        sqrtBracketOK (bDisc box) (bDiscLo box)
          (sqrtUpB (bDisc box)) = true ∧
        bPiLo box >= max (bK1Up box) (bK2Up box) /
          (bXMin box * bXMin box) + bLambdaUp box) := by
    simpa [checkBVerified, bXMin, bXMax, bLamMin, bAMin, bAMax,
      bL2Up, bLUp, bL14Up, bTRho, bRhoLo, bEpsUp,
      bRootOneMinusE, bPiLo, bLambdaUp, bK1Up, bOnlyK14,
      bPhiMin, bDisc, bDiscLo, bWLo, bK2Up, not_le, pow_two] using hcheck
  refine
    { sqrtL := hnorm.1.1
      lUp_lt_one := hnorm.1.2
      sqrtOneMinusE := hnorm.2.1
      piLo_pos := hnorm.2.2.1
      maximum := ?_ }
  by_cases hgate : bOnlyK14 box
  · exact .endpoint hgate (by simpa [hgate] using hnorm.2.2.2)
  · have htail :
        sqrtBracketOK (bDisc box) (bDiscLo box)
            (sqrtUpB (bDisc box)) = true ∧
          bPiLo box >= max (bK1Up box) (bK2Up box) /
            (bXMin box * bXMin box) + bLambdaUp box := by
      simpa [hgate] using hnorm.2.2.2
    exact .interior hgate htail.1 htail.2

structure BBoxContext (P : AdmissibleParams) (box : RatBox) : Prop where
  point : box.Contains P.e P.kappa
  placed : wellPlacedB box = true

end OddCycleBound.RegionII.Certificate
