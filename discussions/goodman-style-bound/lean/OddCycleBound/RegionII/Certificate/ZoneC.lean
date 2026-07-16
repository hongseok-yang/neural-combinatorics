import OddCycleBound.RegionII.Certificate.ZoneB

/-! # Exact moderate Zone-C certificate checker -/

namespace OddCycleBound.RegionII.Certificate

def sqrtLoC (x : ℚ) : ℚ := sqrtLo x (10 ^ 30)
def sqrtUpC (x : ℚ) : ℚ := sqrtUp x (10 ^ 30)

structure CBoxData extends RatBox where
  aLo : ℚ
  aUp : ℚ
  dLo : ℚ
  dUp : ℚ
  qLo : ℚ
  qUp : ℚ
  pLo : ℚ
  pUp : ℚ
  xLo : ℚ
  xUp : ℚ
  sLo : ℚ
  sUp : ℚ
  l2Lo : ℚ
  l2Up : ℚ
  yUp : ℚ
  fLo : ℚ
  fUp : ℚ
  xiLo : ℚ
  xiUp : ℚ
  x14Lo : ℚ
  x14Up : ℚ
  y14Up : ℚ
  uLo : ℚ
  g2Lo : ℚ
  rhoLoUp : ℚ
  rhoLoLo : ℚ
  cI : ℚ
  cII : ℚ
  cI0 : ℚ
  sqrtOK : Bool

def cL2Floor (b : RatBox) : ℚ :=
  max 0 (((1 - b.e2) / 2) * b.e1 -
    (b.k2 * b.e2) * (b.k2 * b.e2 + b.e2))

def cL2Ceil (b : RatBox) : ℚ :=
  min (((1 - b.e1) / 2) * b.e2)
    ((((1 - b.e1) / 2) - b.k1 * b.e1) ^ 2)

def cLLo (b : RatBox) : ℚ := sqrtLoC (cL2Floor b)
def cLRawUp (b : RatBox) : ℚ := sqrtUpC (cL2Ceil b)
def cLUp (b : RatBox) : ℚ :=
  min (cLRawUp b) (((1 - b.e1) / 2) - b.k1 * b.e1)

def cQLo (b : RatBox) : ℚ :=
  max (((1 - b.e2) / 2) - b.k2 * b.e2) (1 / 3)

def cQUp (b : RatBox) : ℚ :=
  ((1 - b.e1) / 2) - b.k1 * b.e1

def cPLo (b : RatBox) : ℚ := 1 - cQUp b
def cPUp (b : RatBox) : ℚ := 1 - cQLo b
def cSLo (b : RatBox) : ℚ := cQLo b / cPUp b
def cSUp (b : RatBox) : ℚ := cQUp b / cPLo b

def cYUp (b : RatBox) : ℚ :=
  min (min (cLUp b / cPLo b) (1 / 2)) (cSUp b)

def cYSUp (b : RatBox) : ℚ :=
  min (roundUp (cYUp b / cSLo b) (10 ^ 6)) 1

def makeCBox (b : RatBox) : CBoxData :=
  let aLo := (1 - b.e2) / 2
  let aUp := (1 - b.e1) / 2
  let dLo := b.k1 * b.e1
  let dUp := b.k2 * b.e2
  let qLo := max (aLo - dUp) (1 / 3)
  let qUp := aUp - dLo
  let pLo := 1 - qUp
  let pUp := 1 - qLo
  let xLo := chartXQ b.e2 b.k2
  let xUp := chartXQ b.e1 b.k1
  let sLo := qLo / pUp
  let sUp := qUp / pLo
  let l2Floor := cL2Floor b
  let l2Ceil := cL2Ceil b
  let lLo := cLLo b
  let lRawUp := cLRawUp b
  let lUp := cLUp b
  let yUp := min (min (lUp / pLo) (1 / 2)) sUp
  let ell2Lo := l2Floor / (aUp ^ 2)
  let ell2Up := min (l2Ceil / (aLo ^ 2)) 1
  let deltaLo := (1 - 3 * b.e2) / 6
  let fLo := max (aLo - lUp) (dLo + deltaLo)
  let fUp := aUp - lLo
  let xiLo := (1 - b.e2) ^ 2 * b.k1 / b.e2
  let xiUp := min 1 ((1 - b.e1) ^ 2 * b.k2 / b.e1)
  let x14Lo := roundDown xLo (10 ^ 6) ^ 14
  let x14Up := min 1 (roundUp xUp (10 ^ 6) ^ 14)
  let y14Up := min 1 (roundUp yUp (10 ^ 6) ^ 14)
  let uLo := 1 - xUp
  let ysUp := cYSUp b
  let g2Lo := ell2Lo * (1 - ysUp ^ 13)
  let sqrtALo := sqrtLoC aLo
  let sqrtAUp := sqrtUpC aUp
  let sqrtTwoLo := sqrtLoC 2
  let sqrtTwoUp := sqrtUpC 2
  let rhoLoUp := (1 - x14Lo) * sqrtAUp / (2 * sqrtTwoLo * fLo * (1 + xLo))
  let rhoLoLo := (1 - x14Up) * sqrtALo / (2 * sqrtTwoUp * fUp * (1 + xUp))
  let cI := 2 * (1 - x14Up) * (1 - y14Up) * b.k1 ^ 2 * (1 + 4 * xiLo) /
    ((1 + xUp) * (1 + yUp) * (1 + 2 * xiLo))
  let sqrtTwiceALo := sqrtLoC (2 * aLo)
  let cII := sqrtTwiceALo * (1 - y14Up) * fLo * dLo * (4 * xiLo + 1) /
    (aUp ^ 3 * (1 + yUp) * (4 * xiLo + 2))
  let cI0 := 2 * (1 - x14Up) * (1 - y14Up) / ((1 + xUp) * (1 + yUp))
  let sqrtOK :=
    sqrtBracketOK l2Floor lLo (sqrtUpC l2Floor) &&
    sqrtBracketOK l2Ceil (sqrtLoC l2Ceil) lRawUp &&
    sqrtBracketOK aLo sqrtALo (sqrtUpC aLo) &&
    sqrtBracketOK aUp (sqrtLoC aUp) sqrtAUp &&
    sqrtBracketOK 2 sqrtTwoLo sqrtTwoUp &&
    sqrtBracketOK (2 * aLo) sqrtTwiceALo (sqrtUpC (2 * aLo))
  { toRatBox := b, aLo, aUp, dLo, dUp, qLo, qUp, pLo, pUp, xLo, xUp, sLo, sUp,
    l2Lo := ell2Lo, l2Up := ell2Up, yUp, fLo, fUp, xiLo, xiUp, x14Lo,
    x14Up, y14Up, uLo, g2Lo, rhoLoUp, rhoLoLo, cI, cII, cI0, sqrtOK }

def CBoxData.cLo (b : CBoxData) : ℚ :=
  if 2 * b.rhoLoUp * b.xiUp ≤ 1 then b.cI
  else if 2 * b.rhoLoLo * b.xiLo > 1 then b.cII
  else min b.cI b.cII

def CBoxData.mPlus (b : CBoxData) : Nat :=
  let g2p := b.g2Lo - b.g2Lo ^ 2 / 2
  let raw := if g2p > 0 then max 15 (3 + (Rat.floor (b.qLo * g2p / b.dUp)).toNat) else 15
  min raw 500000

def cBattleHeadQ (b : CBoxData) (xp yp : ℚ) : ℚ :=
  (1 / b.aLo) * xp + (b.l2Up / b.aLo) * yp

def cBattleExprQ (b : CBoxData) (xp yp sp : ℚ) : ℚ :=
  cBattleHeadQ b xp yp - (b.pLo * b.qLo / b.aUp ^ 3) * sp

def checkCBattleAux (b : CBoxData) (cLo : ℚ) (target : Nat) :
    Nat → Nat → ℚ → ℚ → ℚ → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, m, xp, yp, sp =>
      let head := cBattleHeadQ b xp yp
      if m = target then decide (head ≤ cLo * m)
      else if m < target ∧ cBattleExprQ b xp yp sp ≤ cLo * m then
        checkCBattleAux b cLo target fuel (m + 1)
          (roundUp (xp * roundUp b.xUp (10 ^ 12)) (10 ^ 12))
          (roundUp (yp * roundUp b.yUp (10 ^ 12)) (10 ^ 12))
          (roundDown (sp * roundDown b.sLo (10 ^ 12)) (10 ^ 12))
      else false

def checkCBattle (b : CBoxData) (target : Nat) : Bool :=
  let start := b.mPlus
  if target < start ∨ target > 500001 then false
  else
    checkCBattleAux b b.cLo target (target - start + 1) start
      (directedPowUp b.xUp (start - 2))
      (directedPowUp b.yUp (start - 2))
      (directedPowDown b.sLo (start - 2))

def checkCRegular (box : RatBox) (target : Nat) : Bool :=
  let b := makeCBox box
  if !b.sqrtOK || b.fLo ≤ 0 || b.sLo ≤ 0 || b.sLo ≥ b.xUp || box.k1 = 0 then false
  else if b.cLo ≤ 0 then false
  else checkCBattle b target

def checkCBottom (box : RatBox) : Bool :=
  let b := makeCBox box
  if !b.sqrtOK || b.fLo ≤ 0 || b.sLo ≤ 0 || b.sLo ≥ b.xUp || box.k1 ≠ 0 then false
  else
    let g2p := b.g2Lo - b.g2Lo ^ 2 / 2
    if !(2 * b.rhoLoUp * b.xiUp ≤ 1) || g2p ≤ 0 then false
    else
      let c0 := b.qLo * g2p / box.e2
      let a := b.uLo * c0
      if !(box.k2 ≤ a / 2) then false
      else decide ((1 / b.aLo) * expNegUpC (a / box.k2) ≤ b.cI0 * box.k2 * c0)

def checkCNode (tokens : Array RegionCertToken) :
    Nat → Nat → RatBox → Nat → Option ParseOut
  | 0, _, _, _ => none
  | fuel + 1, index, box, depth =>
      match tokens[index]? with
      | some .splitE =>
          let children := box.splitE
          match checkCNode tokens fuel (index + 1) children.1 (depth + 1) with
          | none => none
          | some left =>
              match checkCNode tokens fuel left.next children.2 (depth + 1) with
              | none => none
              | some right => some ⟨right.next, left.stats.merge right.stats⟩
      | some .splitK =>
          let children := box.splitK
          match checkCNode tokens fuel (index + 1) children.1 (depth + 1) with
          | none => none
          | some left =>
              match checkCNode tokens fuel left.next children.2 (depth + 1) with
              | none => none
              | some right => some ⟨right.next, left.stats.merge right.stats⟩
      | some .cSkip =>
          if box.k1 ≥ min (kappaXiQ box.e2) (kappaBarQ box.e1) then
            some ⟨index + 1, skippedStats depth⟩
          else none
      | some (.cVerified m) =>
          if checkCRegular box m then some ⟨index + 1, verifiedStats depth m⟩ else none
      | some .cBottom =>
          if checkCBottom box then some ⟨index + 1, bottomStats depth⟩ else none
      | _ => none

def zoneCRoot : RatBox where
  e1 := 1 / 60
  e2 := 1 / 3 - 1 / 1000
  k1 := 0
  k2 := 1

def checkZoneC (tokens : Array RegionCertToken) : Option CertStats := do
  let result ← checkCNode tokens (tokens.size + 1) 0 zoneCRoot 0
  if result.next = tokens.size then some result.stats else none

def zoneCExpectedStats : CertStats where
  verified := 2997
  skipped := 87
  bottom := 5
  maxDepth := 28
  maxM := 1716

end OddCycleBound.RegionII.Certificate
