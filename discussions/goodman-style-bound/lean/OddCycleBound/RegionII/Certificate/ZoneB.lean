import OddCycleBound.RegionII.Certificate.Intervals
import OddCycleBound.RegionII.Certificate.Generated
import Mathlib.Tactic

/-! # Exact Zone-B certificate checker -/

namespace OddCycleBound.RegionII.Certificate

def kappaXiQ (e : ℚ) : ℚ := e / (1 - e) ^ 2

def kappaBarQ (e : ℚ) : ℚ :=
  min ((1 - e) / (1 + e)) ((1 - 3 * e) / (6 * e))

def chartXQ (e k : ℚ) : ℚ :=
  (1 - e) / (1 + e + 2 * k * e)

def sqrtLoB (x : ℚ) : ℚ := sqrtLo x (10 ^ 40)
def sqrtUpB (x : ℚ) : ℚ := sqrtUp x (10 ^ 40)

def checkBVerified (b : RatBox) : Bool :=
  let xMin := chartXQ b.e2 b.k2
  let xMax := chartXQ b.e1 b.k1
  let lamMin := 1 - xMax
  let aMin := xMin * (1 + b.k2) / b.k2
  let aMax := xMax * (1 + b.k1) / b.k1
  let l2Up := 2 * b.e2 / (1 - b.e2)
  let lUp := sqrtUpB l2Up
  if !sqrtBracketOK l2Up (sqrtLoB l2Up) lUp || lUp ≥ 1 then false
  else
    let l14Up := min 1 (l2Up ^ 7)
    let tRho := (1737 / 100 : ℚ) * (1 + b.k1) * b.e1
    let rhoLo := (1 - expNegUpB tRho) / 4
    let epsUp := min (1 / 4) (b.e2 / (4 * (1 - b.e2) ^ 2 * b.k1 * (1 + rhoLo)))
    let rootOneMinusE := sqrtLoB (1 - b.e2)
    if !sqrtBracketOK (1 - b.e2) rootOneMinusE (sqrtUpB (1 - b.e2)) then false
    else
      let piLo := rootOneMinusE * (1 - lUp) * (1 - l14Up) * (1 - epsUp) / (1 + lUp)
      if piLo ≤ 0 then false
      else
        let lamUp := xMax ^ 13 * l2Up ^ 6 * lUp * (1 - b.e1) ^ 2 / (15 * b.e1)
        let k1Up := xMax ^ 14 * max 0 (14 - aMin) / 15
        let onlyK14 := decide (aMax < 14 ∧ 15 * (14 - aMax) * lamMin ≥ aMax + 1)
        if onlyK14 then
          decide (piLo ≥ k1Up / (xMin * xMin) + lamUp)
        else
          let phiMin :=
            2 * (1 - b.e2) * b.e1 * (1 + b.k2) ^ 2 /
              (b.k2 * (1 + b.e2 + 2 * b.k2 * b.e2) ^ 2)
          let disc := phiMin * phiMin + 4 * phiMin
          let discLo := sqrtLoB disc
          if !sqrtBracketOK disc discLo (sqrtUpB disc) then false
          else
            let wLo := max 0 ((discLo - phiMin) / 2)
            let k2Up := expNegUpB (phiMin + 2 * wLo)
            decide (piLo ≥ max k1Up k2Up / (xMin * xMin) + lamUp)

structure ParseOut where
  next : Nat
  stats : CertStats

def checkBNode (tokens : Array RegionCertToken) :
    Nat → Nat → RatBox → Nat → Option ParseOut
  | 0, _, _, _ => none
  | fuel + 1, index, box, depth =>
      match tokens[index]? with
      | some .splitE =>
          let children := box.splitE
          match checkBNode tokens fuel (index + 1) children.1 (depth + 1) with
          | none => none
          | some left =>
              match checkBNode tokens fuel left.next children.2 (depth + 1) with
              | none => none
              | some right => some ⟨right.next, left.stats.merge right.stats⟩
      | some .splitK =>
          let children := box.splitK
          match checkBNode tokens fuel (index + 1) children.1 (depth + 1) with
          | none => none
          | some left =>
              match checkBNode tokens fuel left.next children.2 (depth + 1) with
              | none => none
              | some right => some ⟨right.next, left.stats.merge right.stats⟩
      | some .bSkipZoneC =>
          if box.k2 ≤ kappaXiQ box.e1 then some ⟨index + 1, skippedStats depth⟩ else none
      | some .bSkipOutside =>
          if box.k1 ≥ kappaBarQ box.e1 then some ⟨index + 1, skippedStats depth⟩ else none
      | some .bVerified =>
          if checkBVerified box then some ⟨index + 1, verifiedStats depth⟩ else none
      | _ => none

def zoneBRoot : RatBox where
  e1 := 1 / 60
  e2 := 2033 / 10000
  k1 := kappaXiQ (1 / 60)
  k2 := 1

def checkZoneB (tokens : Array RegionCertToken) : Option CertStats := do
  let result ← checkBNode tokens (tokens.size + 1) 0 zoneBRoot 0
  if result.next = tokens.size then some result.stats else none

def zoneBExpectedStats : CertStats where
  verified := 23
  skipped := 3
  maxDepth := 8

theorem zoneB_certificate_checked :
    checkZoneB zoneBTokens = some zoneBExpectedStats := by
  decide +kernel

end OddCycleBound.RegionII.Certificate
