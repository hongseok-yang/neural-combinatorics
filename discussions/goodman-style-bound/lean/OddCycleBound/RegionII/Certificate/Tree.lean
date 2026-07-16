import Mathlib.Data.Rat.Floor

/-!
# Region-II certificate trees

Python emits only a preorder stream of these tokens.  The checker propagates
the exact rational box from the root, so split coverage and leaf locations are
not trusted data.
-/

namespace OddCycleBound.RegionII.Certificate

/-- Preorder tokens shared by the two scalar certificate trees. -/
inductive RegionCertToken where
  | splitE
  | splitK
  | bSkipZoneC
  | bSkipOutside
  | bVerified
  | cSkip
  | cVerified (m : Nat)
  | cBottom
  deriving DecidableEq, Repr

/-- A closed rational rectangle in `(e,kappa)` coordinates. -/
structure RatBox where
  e1 : ℚ
  e2 : ℚ
  k1 : ℚ
  k2 : ℚ
  deriving DecidableEq, Repr

def RatBox.splitE (b : RatBox) : RatBox × RatBox :=
  let em := (b.e1 + b.e2) / 2
  ({ b with e2 := em }, { b with e1 := em })

def RatBox.splitK (b : RatBox) : RatBox × RatBox :=
  let km := (b.k1 + b.k2) / 2
  ({ b with k2 := km }, { b with k1 := km })

/-- Statistics recomputed by Lean while consuming a complete tree. -/
structure CertStats where
  verified : Nat := 0
  skipped : Nat := 0
  bottom : Nat := 0
  maxDepth : Nat := 0
  maxM : Nat := 0
  deriving DecidableEq, Repr

def CertStats.merge (a b : CertStats) : CertStats where
  verified := a.verified + b.verified
  skipped := a.skipped + b.skipped
  bottom := a.bottom + b.bottom
  maxDepth := max a.maxDepth b.maxDepth
  maxM := max a.maxM b.maxM

def verifiedStats (depth : Nat) (m : Nat := 0) : CertStats where
  verified := 1
  maxDepth := depth
  maxM := m

def skippedStats (depth : Nat) : CertStats where
  skipped := 1
  maxDepth := depth

def bottomStats (depth : Nat) : CertStats where
  verified := 1
  bottom := 1
  maxDepth := depth

end OddCycleBound.RegionII.Certificate
