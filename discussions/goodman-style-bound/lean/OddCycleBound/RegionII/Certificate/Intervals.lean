import OddCycleBound.RegionII.Certificate.Tree
import Mathlib.Analysis.Complex.Exponential

/-!
# Executable rational interval primitives

All endpoint arithmetic is exact in `ℚ`.  Square-root endpoints use integer
square root and are separately checked by squaring.  Exponential upper bounds
are reciprocals of finite positive Taylor sums.  Directed powers round after
the same binary operations used by the corrected certifier.
-/

namespace OddCycleBound.RegionII.Certificate

def roundDown (x : ℚ) (den : Nat) : ℚ :=
  (⌊x * den⌋ : ℚ) / den

def roundUp (x : ℚ) (den : Nat) : ℚ :=
  (⌈x * den⌉ : ℚ) / den

def sqrtIndex (x : ℚ) (scale : Nat) : Nat :=
  if x ≤ 0 then 0
  else Nat.sqrt (x.num.toNat * scale * scale / x.den)

def sqrtLo (x : ℚ) (scale : Nat) : ℚ :=
  sqrtIndex x scale / scale

def sqrtUp (x : ℚ) (scale : Nat) : ℚ :=
  if x ≤ 0 then 0 else (sqrtIndex x scale + 1) / scale

def sqrtBracketOK (x lo hi : ℚ) : Bool :=
  decide (0 ≤ lo ∧ lo * lo ≤ x ∧ x ≤ hi * hi ∧ 0 ≤ hi)

def partialExp (x : ℚ) (n : Nat) : ℚ × ℚ :=
  (x ^ n / n.factorial,
    ∑ i ∈ Finset.range (n + 1), x ^ i / i.factorial)

/-- Zone-B upper enclosure of `exp (-t)`. -/
def expNegUpB (t : ℚ) : ℚ :=
  let t' := roundDown t (10 ^ 12)
  1 / (partialExp t' 40).2

def expCutoffC (t eps : ℚ) : Nat → Nat → ℚ → Nat
  | 0, k, _ => k - 1
  | fuel + 1, k, term =>
      if term > eps ∧ k < 500 then
        let next := term * t / k
        expCutoffC t eps fuel (k + 1) next
      else k - 1

/-- Zone-C upper enclosure of `exp (-t)`, matching the 500-step source loop. -/
def expNegUpC (t : ℚ) : ℚ :=
  let t' := min (roundDown t (10 ^ 9)) 400
  let cutoff := expCutoffC t' (1 / 10 ^ 50) 499 1 1
  1 / (partialExp t' cutoff).2

def directedPowUpGo (den : Nat) (r b : ℚ) (n : Nat) : ℚ :=
  if h : n = 0 then r
  else
    let r' := if n % 2 = 1 then roundUp (r * b) den else r
    directedPowUpGo den r' (roundUp (b * b) den) (n / 2)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)

def directedPowDownGo (den : Nat) (r b : ℚ) (n : Nat) : ℚ :=
  if h : n = 0 then r
  else
    let r' := if n % 2 = 1 then roundDown (r * b) den else r
    directedPowDownGo den r' (roundDown (b * b) den) (n / 2)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)

def directedPowUp (base : ℚ) (n : Nat) : ℚ :=
  directedPowUpGo (10 ^ 12) 1 (roundUp base (10 ^ 12)) n

def directedPowDown (base : ℚ) (n : Nat) : ℚ :=
  directedPowDownGo (10 ^ 12) 1 (roundDown base (10 ^ 12)) n

end OddCycleBound.RegionII.Certificate
