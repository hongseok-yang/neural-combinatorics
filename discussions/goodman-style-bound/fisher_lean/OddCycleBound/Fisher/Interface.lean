import OddCycleBound.Kernel

/-!
# The triangle-density interface consumed by `OddCycleBound.Main`

This file states the *exact* proposition that the odd-cycle development in the
sibling `lean/` project assumes as its sole external input, under the name
`OddCycleBound.TriangleDensityLowerBoundUpTo` (see
`lean/OddCycleBound/Conditional.lean`).  The goal of the `Fisher/` development is
to *discharge* this hypothesis by Fisher's finite-graph proof plus a
graph → graphon transfer, so that the conditional theorems in
`OddCycleBound.Main` become unconditional on `1/2 ≤ p ≤ 2/3`.

The proposition, in density form (Corollary in `fisher.tex`), says: for a
graphon `W` with edge density `p = edgeDensity W μ` satisfying `1/2 < p ≤ ρ`,
writing `c := (1 - √(4 - 6p)) / 3`, the triangle density obeys
`(3/2)·c·(1-c)^2 ≤ t(K₃, W) = trace μ (compPow μ W 2)`.

With `u := √(1 - 3p/2)` one has `c = (1-2u)/3` and `(3/2)·c·(1-c)^2 =
p - 4/9 - (4/9)·u^3`, which is precisely Fisher's density corollary
`q ≥ p - 4/9 - (4/9)(1 - 3p/2)^{3/2}`.
-/

open MeasureTheory

namespace OddCycleBound

universe u

/-- Direct Razborov–Reiher / Fisher triangle-density lower bound up to an
edge-density cutoff `rho`.  This is the sole external interface used by the
public conditional cycle theorems in `OddCycleBound.Main`.

Copied verbatim (statement) from `lean/OddCycleBound/Conditional.lean`; the
`Fisher/` project's target is to produce a term of type
`TriangleDensityLowerBoundUpTo (2/3)` (and hence, by monotonicity, of every
smaller cutoff `1003/2000`, `103/200`, `51/100`). -/
def TriangleDensityLowerBoundUpTo (rho : Real) : Prop :=
  forall {Omega' : Type u} [MeasurableSpace Omega']
    {mu' : Measure Omega'} [IsProbabilityMeasure mu']
    {W' : Omega' -> Omega' -> Real},
    IsGraphon W' mu' ->
    1 / 2 < edgeDensity W' mu' ->
    edgeDensity W' mu' <= rho ->
    let c := (1 - Real.sqrt (4 - 6 * edgeDensity W' mu')) / 3
    (3 / 2) * c * (1 - c) ^ 2 <= trace mu' (compPow mu' W' 2)

/-- Restrict a triangle-density hypothesis to a smaller cutoff. -/
theorem TriangleDensityLowerBoundUpTo.mono
    {rho sigma : Real}
    (h : TriangleDensityLowerBoundUpTo.{u} rho)
    (hsigma : sigma <= rho) :
    TriangleDensityLowerBoundUpTo.{u} sigma := by
  intro Omega' _ mu' _ W' hW' hp hle
  exact h hW' hp (hle.trans hsigma)

end OddCycleBound
