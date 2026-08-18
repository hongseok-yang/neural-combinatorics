import Taeyoung.Fisher.GraphonBridge

/-!
# Fisher's triangle-density bound, vendored

Atlas 148 is the one scoped row whose proof needs a *sharp* triangle-density
lower bound: `notes/atlas148_paw_bias_hilbert_projection.tex` bounds the paw
density below by `p·g(p)`, where `g` is the extremal profile of the clique
density theorem, and the required bound is within `3.5%–6%` of `g` on
`[1/2, 3/5]` — far too tight for Goodman, which is `15%–33%` short there.

The sibling project `discussions/goodman-style-bound/fisher_lean` proves
Fisher's 1989 theorem, the `k = 2` branch of that profile, on the band
`1/2 < p ≤ 2/3`:

```
t(K₃, W) ≥ (3/2)·c·(1-c)²,      c = (1 - √(4-6p))/3.
```

The Atlas 148 argument needs the profile on all of `[p, 1]`, but only because
it invokes the full clique density theorem where Goodman already suffices:
above `s = 2/3` the crude bound `t(K₃) ≥ s(2s-1)`, fed through the same
`z = p^{5/2}s^{-3/2}` substitution, clears the requirement by a factor of at
least `1.34` on `[1/2, 3/5]`.  So Fisher's band is the whole of the deep input
this catalogue needs, and Razborov–Reiher is not required.

## Why a copy and not a dependency

The two projects share a toolchain (Lean `v4.31.0`) and a Mathlib revision
(`fabf563a`), so a path dependency would work.  A copy is preferred because:

* the upstream project carries one `sorry`,
  `Fisher.TraceMonoid.cartier_foata`, a standalone Cartier–Foata power-series
  inversion that nothing in the proof chain refers to.  Vendoring the closure
  of `triangleDensityLowerBound_twoThirds` leaves that file — and its two
  exclusive dependencies `DependenceRatio` and `PowerSeriesPositivity` —
  behind, so this project keeps its invariant that no `sorry` occurs anywhere
  under `Foundation/` or `Methods/`, and none in the imported tree either;
* the catalogue's build stays reproducible from this directory alone.

The seventeen vendored files differ from upstream only in their `import`
lines, each carrying a provenance header.  The internal namespaces
`OddCycleBound` and `Fisher` are kept verbatim so the copy stays diffable
against upstream; `Taeyoung/Methods/TriangleDensity.lean` is the bridge that
restates the result in this project's own graphon vocabulary.

## The vendored chain

```
GraphonBridge ← FiniteGraphon  ← FiniteTheorem ← Spectral ← ThirdTruncation
                               ← GraphonContinuity            ← SmallestRoot
              ← GraphonSampling ← GraphonRounding             ← DependencePolynomial
              ← GraphonScaling                                ← CliqueCounts
              ← Interface       ← Kernel ← PathDensity ← Graphon
```

with `FiniteTheorem` also using `CubicOpt`.  The target is

```lean
theorem OddCycleBound.triangleDensityLowerBound_twoThirds :
    OddCycleBound.TriangleDensityLowerBoundUpTo.{u} (2 / 3)
```

which depends on exactly `[propext, Classical.choice, Quot.sound]`.
-/
