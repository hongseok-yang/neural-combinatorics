# PureChordal

A Lean 4 / Mathlib formalization of the **pure-chordal graphon inequality**, a
Goodman-style chromatic-polynomial lower bound. For every chordal graph `H` whose
maximal cliques all have the common size `r ≥ 3`, and every graphon `W` with edge
density `p ≥ 1 − 1/(r − 1)`, the homomorphism density of `H` in `W` satisfies

```
t(H, W)  ≥  (1 − p)^v(H) · χ_H( 1 / (1 − p) ),
```

where `v(H)` is the number of vertices and `χ_H` is the chromatic polynomial of `H`.
As a companion, at the threshold density `p = 1 − 1/k` the balanced complete
`k`-partite graphon is a minimizer of `t(H, ·)`.

## Notation

For a probability space `(Ω, μ)` and a finite simple graph `H`:

- `Graphon Ω μ` — a graphon: a measurable, symmetric kernel `Ω → Ω → ℝ` valued in `[0,1]`.
- `homDensity H W` — the homomorphism density `t(H, W) = ∫ ∏_{uv ∈ E(H)} W(x_u, x_v)`.
- `cliqueDensity s W` — the `Kₛ` homomorphism density `t(Kₛ, W)`; `cliqueDensity 2 W` is
  the edge density `p`.
- `IsChordal H` — chordality, as the existence of a maximal-clique-tree decomposition.
- `HasPureMaximalCliques H r` — every maximal clique of `H` has cardinality `r`.
- `MaximalCliqueTreeDecomp.chromaticPolynomial` — the factored chromatic polynomial `χ_H`
  attached to a clique-tree decomposition.
- `balancedMultipartiteGraphon k` — the balanced complete `k`-partite graphon on `Fin k`,
  each part carrying mass `1/k`.

## Theorems in `PureChordal/Main.lean`

- **`pureChordal_chromaticPolynomial_lower_bound`** — the headline inequality. For a
  chordal `H` with `HasPureMaximalCliques H r`, `3 ≤ r`, edge density
  `p = cliqueDensity 2 W ≥ 1 − 1/(r − 1)` (and `p ≠ 1`),
  ```
  (1 − p)^(card V) · eval (1 / (1 − p)) χ_H  ≤  homDensity H W.
  ```
  Assembled from two independent components: `certificateBound_le_homDensity`
  (`CertificatePolynomialBound.lean`), the analytic bound of the clique-tree certificate
  against the true hom density, and `certificateBound_eq_eval_chromaticPolynomial`
  (`ChromaticFactorization.lean`), the finite-combinatorial identity rewriting that
  certificate as `(1 − p)^v(H) · χ_H(1/(1 − p))`.

- **`pureChordal_balancedMultipartite_minimal`** — the extremal companion. Under the same
  hypotheses with `r ≤ k` and edge density pinned to `cliqueDensity 2 W = 1 − 1/k`,
  ```
  homDensity H (balancedMultipartiteGraphon k)  ≤  homDensity H W,
  ```
  i.e. the balanced complete `k`-partite graphon minimizes `t(H, ·)` at that density.
  Proven via `MaximalCliqueTreeDecomp.balancedMultipartite_minimal`.

### Worked examples

`PureChordal/Examples/{N4,N5,N6}.lean` carry explicit
`PureCliqueTreeDecomp` certificates and derive `k`-partite optimality for all 17 non-clique
pure chordal graphs on at most six vertices (1 on four vertices, 4 on five, 12 on six).

## How to verify the proof

The claim is: the two `Main.lean` theorems are proven from the Lean/Mathlib logical
foundations alone, with no `sorry` and no extra axioms.

1. **It compiles.** From the package root:
   ```
   lake exe cache get   # fetch the prebuilt Mathlib v4.31.0 (avoids a cold Mathlib build)
   lake build
   ```
   This type-checks every module against the pinned Mathlib `v4.31.0`. A successful build
   means the Lean kernel has verified every proof term; an incomplete proof would fail the
   build.

2. **It uses only the standard axioms.** `PureChordal/CheckComplete.lean` imports the two
   theorems and runs `#print axioms` on each. Build it and read the emitted lines:
   ```
   lake build PureChordal.CheckComplete
   ```
   Each theorem reports **exactly**:
   ```
   depends on axioms: [propext, Classical.choice, Quot.sound]
   ```
   These are the three standard axioms of Lean/Mathlib classical mathematics. The absence of
   `sorryAx` is the machine-checked guarantee that nothing is assumed or left unproven.

There are no `decide +kernel` / `native_decide` shortcuts and no computational certificates
trusted outside the kernel.

## Benchmarks

A full `lake build` of the complete proof is 3286 build jobs on the pinned Mathlib
`v4.31.0` toolchain. On a Windows 11 laptop with 16 GB RAM and an Intel i7-1165G7 CPU
(2.80 GHz), a clean build of the proof takes about 4.8 minutes (≈285 s) and peak memory
usage is about 9.6 GB .
