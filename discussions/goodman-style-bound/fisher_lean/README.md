# Fisher's triangle-density lower bound

A Lean 4 + Mathlib verification of Fisher's lower bound for the triangle
density of a finite graph, together with a deterministic finite-to-graphon
transfer.  The development proves the triangle-density hypothesis used by the
odd-cycle Goodman-type bound in the sibling `../lean/` project.

The mathematical reference is [`../fisher.tex`](../fisher.tex).

## Main theorem

For a graphon `W` on a probability space `(Omega, mu)`, let

```math
p = t(K_2,W) = \iint W(x,y)\,d\mu(x)\,d\mu(y)
```

be its edge density and let

```math
q = t(K_3,W)
  = \iiint W(x,y)W(y,z)W(z,x)\,d\mu(x)\,d\mu(y)\,d\mu(z)
```

be its triangle density.  On the band `1/2 < p <= 2/3`, the project proves

```math
q \;\ge\;
p-\frac49-\frac49\left(1-\frac{3p}{2}\right)^{3/2}.
```

Equivalently, if

```math
c=\frac{1-\sqrt{4-6p}}{3},
```

then

```math
q \ge \frac32 c(1-c)^2.
```

The graphon-facing Lean theorem is in
`OddCycleBound/Fisher/GraphonBridge.lean`:

```lean
theorem OddCycleBound.triangleDensityLowerBound_twoThirds :
    TriangleDensityLowerBoundUpTo.{u} (2 / 3)
```

Here `TriangleDensityLowerBoundUpTo rho` quantifies over every probability
space and every graphon whose edge density lies in `1/2 < p <= rho`.  Its
statement is copied from the interface assumed by
`../lean/OddCycleBound/Main.lean`.

By monotonicity, the theorem immediately supplies all smaller cutoffs used in
that project, including `1003/2000`, `103/200`, and `51/100`:

```lean
example : OddCycleBound.TriangleDensityLowerBoundUpTo (103 / 200) :=
  OddCycleBound.TriangleDensityLowerBoundUpTo.mono
    OddCycleBound.triangleDensityLowerBound_twoThirds (by norm_num)
```

Thus the corresponding conditional odd-cycle theorems can be instantiated
with a verified proof of their triangle-density hypothesis.

### Definitions needed to read the statement

Fix a measurable space `Omega` with a probability measure `mu`.

- A **graphon** is a measurable, symmetric kernel
  `W : Omega -> Omega -> Real` with values in `[0,1]`.  In Lean this is
  `IsGraphon W mu`.
- `edgeDensity W mu` is `t(K2,W)`, the double integral of `W`.
- `compPow mu W 2` is the second integral-composition power of `W`.
- `trace mu (compPow mu W 2)` is the cyclic triple integral above, hence
  `t(C3,W) = t(K3,W)`.
- `TriangleDensityLowerBoundUpTo rho` is the universal graphon assertion that
  the displayed Fisher bound holds whenever `1/2 < p <= rho`.

## Idea of the proof

The verification has two distinct parts.  First it formalizes Fisher's finite
graph argument.  It then proves, within Lean, that finite simple graphs are
dense for precisely the edge and triangle densities needed to transfer the
finite inequality to arbitrary graphons.

### 1. Fisher's finite theorem

For a finite simple graph `G`, write

```math
n = |V(G)|,\qquad e = |E(G)|,\qquad T = \#K_3(G).
```

Let `c_k(G)` be the number of `k`-cliques and define the dependence
polynomial

```math
D_G(z)=\sum_{k\ge0}(-1)^k c_k(G)z^k.
```

The formal proof proceeds as follows.

1. **Clique identities.**  Double-counting establishes the neighborhood and
   common-neighborhood identities needed for the coefficients of `D_G`.
2. **Dependence-polynomial recurrences.**  Deleting a vertex gives

   ```math
   D_G(z)=D_{G-v}(z)-zD_{G[N(v)]}(z),
   ```

   and differentiating `D_G` is expressed through induced common
   neighborhoods.
3. **Smallest positive root.**  For a nonempty graph, `beta(G)` is the least
   positive zero of `D_G`.  Recursive deletion proves existence, positivity
   below `beta(G)`, and monotonicity under induced subgraphs.
4. **Third-order truncation.**  Taylor's theorem at `beta(G)`, together with
   nonnegativity of the fourth derivative on the relevant interval, gives

   ```math
   1-n\beta+e\beta^2-T\beta^3\le0.
   ```

   With `r(G)=1/beta(G)`, this becomes

   ```math
   r^3-nr^2+er-T\le0.
   ```
5. **Spectral lower bound.**  If `lambda` is the spectral radius of the
   complement adjacency matrix, the development proves

   ```math
   r(G)\ge1+\lambda(\overline G)
       \ge n-\frac{2e}{n}.
   ```
6. **Cubic optimization.**  The cubic `phi(x)=x^3-nx^2+ex` is minimized on
   the required interval at

   ```math
   x_+=\frac{n+\sqrt{n^2-3e}}{3}.
   ```

Combining these facts proves `Fisher.fisher_finite`:

```math
T\ge
\frac{9en-2n^3-2(n^2-3e)^{3/2}}{27}
\qquad\left(\frac{n^2}{4}\le e\le\frac{n^2}{3}\right).
```

After substituting `p=2e/n^2` and `q=6T/n^3`, this is exactly the density
form used in the graphon bridge.

### 2. Finite graphs approximate graphons

The transfer does not assume a graphon-sampling theorem as an axiom.  It proves
the required two-density approximation directly.

1. A bounded graphon is approximated in `L1` by a finite-feature kernel.
2. Clamping and symmetrizing produce a finite weighted graphon with nearly the
   same edge and triangle densities.  The triangle-density error is controlled
   by

   ```math
   |t(K_3,U)-t(K_3,W)|\le3\lVert U-W\rVert_1.
   ```
3. `GraphonRounding.lean` converts a finite weighted graphon into finite simple
   graphs deterministically.  Every atom is copied `n+3` times and receives a
   finite coordinate label.  For an intended edge weight `H(q,r)`, the edge
   test uses the threshold

   ```math
   \left\lfloor\sqrt{H(q,r)}\,(n+3)\right\rfloor.
   ```

   Two independent endpoint tests multiply to the desired edge weight.
   Around a triangle, the six coordinate tests factor into the product of the
   three rounded edge weights.  Explicit collision coefficients account for
   repeated copies and tend to `1`.
4. A uniform blow-up replaces the remaining atom weights by vertex
   multiplicities.
5. A diagonal choice yields `exists_finiteGraph_density_approximants`: a
   sequence of finite simple graphs whose edge and triangle densities converge
   simultaneously to those of the original graphon.

### 3. Passing Fisher's inequality to the limit

If `1/2 < p < 2/3`, sufficiently accurate finite approximants remain inside
the closed finite density band.  Fisher's finite inequality applies to them,
and continuity of the Fisher curve passes the inequality to the limit.

The upper endpoint `p=2/3` is handled by scaling the kernel by coefficients
strictly below `1` and tending to `1`.  `GraphonContinuity.lean` controls the
edge and triangle densities under this `L1` approximation.  Finally,
`fisher_density_param_eq` identifies the density-coordinate formula with the
`c`-parameter formulation required by `TriangleDensityLowerBoundUpTo`.

## Verification and trust status

The target theorem has been compiled with Lean `v4.31.0`.  An axiom audit can
be reproduced with a temporary file:

```lean
import OddCycleBound.Fisher.GraphonBridge

#print axioms OddCycleBound.triangleDensityLowerBound_twoThirds
```

Running `lake env lean Audit.lean` prints:

```text
'OddCycleBound.triangleDensityLowerBound_twoThirds' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

In particular, the target does **not** depend on `sorryAx`.  The listed axioms
are the standard classical and quotient principles used throughout Mathlib.

There is one literal `sorry` elsewhere under this project's
`OddCycleBound/` sources:

```lean
Fisher.TraceMonoid.cartier_foata
```

It states the standalone Cartier--Foata power-series inversion theorem.  No
other declaration refers to it, and neither `TraceMonoid.lean` nor its
power-series support modules occur in the target theorem's dependency graph.
Importing the project root merely makes that theorem available; it does not
make unrelated declarations depend on its proof.  Consequently:

- the graphon triangle-density theorem is verified without `sorryAx`;
- the finite Fisher theorem used by it is verified without `sorryAx`;
- `cartier_foata` itself remains an independent unfinished result.

To make every declaration in the Fisher project `sorry`-free, one would still
need to prove `cartier_foata` or remove that optional module.  This is not
required for the theorem documented here.

## Module dependencies

Arrows point from a module to a module that imports it.  The target dependency
graph is:

```text
CliqueCounts -> DependencePolynomial -> SmallestRoot -> ThirdTruncation
  -> Spectral -> FiniteTheorem -> FiniteGraphon -> GraphonRounding
  -> GraphonSampling -> GraphonBridge

CubicOpt -> FiniteTheorem
Kernel -> GraphonContinuity -> FiniteGraphon
GraphonContinuity -> GraphonScaling -> GraphonBridge
Kernel -> Interface -> GraphonBridge
FiniteGraphon -> GraphonBridge
GraphonBridge -> triangleDensityLowerBound_twoThirds
```

The optional, currently unused trace-monoid branch is:

```text
PowerSeriesPositivity ----+
                          +-> DependenceRatio -> TraceMonoid
DependencePolynomial -----+                         |
                                                    v
                                     cartier_foata (unfinished)
```

## Building

The toolchain is pinned to Lean and Mathlib `v4.31.0`.

```text
cd fisher_lean
lake exe cache get
lake build
```

The first command downloads precompiled Mathlib artifacts.  The second builds
the `OddCycleBound` library and the project root.

To check only the graphon bridge:

```text
lake env lean OddCycleBound/Fisher/GraphonBridge.lean
```

Because the project root imports the optional `TraceMonoid` module, a complete
build may report the existing `cartier_foata` sorry warning.  This warning is
separate from the axiom audit of the target theorem.

## Files

All Lean sources live under `OddCycleBound/`; the principal new declarations
are in namespace `Fisher` for the finite argument and namespace
`OddCycleBound` for graphon-facing results.

### Main result and graphon transfer

| File | Mathematical content | Principal Lean names |
|------|----------------------|----------------------|
| `Fisher/Interface.lean` | Exact proposition consumed by the sibling odd-cycle development | `TriangleDensityLowerBoundUpTo`, `TriangleDensityLowerBoundUpTo.mono` |
| `Fisher/GraphonContinuity.lean` | `L1` continuity of edge and triangle densities | `kernelL1Dist`, `abs_edgeDensity_sub_le_kernelL1Dist`, `abs_triangleDensity_sub_le_three_mul_kernelL1Dist` |
| `Fisher/FiniteGraphon.lean` | Uniform finite graphs as graphons; translation between counts and densities | `finiteGraphKernel`, `edgeDensity_finiteGraphKernel`, `triangleDensity_finiteGraphKernel` |
| `Fisher/GraphonRounding.lean` | Deterministic label rounding of finite weighted graphons | `roundingGraph`, `roundingMeasure`, `roundingGraph_density_tendsto` |
| `Fisher/GraphonSampling.lean` | Finite-feature approximation, uniform blow-ups, and the diagonal density theorem | `FiniteGraphApprox`, `exists_finiteGraph_density_approximants` |
| `Fisher/GraphonScaling.lean` | Approximation of the closed upper endpoint by interior graphons | `scaleKernel`, `exists_interior_scaled_graphons` |
| `Fisher/GraphonBridge.lean` | Limit transfer and final assembly | `fisherCurve`, `fisher_density_form_graphon_strict`, `triangleDensityLowerBound_twoThirds` |

### Fisher's finite argument

| File | Mathematical content | Principal Lean names |
|------|----------------------|----------------------|
| `Fisher/CliqueCounts.lean` | Clique counts and neighborhood double-counting | `cliqueCount`, `sum_cliqueCount_neighbor`, `sum_cliqueCount_commonNbhd` |
| `Fisher/DependencePolynomial.lean` | Dependence polynomial, deletion recurrence, derivative identity | `depPoly`, `depPoly_delete_vertex`, `depPoly_derivative_identity` |
| `Fisher/SmallestRoot.lean` | Least positive root and induced-subgraph monotonicity | `beta`, `depPoly_eval_beta`, `beta_le_beta_induce`, `depPoly_induced_nonneg_on_Icc` |
| `Fisher/ThirdTruncation.lean` | Taylor truncation and cubic-root consequence | `growthFactor`, `third_truncation`, `exists_root_ge_growth` |
| `Fisher/Spectral.lean` | Complement spectral-radius and average-degree lower bounds | `complSpectralRadius`, `growth_ge_one_add_lambda`, `growth_ge_avg_degree` |
| `Fisher/CubicOpt.lean` | Real-variable minimization of Fisher's cubic | `xMinus`, `xPlus`, `cubic_min_at_xPlus`, `cubic_value_xPlus` |
| `Fisher/FiniteTheorem.lean` | Fisher's finite theorem and density form | `fisher_finite`, `fisher_density_form` |

### Reused graphon infrastructure

| File | Mathematical content | Principal Lean names |
|------|----------------------|----------------------|
| `Graphon.lean` | Graphons, degrees, means, and kernel operators | `IsGraphon`, `edgeDensity`, `degree`, `kernelOp` |
| `PathDensity.lean` | Path-density infrastructure required by `Kernel` | path-density lemmas |
| `Kernel.lean` | Kernel composition, powers, and cyclic trace | `comp`, `compPow`, `trace` |

These files originate in the sibling `../lean/OddCycleBound/` development and
are reused or adapted here so that the Fisher theorem has exactly the same
graphon interface.

### Optional trace-monoid branch

| File | Mathematical content | Status |
|------|----------------------|--------|
| `Fisher/PowerSeriesPositivity.lean` | Coefficientwise nonnegativity calculus for formal power series | proved |
| `Fisher/DependenceRatio.lean` | Nonnegative coefficients of dependence-series ratios | proved |
| `Fisher/TraceMonoid.lean` | Trace classes, induced monotonicity, and Cartier--Foata inversion | trace-class results proved; `cartier_foata` unfinished and unused |
