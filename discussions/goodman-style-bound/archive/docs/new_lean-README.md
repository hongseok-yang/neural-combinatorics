# The high-density odd-cycle bound

A Lean 4 + Mathlib formalization of the odd-cycle homomorphism-density inequality for graphons of edge
density at least `2/3`.

## Main theorem

```lean
theorem odd_cycle_bound {m : ℕ} (hW : IsGraphon W μ)
    (hp : 2 / 3 ≤ edgeDensity W μ) (hm : Odd m) (hm3 : 3 ≤ m) :
    edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1)
      ≤ cycleDensity μ W m
```
(`OddCycleBound/Main.lean`, namespace `OddCycleBound.HighDensity`.)

Mathematically: for every graphon $`W`$ of edge density $`p \ge 2/3`$ and every odd $`m \ge 3`$,

```math
t(C_m, W) \;\ge\; p^{m} - p(1-p)^{m-1}.
```

### Definitions needed to read the statement

Fix a probability space $`(\Omega, \mu)`$ ($`\mu`$ a probability measure on a measurable space $`\Omega`$).

- **Graphon** $`W : \Omega \times \Omega \to \mathbb{R}`$ — a symmetric, measurable, $`[0,1]`$-valued
  kernel. In Lean this is `IsGraphon W μ`: `Measurable (uncurry W)`, $`0 \le W(x,y) \le 1`$, and
  $`W(x,y) = W(y,x)`$. A graphon is the limit object of a sequence of dense graphs; $`W(x,y)`$ is the
  "probability of an edge" between points $`x`$ and $`y`$.

- **Edge density** $`p = \iint W(x,y)\,d\mu(x)\,d\mu(y)`$ (`edgeDensity W μ`), the homomorphism density
  $`t(K_2, W)`$ of a single edge.

- **Cycle density** $`t(C_m, W) = \int\!\cdots\!\int W(x_1,x_2)\,W(x_2,x_3)\cdots W(x_m,x_1)\,d\mu(x_1)\cdots d\mu(x_m)`$ (`cycleDensity μ W m`), the homomorphism density of the $`m`$-cycle. In Lean
  it is `trace μ (compPow μ W (m−1))`, the cyclic trace of the $`(m-1)`$-st power of the integral
  operator with kernel $`W`$.

The right-hand side $`p^{m} - p(1-p)^{m-1}`$ is the conjectured extremal value, attained by the union of
a clique and isolated vertices.

## Idea of the proof

It is cleaner to work with the complement kernel $`U = 1 - W`$, again a graphon, with edge density
$`q = 1 - p \le 1/3`$. Two functionals of $`U`$ drive the argument. The *centred degree*
$`g(x) = \int U(x,y)\,d\mu(y) - q`$ measures how far $`x`$ is from average degree; it is mean-zero. The
*compression* $`A`$ is the integral operator of $`U`$ restricted to mean-zero functions. Their interaction
is recorded by the **spectral moments**

```math
s_j = \langle g,\, A^{j} g\rangle, \qquad s_0 = \lVert g\rVert^2 \ (\text{the degree variance}).
```

All of $`g`$, $`A`$, $`s_j`$ are defined in `Graphon.lean`.

**From the cycle density to a polynomial in the moments.** Expand the cyclic product
$`t(C_m,W) = \int \prod_i \bigl(1 - U(x_i,x_{i+1})\bigr)`$ by inclusion–exclusion. The naive expansion has
$`2^m`$ terms, but as a cyclic sum it telescopes to an $`O(m)`$-term identity (`complTrace_necklace`) in the
*path densities* $`x_j = t(P_j, U)`$ of the complement, and Lemma 2.4 (`PathDensity.lean`) writes each
$`x_j`$ as an explicit polynomial in $`q`$ and $`s_0,\dots,s_{j-1}`$. Substituting, the difference

```math
\Phi_m \;:=\; t(C_m,W) - \bigl(p^{m} - p(1-p)^{m-1}\bigr)
```

becomes an explicit polynomial in $`q`$ and $`s_0,\dots,s_{m-2}`$ with no operators left in it
(`neckSum_moment`), and the theorem is exactly $`\Phi_m \ge 0`$. For $`m = 3`$ everything collapses to

```math
\Phi_3 = 2 s_0 = 2\lVert g\rVert^2 \ge 0,
```

i.e. the triangle bound is just "degree variance is nonnegative" (`cycle_bound_three`).

**Making the moments visible.** $`A`$ is compact and self-adjoint with $`\lVert A\rVert \le 1/2`$, so by the
spectral theorem its eigenvalues $`\lambda_k`$ lie in $`[-1/2, 1/2]`$ and

```math
s_j = \sum_k w_k\, \lambda_k^{\,j}, \qquad w_k \ge 0
```

(`AtomicSpectral.lean`, `AtomicMomentRepresentation.lean`; the relevant part of $`A`$ is finite-rank on
the Krylov subspace spanned by $`g, Ag, A^2 g, \dots`$, `KrylovCompression.lean`). Grouping the terms of
$`\Phi_m`$ by how many moment factors they carry writes it as

```math
\Phi_m = \sum_{r=1}^{(m-1)/2} \ \sum_{k_1,\dots,k_r} w_{k_1}\cdots w_{k_r}\;
  \mathrm{multiKernel}(m, r, q; \lambda_{k_1},\dots,\lambda_{k_r}),
```

a nonnegative-weighted average of one symmetric polynomial $`\mathrm{multiKernel}`$. Since the weights are
nonnegative, $`\Phi_m \ge 0`$ follows once $`\mathrm{multiKernel}(m,r,q;\cdot) \ge 0`$ on the cube
$`[-1/2,1/2]^r`$ for each $`r`$.

Explicitly (`SymmetricPoly.lean`), let $`h_d`$ be the complete homogeneous symmetric polynomial of
degree $`d`$, i.e. the sum of all degree-$`d`$ monomials in its arguments,

```math
h_d(a_1,\dots,a_k) = \sum_{i_1 + \cdots + i_k = d} a_1^{i_1}\cdots a_k^{i_k},
```

and write $`a^{\times k}`$ for the argument $`a`$ repeated $`k`$ times. With $`p = 1 - q`$ and $`n = m - 2r`$,

```math
\mathrm{multiKernel}(m,r,q;\lambda_1,\dots,\lambda_r) = \frac{m}{r}\Bigl[\,
  h_n\bigl(p^{\times r},\, -\lambda_1,\dots,-\lambda_r\bigr)
  + h_n\bigl(q^{\times r},\, \lambda_1,\dots,\lambda_r\bigr)\Bigr]
  - h_{n-1}\bigl(q^{\times (r+1)},\, \lambda_1,\dots,\lambda_r\bigr).
```

**Reducing to one variable.** Restricting $`\mathrm{multiKernel}`$ to the diagonal
$`\lambda_1 = \cdots = \lambda_r = \ell`$ gives the *single-variable* polynomial $`\mathrm{diagKernel}`$
(`diagKernel_eq_multiKernel`), and the two are not independent: they share one coefficient sequence
$`\mathrm{kerB}_j`$, with $`\mathrm{multiKernel} = \sum_j \mathrm{kerB}_j\, h_j(\vec\lambda)`$ and
$`\mathrm{diagKernel} = \sum_j \mathrm{kerB}_j \binom{j+r-1}{r-1}\ell^j`$ (`multiKernel_expand`,
`diagKernel_expand`). Since $`h_j(\vec\lambda)/\binom{j+r-1}{r-1}`$ is the $`j`$-th moment of a Dirichlet
weight, averaging $`\mathrm{diagKernel}`$ against that weight reproduces $`\mathrm{multiKernel}`$ exactly
(`multiKernel_eq_dirExp`): 
```math
\mathrm{multiKernel}(m,r,q;\vec\lambda) = \mathbb{E}_{\Theta\sim\mathrm{Dir}(1^r)}\,\mathrm{diagKernel}(m,r,q,\textstyle\sum_i \Theta_i\lambda_i)
```
As that weight is a probability measure supported inside $`[-\tfrac12,\tfrac12]`$, positivity of
$`\mathrm{multiKernel}`$ on the cube follows from positivity of its diagonal $`\mathrm{diagKernel}`$ on
$`[-\tfrac12,\tfrac12]`$ (`MixtureIntegral.lean`, `multiKernel_nonneg`),

```math
\mathrm{diagKernel}(m,r,q,\ell) = \frac{m}{r}\Bigl[\,
  h_n\bigl(p^{\times r},\, (-\ell)^{\times r}\bigr)
  + h_n\bigl(q^{\times r},\, \ell^{\times r}\bigr)\Bigr]
  - h_{n-1}\bigl(q^{\times (r+1)},\, \ell^{\times r}\bigr).
```

For instance $`\mathrm{diagKernel}(5,1,q,\ell) = 4\ell^2 + (8q-5)\ell + 12q^2 - 15q + 5`$. The whole
theorem has now come down to

```math
\mathrm{diagKernel}(m,r,q,\ell) \ge 0 \qquad
  \text{for all } 0 \le q \le \tfrac13,\ \ell \in [-\tfrac12, \tfrac12],\ 1 \le r \le \tfrac{m-1}{2}.
```

**Nonnegativity of `diagKernel`.** The reduction to real analysis runs through the auxiliary function

```math
\rho_{n,m}(u) = \frac{m}{n}\bigl(u^{n} + (1-u)^{n}\bigr) - u^{\,n-1}
```

(`RhoLemma.lean`). This is not pulled from nowhere: replacing the symmetric polynomials $`h_d`$ by their
Beta-integral representation writes $`\mathrm{diagKernel}`$ as a finite $`\mathrm{Beta}(r,r)`$ integral
(`gform_eq`), and its integrand — once a factor $`x^{n}`$ is cleared — is precisely
$`\rho_{n,m}\bigl((qx+\ell(1-x))/x\bigr)`$ (`bracket_eq_rho`), which is what $`\rho`$ is defined to be.
Substituting $`x = \ell/(\ell+s)`$ then gives, for $`\ell > 0`$,

```math
\mathrm{diagKernel}(m,r,q,\ell) = C_{m,r}\,\ell^{\,n+r}\int_0^{\infty}
  \frac{s^{\,r-1}}{(\ell+s)^{m}}\,\rho_{n,m}(q+s)\,ds, \qquad C_{m,r} > 0
```

(`KernelForm.lean`, `KernelImproper.lean`). The prefactor and the weight $`s^{r-1}/(\ell+s)^m`$ are
positive, so the sign of $`\mathrm{diagKernel}`$ is governed entirely by that of $`\rho_{n,m}(q+s)`$ as $`s`$
ranges over $`(0,\infty)`$ (equivalently $`u = q + s`$ over $`(q, \infty)`$). Now $`\rho_{n,m}`$ is *not*
everywhere nonnegative — it can dip below zero on a bounded window — but it is nonnegative for
$`u \le 1/2`$ and for $`u \ge n/m`$, and it satisfies a reflection inequality
$`\rho_{n,m}(u) + \rho_{n,m}(1-u) \ge 0`$ (`RhoLemma.lean`). These sign windows, together with integration
by parts, close the region in four cases directly — $`r = 1`$, $`\ell \le 0`$, $`2r \ge n`$, and
$`\ell \ge q + r/m`$ (`KernelR1.lean`, `KernelIBP.lean`, `StripAssembly.lean`) — because in each the
integral either avoids the negative window or the reflection cancels it. What is left is a bounded strip
in the $`(r,\ell)`$ plane where the negative window contributes and must be beaten quantitatively; it is
closed two ways: exact rational (Bernstein/Handelman) certificates for the finitely many odd
$`9 \le m \le 61`$ (the hypothesis `Hfin`), and a uniform analytic tail estimate for all odd $`m \ge 63`$
(the hypothesis `Hleft`, the `M6*` and `AppConstants*` files).

Module dependencies (hand-written files; arrows point from a file to the files it imports):

```
Graphon → PathDensity → Kernel, Certificate → Cycle → Necklace → General/*
LowBand/GraphonL2Operator → LowBand/CompactGraphonOperator

FiniteRank → BlockPower
GraphonReduction → MomentExpansion
SymmetricPoly → MixtureIntegral → Expansion → Atomic*, DefectIdentity → DefectPowerSeries
KrylovCompression → GraphonKrylovBridge ─────────────► ExpansionAssembly ─┐
RhoLemma → KernelForm → KernelImproper → KernelIntegrable, KernelR1        │
KernelReflect ─┘                          KernelR1 → KernelIBP             │
M6Strip → M6Reflection → M6LeftEstimate                                    │
M6TailFactors → M6TailRatio → M6StripLeftB, M6StripLeftA                   │
AppConstants → AppConstantsB0 → AppConstantsTail                           │
Sweep/Core → Sweep/Aggregate ─► M6StripLeftA ─► StripAssembly ─────────────┤
                                                                           ▼
                    FinalAssembly → HighDensityGE63, HighDensityLE61 → Main
                    Hfin/Aggregate ──────────────► HighDensityLE61
```

## Building

```
lake exe cache get     # download the prebuilt Mathlib v4.31.0 oleans
lake build -j 1        # build one module at a time (sequential)
```

Toolchain: Lean `v4.31.0`, Mathlib `v4.31.0` (pinned in `lean-toolchain` / `lakefile.toml`). Build
sequentially with `-j 1`: peak memory still reaches roughly `32 GB` on the heaviest certificate
modules even single-threaded, and a parallel build exceeds `64 GB`.

## Files

All proof files live under `OddCycleBound/`; the library namespace is `OddCycleBound` (high-density
work in `OddCycleBound.HighDensity`). Tables give the mathematical content and the principal Lean
names.

### Main results and top-level assembly

| File | Mathematical content | Lean names |
|------|----------------------|-----------|
| `Main.lean` | the theorem for all odd `m ≥ 3`, split at `m ≤ 61` vs `m ≥ 63` | `odd_cycle_bound` |
| `HighDensity/HighDensityGE63.lean` | the theorem for odd `m ≥ 63`, where no exact certificates are needed (`Hleft` only) | `odd_cycle_bound_ge63` |
| `HighDensity/HighDensityLE61.lean` | the theorem for odd `3 ≤ m ≤ 61`, using the exact certificates | `odd_cycle_bound_le61` |
| `HighDensity/FinalAssembly.lean` | reduces the graphon bound to the two remaining positivity facts `Hfin` (odd `m ≤ 61`) and `Hleft` (the remaining strip) | `cycle_bound_of_diagKernel_certificates` |

### Integral foundation

| File | Mathematical content | Lean names |
|------|----------------------|-----------|
| `Graphon.lean` | graphon and its integral functionals: edge density `p = ∫∫W`, degree function, its mean-zero part, and the spectral moments `s_j = ⟨g, Aʲg⟩` of the centred degree operator `A` | `IsGraphon`, `edgeDensity`, `degree`, `degCentered`, `compress`, `specMoment`, `kernelOp` |
| `PathDensity.lean` | the path densities `x_j = t(P_j, W)` as explicit polynomials in `q` and the moments `s_j` | `pathDensity`, `pathIter` |
| `Kernel.lean` | the kernel-composition algebra: composition, iterated powers, and the cyclic trace with its rotation invariance | `comp`, `compPow`, `trace`, `trace_comp_comm`, `onesKernel` |
| `Cycle.lean` | the cycle density `cycleDensity μ W m = t(C_m,W)` and the edge-deletion inequality `t(C_m,W) ≤ x_{m−1}` | `cycleDensity`, `edge_deletion_general`, `compPow_nonneg` |
| `Necklace.lean` | the cyclic inclusion–exclusion (telescoping) expansion of the trace of powers into path densities | necklace recursion lemmas |
| `General/Necklace.lean` | the general-`m` cyclic inclusion–exclusion identity | `complTrace_necklace` |
| `General/PathRecurrence.lean` | the general-`m` recurrence for the path densities `x_{n+1} = q·x_n + Σ s_i·x_{n−1−i}` | `pathDensity_succ` |
| `General/SumOfSquares.lean` | the moment sum-of-squares engine `∫(Σ c·h)² ≥ 0` | `sos_sq_expand` |
| `Certificate.lean` | sum-of-squares proofs that $`\Phi_m`$ is nonnegative for `C₅` and `C₇` | `sos2`, `cert5_specMoment`, `cert7_specMoment` |
| `LowBand/GraphonL2Operator.lean` | the graphon as a self-adjoint `L²` integral operator | `kernelL2Op` |
| `LowBand/CompactGraphonOperator.lean` | compactness and the self-adjoint eigen-expansion / finite-rank approximation of that operator | compact-operator interfaces |

### Reduction of the target to `diagKernel ≥ 0`

| File | Mathematical content | Lean names |
|------|----------------------|-----------|
| `HighDensity/GraphonReduction.lean` | reduces the cycle bound to $`\Phi_m \ge 0`$, i.e. nonnegativity of the cyclic-trace sum `neckSum` | `cycle_bound_of_neckSum` |
| `HighDensity/MomentExpansion.lean` | writes $`\Phi_m`$ as a polynomial in the path densities and moments, with no operators left; the `m = 3` case | `neckSum_moment`, `cycle_bound_three` |
| `HighDensity/SymmetricPoly.lean` | complete homogeneous symmetric polynomials; the one-parameter kernel `diagKernel` and its multivariate form `multiKernel` with their shared coefficient sequence | `hsym`, `diagKernel`, `multiKernel`, `kerB` |
| `HighDensity/MixtureIntegral.lean` | box positivity of `multiKernel` follows from `diagKernel ≥ 0` on `[−½,½]`, via a Dirichlet-mixture (iterated Beta) integral | `multiKernel_nonneg`, `dirExp_pow`, `beta_nat` |
| `HighDensity/Expansion.lean` | the expansion of $`\Phi_m`$ evaluated at a finite set of eigenvalues | expansion lemmas |
| `HighDensity/FiniteRank.lean` | a finite-dimensional block-matrix identity validating steps 1–4 on a model with finitely many eigenvalues | `two_sided_identity` |
| `HighDensity/BlockPower.lean` | a recurrence for the powers of the block operator, toward the cyclic-trace identity | block-power lemmas |
| `HighDensity/AtomicSpectral.lean` | the eigenvalues of the compression lie in `[−1/2, 1/2]` | support lemmas |
| `HighDensity/AtomicMomentRepresentation.lean` | each moment is a nonnegative-weighted power sum $`s_j = \sum_k w_k \lambda_k^{j}`$ | representation lemmas |
| `HighDensity/KrylovCompression.lean` | a finite Krylov subspace and its symmetric, norm-controlled orthogonal compression | Krylov compression |
| `HighDensity/GraphonKrylovBridge.lean` | identifies the moments of the centred graphon `L²` compression with the integral moments `s_j` | bridge lemmas |
| `HighDensity/DefectIdentity.lean` | expresses $`\Phi_m`$ as a universal identity in the path densities and moments | identity lemmas |
| `HighDensity/DefectPowerSeries.lean` | the path recurrence as an exact Schur-complement inverse (formal power series) | series identities |
| `HighDensity/ExpansionAssembly.lean` | `diagKernel ≥ 0` implies the graphon cycle bound (assembly of the reduction) | assembly lemma |

### Nonnegativity of `diagKernel`

`diagKernel m r q ℓ` is a real polynomial in `q, ℓ` (parameters `m, r ∈ ℕ`, `n = m − 2r`); the cycle
bound reduces to `diagKernel m r q ℓ ≥ 0` for `ℓ ∈ [−½, ½]`, `0 ≤ q ≤ 1/3`.

| File | Mathematical content | Lean names |
|------|----------------------|-----------|
| `HighDensity/RhoLemma.lean` | the sign structure of the auxiliary function `ρ` (reflection nonnegativity and the left/right windows) | `rho`, `rho_window`, `rho_reflect`, `rho_neg`, `rho_empty` |
| `HighDensity/KernelForm.lean` | the finite Beta`(r,r)` integral form of `diagKernel`; nonnegativity when `2r ≥ n` or `ℓ ≤ 0` | `gform_eq`, `diagKernel_nonneg_two_r_ge`, `diagKernel_nonneg_le_zero` |
| `HighDensity/KernelImproper.lean` | the improper `∫₀^∞` integral form of `diagKernel` (substitution `x = ℓ/(ℓ+s)`) | `kernel_form` |
| `HighDensity/KernelIntegrable.lean` | integrability of the kernel integrand on `(0, ∞)` | `kernelIntegrand_integrableOn` |
| `HighDensity/KernelReflect.lean` | the weighted-reflection inequality pairing points across `1/2 − q` | `reflection_pair_nonneg` |
| `HighDensity/KernelR1.lean` | the `r = 1` case: base length `m = 5`, and the integral reduction for `m ≥ 7` | `r1_integral_nonneg`, `diagKernel_nonneg_r1_of_integral` |
| `HighDensity/KernelIBP.lean` | integration-by-parts estimate for all `r ≥ 1`; the complete `r = 1` case | `diagKernel_nonneg_ibp`, `diagKernel_nonneg_r1` |
| `HighDensity/StripAssembly.lean` | the full `(r, ℓ)` case analysis, reducing `diagKernel ≥ 0` to the two hypotheses `Hfin`, `Hleft` | `diagKernel_nonneg` |

### The remaining strip (`m ≥ 63`, `Hleft`)

| File | Mathematical content | Lean names |
|------|----------------------|-----------|
| `HighDensity/M6Strip.lean` | the threshold bound `H(b) ≤ 2/5` and the reflection comparison at the band endpoints | `threshold_bound`, `right_condition` |
| `HighDensity/M6Reflection.lean` | nonnegativity on the right half of the band (`θ ≥ 1/6`, `ℓ > 2/5`) | `diagKernel_nonneg_strip_right` |
| `HighDensity/M6LeftEstimate.lean` | the surplus/deficit accounting on the left half, reduced to a scalar inequality | left-estimate lemmas |
| `HighDensity/M6TailFactors.lean` | per-factor scalar bounds of the tail ratio (rational, no fractional powers) | `tail_two_p_eps`, `tail_eps_b`, `tail_cn_lower` |
| `HighDensity/M6TailRatio.lean` | the same bounds raised to their integer powers (collapsing fractional exponents) | `rpow_npow_eq`, `tail_pow_p`, `cn_core` |
| `HighDensity/M6StripLeftB.lean` | the left band for `θ ∈ (1/6, 1/4]`, closed uniformly in `m` | `diagKernel_nonneg_strip_left_b` |
| `HighDensity/M6StripLeftA.lean` | the left band for `θ ≤ 1/6`, and the combined provider for `Hleft` | `diagKernel_nonneg_strip_left_a`, `diagKernel_nonneg_strip_left_ab` |
| `HighDensity/AppConstants.lean` | the uniform tail arithmetic for `m ≥ 500`, isolating the fractional-power factor `B₀` | `constA_tail` |
| `HighDensity/AppConstantsB0.lean` | the bound `B₀(θ) ≥ 201/200` (monotonicity/derivative) | `B0_ge` |
| `HighDensity/AppConstantsTail.lean` | the uniform `m ≥ 500` closure of both tail constants | `constA_m500`, `constB_m63` |

### Certificates (least-central; machine-generated data checked in Lean)

The two families below are emitted by Python scripts that serialize exact-rational data; every identity
and sign is re-checked inside Lean. Each generated file names its emitter in its header.

| File(s) | Mathematical content | Generated by |
|---------|----------------------|--------------|
| `HighDensity/HfinPolyReflect.lean` | dense bivariate `ℤ`-polynomial arithmetic (`bpEval`, Horner) so a per-pair polynomial identity is checked by `decide` on coefficient data instead of `ring` | — (hand-written) |
| `HighDensity/Hfin/P{mmm}R{rr}.lean` (196 files) | one exact Bernstein/Handelman certificate `0 ≤ diagKernel m r q ℓ` per admissible pair with odd `9 ≤ m ≤ 61` | `hfin_certs.py --gen` |
| `HighDensity/Hfin/M{mmm}.lean` (27 files) | per-`m` dispatchers over the pairs of that `m` | `hfin_certs.py --gen` |
| `HighDensity/Hfin/Aggregate.lean` | collects all dispatchers into the family `finKernel_all` (the `m ≤ 61` certificates) | `hfin_certs.py --gen` |
| `HighDensity/Sweep/Core.lean` | the exact-rational sweep target `gRatA m r` and the identity collapsing its fractional-power factor to integer powers | — (hand-written) |
| `HighDensity/Sweep/M{mmm}.lean` (219 files) | the scalar inequality `1 ≤ gRatA m r` for every admissible pair with odd `63 ≤ m ≤ 499`, by `norm_num` | `app_constants_finite_sweep.py --gen` |
| `HighDensity/Sweep/Aggregate.lean` | collects the per-`m` sweep lemmas | `app_constants_finite_sweep.py --gen` |

Generator scripts (not part of any Lean proof; they also run as independent checks):

| Script | Role |
|--------|------|
| `hfin_certs.py` | Handelman/Bernstein certificate search (LP feasibility → exact rational recovery) and Lean emission for the `Hfin` family |
| `hfin_pipeline.py` | end-to-end driver: generate all pairs, emit dispatchers, build, check |
| `app_constants_finite_sweep.py` | exact-rational certifier and Lean emitter for the `63 ≤ m ≤ 499` finite sweep |
