# The odd-cycle Goodman-type bound

A Lean 4 + Mathlib formalization of the odd-cycle homomorphism-density inequality for graphons, over a
range of edge densities and cycle lengths.

## Main theorem

For a graphon $W$ of edge density $p$ and an odd cycle $C_m$, the target inequality is

$$t(C_m, W) \;\ge\; p^{m} - p(1-p)^{m-1}.$$

In Lean (`OddCycleBound/Main.lean`, namespace `OddCycleBound`) this reads

```lean
trace mu (compPow mu W (m - 1)) ≥
  edgeDensity W mu ^ m - edgeDensity W mu * (1 - edgeDensity W mu) ^ (m - 1)
```

The project proves this in several ranges of `p` and `m`. Unconditional results hold for the graphon
alone; the all-density results for `m ≥ 9` additionally take Razborov's triangle-density lower bound as a
hypothesis.

| Lean theorem | Cycle | Density range | Hypothesis |
|--------------|-------|---------------|-----------|
| `C3_bound` | `C₃` | all `p` | — |
| `C5_bound` | `C₅` | all `p` | — |
| `C7_bound` | `C₇` | all `p` | — |
| `C9_path_bound` | `C₉` | `p ≥ 1003/2000` | — |
| `C11_path_bound` | `C₁₁` | `p ≥ 103/200` | — |
| `C13_path_bound` | `C₁₃` | `p ≥ 51/100` | — |
| `odd_cycle_regionII_large_bound` | odd `m ≥ 15` | `1/2 < p < 2/3` | — |
| `C9_conditional_bound` | `C₉` | all `p` | triangle bound up to `1003/2000` |
| `C11_conditional_bound` | `C₁₁` | all `p` | triangle bound up to `103/200` |
| `C13_conditional_bound` | `C₁₃` | all `p` | triangle bound up to `51/100` |
| `odd_cycle_regionII_conditional_bound` | odd `m ≥ 3` | `1/2 < p < 2/3` | triangle bound up to `103/200` |

### Definitions needed to read the statement

Fix a probability space $(\Omega, \mu)$ ($\mu$ a probability measure on a measurable space $\Omega$).

- **Graphon** $W : \Omega \times \Omega \to \mathbb{R}$ — a symmetric, measurable, $[0,1]$-valued
  kernel. In Lean this is `IsGraphon W μ`: `Measurable (uncurry W)`, $0 \le W(x,y) \le 1$, and
  $W(x,y) = W(y,x)$. It is the limit object of a sequence of dense graphs; $W(x,y)$ is the "probability
  of an edge" between $x$ and $y$.

- **Edge density** $p = \iint W(x,y)\,d\mu(x)\,d\mu(y)$ (`edgeDensity W μ`), the homomorphism density
  $t(K_2, W)$.

- **Cycle density** $t(C_m, W) = \int\!\cdots\!\int W(x_1,x_2)\cdots W(x_m,x_1)\,d\mu^m$
  (`trace μ (compPow μ W (m−1))`), the cyclic trace of the $(m-1)$-st power of the integral operator
  with kernel $W$.

- **Triangle-density hypothesis** `TriangleDensityLowerBoundUpTo c` — the assertion that the sharp
  Razborov lower bound on $t(K_3, W)$ in terms of $p$ holds for every graphon with $p \le c$.
  Formalizing this extremal-graph-theory theorem is out of scope, so the all-density results for
  $m \ge 9$ carry it as an explicit assumption.

The right-hand side $p^{m} - p(1-p)^{m-1}$ is the conjectured extremal value, attained by the union of a
clique and isolated vertices.

## Idea of the proof

It is cleaner to work with the complement kernel $U = 1 - W$, again a graphon, with edge density
$q = 1 - p$. Two functionals of $U$ drive the argument. The *centred degree*
$g(x) = \int U(x,y)\,d\mu(y) - q$ measures how far $x$ is from average degree; it is mean-zero. The
*compression* $A$ is the integral operator of $U$ restricted to mean-zero functions. Their interaction
is recorded by the **spectral moments**

$$s_j = \langle g,\, A^{j} g\rangle, \qquad s_0 = \lVert g\rVert^2 \ (\text{the degree variance}).$$

All of $g$, $A$, $s_j$ are defined in `Graphon.lean`.

Expanding the cyclic product $t(C_m,W) = \int \prod_i\bigl(1 - U(x_i,x_{i+1})\bigr)$ by
inclusion–exclusion telescopes — despite the $2^m$ naive terms — to an $O(m)$-term identity
(`complTrace_necklace`) in the path densities $x_j = t(P_j, U)$, and Lemma 2.4 (`PathDensity.lean`)
writes each $x_j$ as an explicit polynomial in $q$ and $s_0,\dots,s_{j-1}$. Substituting, the difference

$$\Phi_m \;:=\; t(C_m,W) - \bigl(p^{m} - p(1-p)^{m-1}\bigr)$$

becomes an explicit polynomial in $q$ and the moments $s_j$, and the theorem is $\Phi_m \ge 0$. For
$m = 3$ it collapses to $\Phi_3 = 2 s_0 = 2\lVert g\rVert^2 \ge 0$, i.e. the triangle bound is "degree
variance is nonnegative" (`cycle_bound_three`).

The one fact that makes the moments tractable is that the sequence $(s_j)$ is *Hankel-positive*: writing
$h_i = A^i g$, one has $\int h_i h_j\,d\mu = s_{i+j}$, so for any real coefficients $c_0,\dots,c_d$

$$\sum_{i,j} c_i c_j\, s_{i+j} = \int \Bigl(\sum_i c_i\, h_i\Bigr)^{2} d\mu \;\ge\; 0$$

(`General/SumOfSquares.lean`, `sos_sq_expand`). Every quadratic form of this shape is therefore a valid
"square" in the moments, and a nonnegativity certificate for $\Phi_m$ is a way of exhibiting it as a
combination of such squares. What differs between density ranges is how much room there is to do so.

**$p \ge \overline{p}$ — sum-of-squares certificates** ($\overline{p} = 1003/2000$ for $C_9$,
$103/200$ for $C_{11}$, $519/1000$ for $C_{13}$). For $C_5$ and $C_7$, $\Phi_m$ is directly a sum of
squares in the moments, so the bound holds at *every* density (`cert5_specMoment`, `cert7_specMoment`,
assembled in `BoundsC5C7`). For $C_9$–$C_{13}$, $\Phi_m$ becomes a sum of squares only after the density
constraint $q \le \overline{q}$ is used, so the certificate is a **Positivstellensatz identity**

$$\gamma(q)\,\Phi_m = \sum_i \sigma_i\, g_i, \qquad \gamma(q) \ge 0,$$

with multipliers $g_i$ from $\{\,1,\ q,\ \overline{q} - q,\ q(\overline{q} - q)\,\}$
($\overline{q} = 1 - \overline{p}$ the complement threshold) and each $\sigma_i$ a sum of squares in
the moments, so the right-hand side is manifestly nonnegative. A single such identity already proves the
bound, but the one sum of squares is large enough that checking it in Lean at once exhausts memory; so
it is broken into pieces $L_1, L_2, \dots$ — each a sum of squares in only a few of the moments and
checked on its own — whose total is $\gamma(q)\,\Phi_m$. The pieces are found numerically by a semidefinite
program and then rationalised to exact coefficients, hence large and machine-generated (`cert_scripts/`,
the `C11/*` and `C13/*` blocks).

**$1/2 < p \le \underline{p}$ — Razborov's triangle bound** ($\underline{p} = 1003/2000$ for $C_9$,
$103/200$ for $C_{11}$, $51/100$ for $C_{13}$; `Conditional`, `LowBand/`). Below the certificate
threshold the algebraic route fails, and the argument works with the eigenvalues of the graphon
operator $T_W$ itself: its top eigenvalue is $\ell := \lambda_0 \ge p$ (Rayleigh quotient at the
constant function), the rest $\lambda_1, \lambda_2, \dots$ have either sign, and

$$\sum_i \lambda_i^{2} = \textstyle\iint W^2 \le p, \qquad t(C_m, W) = \sum_i \lambda_i^{\,m}, \qquad
  t(K_3, W) = \sum_i \lambda_i^{3}.$$

Only negative eigenvalues can pull $t(C_m,W)$ below the target: with $N = \sum_{\lambda_i < 0}|\lambda_i|^{m}$
one has $t(C_m,W) \ge \ell^{m} - N$, so the bound follows once $N \le \ell^{m} - p^{m} + pq^{m-1} =:
\alpha^{m}$. Suppose not, so $z := N^{1/m} > \alpha$. Monotonicity of power sums gives
$\sum_{\lambda_i<0}|\lambda_i|^{2} \ge z^{2}$ and $\sum_{\lambda_i<0}|\lambda_i|^{3} \ge z^{3}$; with the
square-mass bound $\sum_{i\ge1}\lambda_i^{2} \le S := p - \ell^{2}$ and $\sum a_i^3 \le (\sum a_i^2)^{3/2}$
for the positive eigenvalues, the triangle density is squeezed *from above*,

$$\sum_{i\ge1}\lambda_i^{3} \ \le\ (S - z^{2})^{3/2} - z^{3} \ <\ (S - \alpha^{2})^{3/2} - \alpha^{3}.$$

But **Razborov's triangle-density theorem** pushes it *from below*: with $c \in [0,1/3]$ defined by
$p = \tfrac12 + c - \tfrac32 c^{2}$,

$$\sum_{i\ge1}\lambda_i^{3} = t(K_3,W) - \ell^{3} \ \ge\ \Theta(p) - \ell^{3}, \qquad
  \Theta(p) := \tfrac32\, c\,(1-c)^{2}.$$

The two are incompatible: the difference is monotone in $\ell$, so it reduces to $\ell = p$, and at
$\varepsilon = p - \tfrac12$ small one gets $\Theta(p) \ge \tfrac{149}{100}\varepsilon$ against a
right-hand side $< \tfrac{7}{5}\varepsilon$. The contradiction forces $N \le \alpha^{m}$, hence the
bound. ($C_9$ is $m = 9$; $C_{11}$ and $C_{13}$ have the same shape with a wider cutoff and adjusted
constants.) Formalizing Razborov's theorem is out of scope, so it enters as the hypothesis
`TriangleDensityLowerBoundUpTo` (`RazborovTriangleLower`).

For $C_{13}$ the two thresholds do not meet — the certificate needs $p \ge \overline{p} = 519/1000$ but
the argument above only reaches $p \le \underline{p} = 51/100$ — leaving the band
$51/100 \le p \le 519/1000$ covered by *neither*. It is closed **unconditionally** by the
one-eigenvalue spectral reduction below (the Region II method) specialised to $m = 13$, whose residual
step is the nonnegativity of a polynomial $P$ on a box, discharged by an **exact Bernstein
certificate**: $P$ is written as

$$P = \sum_{\beta} b_\beta\, B_\beta, \qquad b_\beta \ge 0,$$

where the $B_\beta \ge 0$ are the Bernstein basis polynomials of the box, after subdividing the box
until all coefficients $b_\beta$ come out nonnegative; then $P \ge 0$ is immediate, and the $b_\beta$ are
exact rationals Lean rechecks (`RegionII/C13Frontier`, `Certificate/C13*`).

**$1/2 < p < 2/3$, odd $m \ge 15$** (`RegionII/`). Now $q > 1/3$. The eigenvalues $\lambda_i$ of the
compression $A$ obey the spectral-energy bound

$$\sum_i \lambda_i^{2} \;+\; 2\lVert g\rVert^{2} \;\le\; p\,q$$

(`HilbertSchmidtBudget`): $A$ cannot carry more squared spectral mass than $pq$ leaves after the degree
variance, and because $q > 1/3$ this permits **at most one** eigenvalue $\alpha$ above $q$. That
eigenvalue is itself bounded,

$$\alpha^{2} + q\alpha - q \le 0, \qquad\text{i.e.}\qquad \alpha \le \tfrac{1}{2}\bigl(\sqrt{q^{2}+4q}-q\bigr)$$

(`ForcedVariance`). If there is no such eigenvalue, a direct spectral estimate gives $\Phi_m \ge 0$
(`no_frontier_odd_cycle_bound`). Otherwise let $\varphi$ be the unit eigenfunction with
$A\varphi = \alpha\varphi$ and decompose

$$g = c\varphi + g_s, \qquad c = \langle g,\varphi\rangle,\quad g_s \perp \varphi,\quad
  \lVert g\rVert^{2} = c^{2} + \lVert g_s\rVert^{2}.$$

Because $\alpha$ is the *only* eigenvalue exceeding $q$, every other eigenvalue of $A$ has modulus at
most

$$L := \sqrt{pq - \alpha^{2}} \quad (<q),$$

since the non-$\alpha$ spectrum carries total square mass $\sum_{\lambda_i \ne \alpha}\lambda_i^{2}
\le pq - \alpha^{2} = L^{2}$ (`SafeFrontier`). As $g_s \perp \varphi$ lies in the span of these
eigenfunctions, each application of $A$ to it multiplies by a factor in $[-L, L]$ — that is what keeps
its contribution to $\Phi_m$ under control. Substituting the decomposition into $\Phi_m$ gives the
explicit **master inequality** (`MasterDefect`)

$$\Phi_m \ \ge\ -R_m + A_m\,c^{2} + B_m\,\lVert g_s\rVert^{2},$$

with $R_m = \alpha^{m} + L^{m} - p\,q^{m-1}$, $A_m = 2L^{m-2} + m\,K(p,m,\alpha)$ and
$B_m = 2L^{m-2} + m\,K(p,m,L)$, where $K$ is the finite geometric sum (`directedKernel`)

$$K(p,m,\lambda) = \frac{p^{m-1}-\lambda^{m-1}}{p+\lambda} = \sum_{j=0}^{m-2}(-\lambda)^{j}\,p^{m-2-j} \ >\ 0
  \qquad (|\lambda| < p).$$

It remains to show $A_m c^{2} + B_m\lVert g_s\rVert^{2} \ge R_m$. Two inequalities, one from $U \le 1$
and one from $U \ge 0$, relate $c$ and $\lVert g_s\rVert^{2}$ to the shape of $\varphi$. Writing
$\varphi^{+}$ for its positive part and $|\varphi|$ for its absolute value, and setting
$z = \bigl(\int|\varphi|\bigr)^{2}$, $b = \langle|\varphi|,\varphi\rangle \ge 0$,
$k = |\varphi| - \sqrt z\,\mathbf 1 - b\varphi$, $K_0 = \lVert k\rVert^{2}$ (so $z + b^{2} + K_0 = 1$,
and $z \ge 2\alpha$):

$$c \ \le\ \frac{(z - 2\alpha) - 2\alpha b}{2\sqrt z}
  \quad(\text{from } U \le 1), \qquad
  \lVert g_s\rVert^{2} \ \ge\ \frac{(H - bc)_+^{2}}{K_0},\ \
  H = \frac{(\alpha - q)z + (\alpha - L)K_0}{2\sqrt z}
  \quad(\text{from } U \ge 0).$$

The first pairs $T_U\varphi \le \int\varphi^{+} = \sqrt z/2$ against $\varphi^{+}$; the second pairs
$|\varphi|$ against $T_U|\varphi| \ge \alpha$ and applies Cauchy–Schwarz. Inserting both into
$A_m c^{2} + B_m\lVert g_s\rVert^{2}$ and minimizing over the one free parameter $v \in [0,1]$ that
remains gives the exact bound (`Scalar/Huber`)

$$A_m c^{2} + B_m\lVert g_s\rVert^{2} \ \ge\ C_m\,\psi(\xi,\rho),
  \qquad \psi(\xi,\rho) = \min_{0\le v\le 1}\bigl\{\rho v^{2} + (\xi - v + v^{2})_+\bigr\}.$$

Here $\psi$ is a Huber-type envelope: $\xi - v + v^{2}$ is an upward parabola, so $(\xi - v + v^{2})_+$
is flat where it dips below $0$ and quadratic outside (the positive part is the one from the $U \ge 0$
inequality). With $d = \alpha - q$, $f = \alpha - L$ and $e = 1 - 2\alpha$,

$$\xi = \frac{4\alpha^{2} d}{e^{2}}, \qquad \rho = \frac{A_m}{B_m}\cdot\frac{\sqrt{\alpha}}{2\sqrt2\,f},
  \qquad C_m = \frac{B_m\, f \sqrt{2\alpha}\,e^{2}}{4\alpha^{2}}.$$

The whole case is thus reduced to the single scalar inequality $R_m \le C_m\,\psi(\xi,\rho)$. This is
checked by partitioning the admissible domain according to $\xi$ and $e = 1 - 2\alpha$ into three zones
(`Scalar/*`):

- **Zone A** ($\xi \ge 1$ and $e \le 1/60$) — an elementary analytic estimate (`Scalar/ZoneA`);
- **Zone B** ($\xi \ge 1$ and $e \ge 1/60$) — an exact rational box certificate (`Scalar/ZoneBReduction`,
  `Scalar/ZoneBMax`);
- **Zone C** ($\xi \le 1$, any $e$) — elementary for $e \le 1/60$ (`Scalar/ZoneCSmall`), and an analytic
  estimate together with a box certificate for $e \ge 1/60$,

the box certificates in Zones B and C being the exact Bernstein ones described above (`Certificate/*`).

Module dependencies (arrows point from a file to the files it imports; certificate block files omitted):

```
Graphon → PathDensity → Kernel, Certificate → Cycle → Necklace → BoundsC5C7 ─┐
                                                        General/* → C9, C11, C13 ─┤
                                        BasicBounds ──────────────────────────────┤
LowBand/GraphonL2Operator → CompactGraphonOperator → LowBand C9/C11/C13 → Conditional ─┤
HighDensity/* (reduction layer) → RegionII/* ─────────────────────────────────────────┤
                                                                                       ▼
                                                                                     Main
```

## Building

```
lake exe cache get     # download the prebuilt Mathlib v4.31.0 oleans
lake build -j 1        # build one module at a time (sequential)
```

Toolchain: Lean `v4.31.0`, Mathlib `v4.31.0` (pinned in `lean-toolchain` / `lakefile.toml`). Build
sequentially with `-j 1`: several certificate modules use well over `10 GB` each even single-threaded,
and a parallel build multiplies this beyond what typical machines have.

## Files

All proof files live under `OddCycleBound/`; the library namespace is `OddCycleBound`. Tables give the
mathematical content and the principal Lean names.

### Main results and integral foundation

| File | Mathematical content | Lean names |
|------|----------------------|-----------|
| `Main.lean` | the graphon-facing theorems of the table above, obtained from the complement-form lemmas | `C3_bound` … `C13_bound`, `odd_cycle_regionII_large_bound`, `*_conditional_bound` |
| `Graphon.lean` | graphon and its integral functionals: edge density `p = ∫∫W`, degree function, its mean-zero part, and the spectral moments `s_j = ⟨g, Aʲg⟩` of the centred degree operator `A` | `IsGraphon`, `edgeDensity`, `degree`, `degCentered`, `compress`, `specMoment`, `kernelOp` |
| `PathDensity.lean` | the path densities `x_j = t(P_j, W)` as explicit polynomials in `q` and the moments `s_j` (Lemma 2.4) | `pathDensity`, `pathIter` |
| `Kernel.lean` | the kernel-composition algebra: composition, iterated powers, and the cyclic trace with its rotation invariance | `comp`, `compPow`, `trace`, `trace_comp_comm`, `onesKernel` |
| `Cycle.lean` | the cycle density `cycleDensity μ W m = t(C_m,W)` and the edge-deletion inequality `t(C_m,W) ≤ x_{m−1}` | `cycleDensity`, `edge_deletion_general` |
| `Necklace.lean` | the cyclic inclusion–exclusion (telescoping) expansion of the trace of powers into path densities | necklace recursion lemmas |
| `BoundsC5C7.lean` | the `C₅` and `C₇` bounds, assembling the identity, the certificates, and edge deletion | `C5_integral`, `C7_integral`, `C7_integral_all` |
| `BasicBounds.lean` | trivial-regime facts: the cycle density is nonnegative, and the right-hand side is `≤ 0` when `p ≤ 1/2` | `trace_compPow_nonneg`, `rhs9_nonpos_of_le_half` |
| `General/Necklace.lean` | the general-`m` cyclic inclusion–exclusion identity | `complTrace_necklace` |
| `General/PathRecurrence.lean` | the general-`m` recurrence `x_{n+1} = q·x_n + Σ s_i·x_{n−1−i}` | `pathDensity_succ` |
| `General/SumOfSquares.lean` | the moment sum-of-squares engine `∫(Σ c·h)² ≥ 0` and its fixed-arity specializations | `sos_sq_expand`, `sos2var3`, `sos3` |

### Fixed-length cycle bounds `C₉`–`C₁₃`

The assembly files below combine the general identity with a sum-of-squares certificate for
$\Phi_m \ge 0$. The certificate blocks they import (`C11/*`, `C13/*`) are machine-generated data,
listed under Certificates.

| File | Mathematical content | Lean names |
|------|----------------------|-----------|
| `C9.lean` | the `C₉` bound on `p ≥ 1003/2000`, $\Phi_9 \ge 0$ certified by degree-3/bivariate sum-of-squares | `cert9_specMoment`, `C9_path_integral` |
| `C11.lean` | the `C₁₁` bound on `p ≥ 103/200`, $\Phi_{11} \ge 0$ certified piecewise by a Positivstellensatz | `cert11_specMoment`, `C11_path_integral` |
| `C13.lean` | the `C₁₃` bound on `p ≥ 519/1000`, $\Phi_{13}$ split into linear/bivariate/trivariate/quartic blocks | `cert13_specMoment`, `C13_path_integral` |

### Region II — `1/2 < p < 2/3`, odd `m ≥ 15` (`RegionII/`)

A compact self-adjoint spectral argument on the centred complement operator. The corrected reference
proof is vendored under `provenance/regionII_jul12b/`.

| File | Mathematical content | Lean names |
|------|----------------------|-----------|
| `RegionII/LargeOdd.lean` | the unconditional Region II bound for every odd `m ≥ 15` | `regionII_large_odd_bound`, `no_frontier_odd_cycle_bound` |
| `RegionII/C13Frontier.lean` | the unconditional `C₁₃` bound on the range `51/100 ≤ p ≤ 519/1000` | `C13_frontier_bound` |
| `RegionII/C13PathIdentity.lean` | the density-independent identity expressing $\Phi_{13}$ through path densities | path-identity lemma |
| `RegionII/C13FrontierAtoms.lean` | splits the spectral moments into the contribution of the eigenvalue `α` and that of its orthogonal complement | splitting lemmas |
| `RegionII/C13MomentPositivity.lean` | positivity of the `C₁₃` moment polynomial from the exact Bernstein certificates | positivity lemma |
| `RegionII/CenteredOperator.lean` | the centred complement operator | `centeredGraphonOp` |
| `RegionII/CenteredKernel.lean` | the kernel realization of the centred compression | kernel lemmas |
| `RegionII/BoundedKernelL2.lean` | the `L²` realization for signed bounded symmetric kernels | realization lemmas |
| `RegionII/HilbertSchmidtBudget.lean` | the spectral-energy bound `Σλ² + 2‖g‖² ≤ p·q` (`Σλ² = Tr(A²)`) | spectral-energy bound |
| `RegionII/SpectralFoundation.lean` | reusable compact self-adjoint spectral data for a signed kernel | `NonzeroEigenIndex`, expansion lemmas |
| `RegionII/TracePowers.lean` | trace powers of the signed centred kernel | trace-power lemmas |
| `RegionII/OneSidedPolynomial.lean` | the finite coefficient polynomial of the one-sided shift | `oneSidedShift` |
| `RegionII/FormalShift.lean` | the formal-power-series algebra behind the shift | series algebra |
| `RegionII/KernelBlockDecomposition.lean` | the direct block decomposition of the kernel | block lemmas |
| `RegionII/GraphonShiftIdentity.lean` | the one-sided shift identity for an arbitrary graphon (finite-rank approximation) | shift identity |
| `RegionII/OneSidedShift.lean` | nonnegativity and the linear-term lower bound of the shift | shift bounds |
| `RegionII/ShiftSpectral.lean` | the spectral lower bound for the linear term | spectral bound |
| `RegionII/DirectedKernel.lean` | the scalar kernel `K(p,m,λ) = (p^{m-1}−λ^{m-1})/(p+λ)` of the master inequality | `directedKernel` |
| `RegionII/FrontierTrace.lean` | the refined trace bound at the eigenvalue `α` | trace bound |
| `RegionII/Frontier.lean` | the spectrum above `q`: existence and uniqueness of the eigenvalue `α > q` | spectrum lemmas |
| `RegionII/ForcedVariance.lean` | the bound `α² + q·α − q ≤ 0` on the eigenvalue above `q` | `forced_variance` |
| `RegionII/SafeFrontier.lean` | the safe radius `L = √(pq − α²)` and the bound `|λ| ≤ L` on the rest of the spectrum | safe-radius lemmas |
| `RegionII/CouplingChannels.lean` | the two inequalities (from `U ≤ 1` and `U ≥ 0`) bounding `c` and `‖g_s‖²` | coupling lemmas |
| `RegionII/MasterDefect.lean` | the master inequality `Φ_m ≥ −R_m + A_m c² + B_m‖g_s‖²` (operator-to-scalar reduction) | `graphon_frontier_master_defect_directed` |
| `RegionII/HuberGraphon.lean` | the graphon interface to the exact Huber-objective elimination | Huber interface |
| `RegionII/Scalar/Definitions.lean` | the scalar parameters and admissible domain | `AdmissibleParams`, `frontierRadius` |
| `RegionII/Scalar/ParameterFacts.lean` | elementary facts about admissible parameters | parameter lemmas |
| `RegionII/Scalar/ShapeElimination.lean` | exact Huber shape elimination | shape lemmas |
| `RegionII/Scalar/Huber.lean` | the exact Huber minimum: compactness and dual certificates | `huberMin` |
| `RegionII/Scalar/FrontierAlgebra.lean` | scalar algebra for the ceiling on `α` | algebra lemmas |
| `RegionII/Scalar/Coordinates.lean` | the `(e, κ)` chart coordinates for the scalar problem | chart lemmas |
| `RegionII/Scalar/Elementary.lean` | elementary admissible-domain inequalities | domain lemmas |
| `RegionII/Scalar/ThreeGeometric.lean` | a three-term geometric estimate and the secant gate | zone-estimate lemmas |
| `RegionII/Scalar/Payments.lean` | the scalar accounting feeding the zone bounds | accounting lemmas |
| `RegionII/Scalar/TuranCorner.lean` | the analytic Turán extremal-boundary case | `turan_corner` |
| `RegionII/Scalar/ZoneA.lean` | the Zone A estimate | `zoneA` |
| `RegionII/Scalar/ZoneBReduction.lean`, `Scalar/ZoneBMax.lean` | the Zone B reduction and the corrected cycle-length maximization | Zone B lemmas |
| `RegionII/Scalar/ZoneCSmall.lean` | the small-`e` Zone C estimate | Zone C lemmas |
| `RegionII/Scalar/Assembly.lean` | the scalar inequality for every admissible odd `m ≥ 15` | scalar assembly |

### All-density closure under the triangle-density hypothesis

| File | Mathematical content | Lean names |
|------|----------------------|-----------|
| `Conditional.lean` | closes the remaining low bands for `m = 9, 11, 13` from the spectral data, given the triangle-density hypothesis | `TriangleDensityLowerBoundUpTo`, `C11_bound_of_razborov_theorem`, `C13_nearbipartite_bound_of_razborov_theorem` |
| `LowBand/GraphonL2Operator.lean` | the graphon as a self-adjoint `L²` integral operator | `kernelL2Op` |
| `LowBand/CompactGraphonOperator.lean` | compactness and the self-adjoint eigen-expansion / finite-rank approximation | compact-operator interfaces |
| `LowBand/C9Spectral.lean`, `C11Spectral.lean`, `C13Spectral.lean` | the countable-spectrum data `t(C_m,W) = Σ λᵢᵐ` and its use in the low-band `C₉/C₁₁/C₁₃` arguments | spectral-data structures |
| `LowBand/C9Scalar.lean`, `C11Scalar.lean`, `C13Scalar.lean` | the scalar arithmetic of the corresponding low-band arguments | scalar lemmas |

### High-density reduction layer (`HighDensity/`, shared with `../new_lean`)

The subset of the high-density reduction reused by Region II: the reduction of the cycle bound to
$\Phi_m \ge 0$, the moment expansion, and the Krylov compression producing the eigenvalue data. The full high-density
theorem lives in `../new_lean`.

| File | Mathematical content | Lean names |
|------|----------------------|-----------|
| `HighDensity/GraphonReduction.lean` | reduces the cycle bound to nonnegativity of the cyclic inclusion–exclusion sum | `cycle_bound_of_neckSum` |
| `HighDensity/MomentExpansion.lean` | rewrites that sum as a polynomial in the path densities and moments; the `m = 3` case | `neckSum_moment`, `cycle_bound_three` |
| `HighDensity/SymmetricPoly.lean` | complete homogeneous symmetric polynomials and the kernels `diagKernel`, `multiKernel` | `hsym`, `diagKernel`, `multiKernel` |
| `HighDensity/MixtureIntegral.lean` | box positivity from one-parameter positivity via a Dirichlet-mixture integral | `multiKernel_nonneg` |
| `HighDensity/Expansion.lean` | the expansion of $\Phi_m$ evaluated at a finite set of eigenvalues | expansion lemmas |
| `HighDensity/FiniteRank.lean`, `BlockPower.lean` | a finite-dimensional block-matrix identity and a recurrence for the block operator's powers | block lemmas |
| `HighDensity/AtomicSpectral.lean`, `AtomicMomentRepresentation.lean` | the eigenvalues of the compression lie in $[-1/2, 1/2]$; each moment is $s_j = \sum_k w_k \lambda_k^{j}$ | representation lemmas |
| `HighDensity/KrylovCompression.lean`, `GraphonKrylovBridge.lean` | the finite Krylov compression and the identification of its moments with `s_j` | Krylov/bridge lemmas |

### Certificates (least-central; machine-generated data checked in Lean)

The certificate blocks serialize exact-rational data emitted by scripts in `cert_scripts/`; every
identity and sign is re-checked inside Lean. Each generated file names its emitter in its header.

| File(s) | Mathematical content | Generated by |
|---------|----------------------|--------------|
| `C11/Linear.lean`, `C11/Bivar.lean`, `C11/Trivar.lean` | the linear / bivariate / trivariate sum-of-squares blocks of $\Phi_{11}$ | `cert_scripts/gen_linear.py`, `gen_bivar.py`, `gen_trivar.py` |
| `C13/Linear.lean`, `C13/Bivar.lean`, `C13/Trivar.lean`, `C13/Quad.lean`, `C13/Hankel.lean` | the linear / bivariate / trivariate / quartic / Hankel blocks of $\Phi_{13}$ | `cert_scripts/gen_linear.py`, `gen_bivar.py`, `gen_trivar.py` |
| `C13/Engine.lean`, `C13/Engine4.lean` | the multivariate Hankel sum-of-squares engine lemmas used by those blocks | `cert_scripts/gen_engine.py` |
| `RegionII/Certificate/Tree.lean`, `Intervals.lean`, `Soundness.lean`, `Coverage.lean`, `ChartIntervals.lean` | the certificate-tree format, executable rational-interval primitives, and their soundness | — (hand-written checkers) |
| `RegionII/Certificate/Bernstein.lean`, `BernsteinCube.lean` | the checked exact-rational multivariate Bernstein format | — (hand-written checkers) |
| `RegionII/Certificate/ZoneB*.lean`, `ZoneC*.lean` | the semantics and soundness of the Zone B and Zone C certificate boxes and trees | — (hand-written checkers) |
| `RegionII/Certificate/Generated.lean` | the Zone B / shared certificate token stream | `cert_scripts/regionII/emit_certificates.py` |
| `RegionII/Certificate/ZoneCChunked.lean` + `ZoneCChunks/Chunk00…21.lean` | the Zone C certificate as bounded kernel-checking chunks (22 files) | `cert_scripts/regionII/emit_zone_c_chunks.py` |
| `RegionII/Certificate/C13Generated.lean` | the exact `C₁₃` frontier Bernstein coefficient payloads | `cert_scripts/regionII/emit_c13_bernstein.py` |
| `RegionII/Certificate/C13BernsteinSound.lean` | the semantic verification of those payloads | — (hand-written) |

Generator and validation scripts (not part of any Lean proof; several also run as independent checks):

| Script | Role |
|--------|------|
| `cert_scripts/certgen.py` | exact Gram → sum-of-squares certificate generator (univariate Hankel form) |
| `cert_scripts/gen_engine.py` | emits the multivariate Hankel sum-of-squares engine lemmas |
| `cert_scripts/gen_linear.py`, `gen_bivar.py`, `gen_trivar.py`, `gen_assembly.py`, `gen_paths.py` | emit the `C₁₁`/`C₁₃` blocks, the block combiners, and the path recurrences |
| `cert_scripts/lin11.py`, `emit_lin11.py`, `extract_lin11.py`, `feas_c11.py`, `sos_feas_c11.py` | the `C₁₁` linear-block pipeline and feasibility probes |
| `cert_scripts/phi11_moments.py`, `phi13_moments.py` | the moment expansions of $\Phi_{11}$ / $\Phi_{13}$ |
| `cert_scripts/regionII/emit_certificates.py`, `emit_zone_c_chunks.py`, `emit_c13_bernstein.py` | emit the Region II certificate data files |
| `provenance/regionII_jul12b/{zoneB,zoneC}_certifier.py`, `run_all_checks.sh` | the vendored upstream exact certifiers (regression only); `VENDORED_SHA256.md` pins their hashes |
| `verify_c5_moments.py`, `verify_c7.py`, `verify_c7_moments.py`, `verify_necklace.py` | numeric double-checks of the core polynomial identities |
| `CheckGraphon.lean`, `CheckRegionII.lean` | print the axiom trail of the `C₅`–`C₁₃` and Region II theorems |
