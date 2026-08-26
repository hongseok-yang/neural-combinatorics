# Lean verification architecture

The verification development is now one Lake project under `lean/`. This file
records the implemented theorem shape and the meaning of the placeholders; it
does not promote any open graph to a positive or negative case.

## Directory contract

```text
lean/
  Taeyoung/
    Foundation/
      Graphon.lean
      HomDensity.lean
      ChromaticPolynomial.lean
      ChromaticTarget.lean
      Status.lean
      FiniteGraphEncoding.lean
    Methods/
      PureChordal/
        ... internal definitions and certificates ...
        Main.lean
      OddCycleC5/
        Internal/
        C5Bound.lean
        Main.lean
    Examples/
      Graph007.lean
      ... exactly one file per scoped Atlas class ...
      Graph208.lean
    Catalogue/
      Rows.lean
      Counts.lean
    CheckVerified.lean
  Taeyoung.lean
```

`Foundation` defines actual symmetric measurable graphons on arbitrary
probability spaces, edge and homomorphism densities, an extensional
chromatic-polynomial specification, chromatic number, the endpoint-safe target,
and the common propositions being classified. It imports no methodology.

Every proof methodology is isolated in its own directory and exposes its public
result through `Main.lean`. The supplied pure-chordal development has been
migrated into this form. The finite (C_5) method contains only the short-cycle
integral proof needed for graphs of order at most six; it does not import or
assert the general odd-cycle theorem.

## Common theorem shape

The common positive proposition is `SatisfiesLowerBound H`. It quantifies over:

- every polynomial satisfying the natural-colouring characterization of the
  chromatic polynomial of `H`;
- every natural number satisfying the minimal-colouring characterization of
  the chromatic number of `H`;
- every measurable probability space and every graphon on it; and
- every edge density in the required threshold interval.

The target is piecewise at the endpoint:

$$
\operatorname{chromaticTarget}(P,p)=
\begin{cases}
1,&p=1,\\
(1-p)^{v(H)}P\!\left(\dfrac1{1-p}\right),&p\ne1.
\end{cases}
$$

The pure-chordal bridge proves the (p=1) case separately and uses the
certificate/polynomial identity only when (p\ne1).

`ViolatesLowerBound H` is currently the logical negation of the positive
statement. Future negative-method directories may package explicit witnesses
and prove this proposition without changing the example API.

## Example-file states

There are exactly 117 `Examples/GraphNNN.lean` modules. Each defines a finite
graph and Atlas/graph6 metadata. Their `formalization` field has one of three
meanings:

- `verified`: the displayed status theorem is checked without `sorry`;
- `believed`: the catalogue status is mathematically accepted, while the
  remaining Lean bridge is deliberately represented by `sorry`;
- `unresolved`: the catalogue row is open and the module asserts only
  `SatisfiesLowerBound graph ∨ ViolatesLowerBound graph`, an instance of
  excluded middle. It does not choose positive or negative.

Currently 21 rows are `verified`, all by the pure-chordal method:

- 17 non-clique rows reuse the generated clique-tree certificates in
  `Methods/PureChordal/Certificates/{N4,N5,N6}.lean` — Atlas 17, 42, 46, 47,
  51, 106, 144, 150, 161, 162, 163, 164, 167, 195, 201, 202, 207;
- 4 complete-graph rows use the one-bag certificate
  `Certificates.cliqueDecomp` in `Certificates/Cliques.lean` — Atlas 7, 18,
  52, 208.

Atlas 106 is `K_3 \sqcup K_3`. It is covered because the pure-chordal theorem
does not assume connectivity: its certificate factors over connected
components. Atlas 7 (`K_3`) was previously attributed to the odd-cycle bound;
it is a pure chordal graph with `r = 3`, so the checked theorem applies
directly.

The certificate-to-Atlas assignment is not asserted by hand. The generator
`codes/generate_lean_examples.py` rebuilds each certificate graph from its bags
and checks it is isomorphic to the Atlas graph (`verify_certificate_map`)
before emitting any module, so the reuse cannot silently drift.

Atlas 38 imports the checked analytic (C_5) bound but remains `believed` until
the cycle-trace and finite-graph density encodings are connected. All other
classified cases are scaffolds for later method formalizations, exactly as
requested.

Graph6 strings are stable external metadata. The ordinary example graph is
defined by a transparent edge list. A verified graph6 decoder and proofs of
canonical relabelling remain future foundation work, so no theorem presently
depends on parsing graph6 text.

## Auditing

From `lean/`, run:

```powershell
lake build
lake build Taeyoung.CheckVerified
```

The read-only Lean snapshot in `Catalogue/Counts.lean` proves by kernel
computation that its generated list has 117 rows split as 55 positive,
19 negative, and 43 open.  The informal Markdown catalogue is now ahead of
that snapshot at 72 positive, 23 negative, and 22 open.  The preserved
starting baseline for this research pass was 66 positive, 23 negative, and
28 open; the new page-rooted triangle--leaf theorem closes Atlas 137 and 139,
the paw-bias Hilbert projection theorem closes Atlas 148, its exact
$C_4$ page-concentration transfer closes Atlas 145, the weighted-$K_4$
supporting-plane theorem closes Atlas 160, and the triangle--$C_4$ vertex
supporting-plane theorem closes Atlas 126, positively without changing the
negative set.  Atlas 95 and 102 have
new rooted-triangle branch proofs; Atlas 97 and 100 have the rooted
supporting-plane proofs in `notes/triangle_adjacent_leaf_tail.tex` and
`notes/triangle_two_leaf_broom.tex`; Atlas 104 has the odd-cycle one-leaf
proof in `notes/odd_cycle_one_leaf.tex`; while Atlas 166, 172, and 206
have exact counterexamples in the ordinary Turan-local catalogue family,
all awaiting formal verification.  Atlas 166 and 172 use the two-scale
realizations of negative measurable-kernel Hessian modes at $T_2$, whereas
Atlas 206 uses a one-diagonal first-variation perturbation at $T_3$.
Separately, Atlas 152 has the five-step fractional-fibre local witness in
`notes/atlas_152_fractional_fibre_local_counterexample.tex`; its formal audit
should update `lean/Taeyoung/Examples/Graph152.lean` without changing any
shared positive theorem.  The
Atlas 97 and 100 formalizations should add the two dense scalar
supporting-plane lemmas and then update
`lean/Taeyoung/Examples/Graph097.lean` and
`lean/Taeyoung/Examples/Graph100.lean`.  Atlas 104 requires the fractional
degree-weighted edge inequality, the biased probability-measure reduction,
and the scalar odd-cycle transfer before updating
`lean/Taeyoung/Examples/Graph104.lean`.  No file under `lean/` was regenerated
for this update.  Atlas 134 additionally requires the permutation
symmetrization of distributed clique-leaf exponents, the fractional
degree-weighted edge inequality, and monotonicity of
$A_r(s)/s^{r/2}$ before updating
`lean/Taeyoung/Examples/Graph134.lean`.  The proof document is
`notes/clique_distributed_leaves.tex`.  Atlas 113 requires the two-orbit
arithmetic--geometric symmetrization, the fractional degree-weighted edge
inequality, the pure-chordal diamond instance, and the scalar transfer for
$s(2s-1)^2/s^2$.  Its proof is
`notes/diamond_orbit_balanced_leaves.tex`, and the graph module is
`lean/Taeyoung/Examples/Graph113.lean`.  Atlas 119 additionally requires two
orbit symmetrizations, the conditional
square factorization at the bowtie center, Cauchy--Schwarz, the fractional
degree-weighted edge inequality, and the triangle scalar transfer.  Its proof
is `notes/bowtie_outer_leaves.tex`, and the graph module is
`lean/Taeyoung/Examples/Graph119.lean`.  Atlas 120 requires the pointwise
rooted-triangle reduction, the exact Hilbert-space square for the $T_Wd$
weight, the $P_4$ positivity normalization, Jensen under the finite measure
$W(x,y)(T_Wd)(x)\,d\mu^2$, and the scalar first-page estimate.  Its proof is
`notes/triangle_book_two_edge_tail.tex`, and the graph module is
`lean/Taeyoung/Examples/Graph120.lean`.  The reusable formal lemma should
state
$$
\int (T_Wd)\tau\geq(2p-1)\int (T_Wd)d
$$
for $p\geq1/6$, with the operator-square identity exposed separately so that
no unproved monotonicity property of $T_Wd$ enters the proof.  The informal
Atlas 123 proof uses page-orbit arithmetic--geometric symmetrization, the
positive-part rooted-triangle estimate, convexity of
$a^\alpha\max\{2a-p,0\}$ for $0<\alpha\leq1$, conditional page
factorization, and Jensen under the normalized edge measure.  Its proof is
`notes/triangle_book_page_two_edge_tail.tex`, and the graph module is
`lean/Taeyoung/Examples/Graph123.lean`.  The fractional convexity lemma should
be formalized uniformly in the real exponent $\alpha$, rather than only at
$\alpha=1/2$.  Atlas 137 and 139 now have one common arbitrary-graphon proof
in `notes/triangle_book_page_paw_branch.tex`.  Formalization should expose
the real-exponent weighted rooted-triangle lemma, edge-biased Jensen, the
fractional H\"older compression for the new-vertex leaf orientation, and the
page-orbit arithmetic--geometric symmetrization.  Their catalogue rows are
`Verified` in the current read-only Lean snapshot.  This research update did
not change any file under `lean/`.

Atlas 148 now has a full arbitrary-graphon proof in
`notes/atlas148_paw_bias_hilbert_projection.tex`.  Its low-density half
formalizes the exact kernel square $t(H,W)=\int\|T_WF_x\|_2^2$, projection
onto constants, a sharp paw-bias lemma, and the $K_3$ case of Reiher's clique
density theorem.  The latter is an explicit external analytic dependency;
formalization must import or separately prove the graphon sharp-triangle
profile rather than replace it by Goodman's weaker bound.  Its high-density
half projects onto the orthogonal pair $1,W(x,\cdot)-d(x)$, proves the edge
geometric-mean inequality, and checks a supporting line by exact rational
Bernstein coefficients on four boxes.  The graph, target, profile derivative,
all scalar factorizations, and all 91 Bernstein coefficients are reconstructed
by `codes/verify_atlas148_paw_bias_hilbert_projection.py`.  The Atlas 148 row
therefore remains `Believed`; no file under `lean/` was changed and no Lean
command was run.

Atlas 145 is reduced to Atlas 148 in
`notes/c4_triangle_page_concentration.tex`.  After integrating the two
triangle pages, reflection of the underlying $C_4$ turns the density
difference into one half of
$\int(S(x_0,x_1)-S(x_0,x_3))^2\,d\Lambda$.  Formalization should define the
finite unnormalized $C_4$ homomorphism measure, prove its reflection
invariance, and rewrite the square; no division or new analytic theorem is
needed beyond the Atlas 148 result.  The exact graph and decomposition audit
is `codes/verify_c4_triangle_page_concentration.py`.  Atlas 145 remains
`Believed`, and this update changes no file under `lean/`.

Atlas 126 now has a full arbitrary-graphon proof in
`notes/atlas126_triangle_c4_vertex_supporting_plane.tex`.  Rooting at the
unique shared vertex factors the graph into a rooted triangle and rooted
$C_4$; a two-weight Cauchy--Schwarz projection reduces the latter to the
degree $d$, $T_Wd$, and the rooted triangle density.  The low-density
supporting plane uses the same explicit $K_3$ case of Reiher's clique-density
theorem as Atlas 148, while the high-density plane needs no imported density
theorem.  The exact convex face reduction, 29,084-box rational Bernstein
tree, local zero-set patches, graph and target audit, and 46 two-block sanity
checks are reconstructed by
`codes/verify_atlas126_triangle_c4_vertex_supporting_plane.py`.
Formalization should create `lean/Taeyoung/Examples/Graph126.lean`, prove the
weighted projection, and reflect the scalar certificates.  Atlas 126 remains
`Believed`; no file under `lean/` was changed and no Lean command was run.

The informal Atlas 142 proof conditions on the tail-bearing
$K_4$ vertex, applies the triangle Goodman theorem in its link, inserts
$\tau\geq(2T_Wd-p)_+$ pointwise, and proves a sharp supporting plane in the
coordinates $(d,T_Wd-d^2)$.  Its discriminant residual is certified by 56
strictly positive Bernstein coefficients.  The proof and exact coefficient
matrix are in `notes/k4_two_edge_tail.tex`; the graph module is
`lean/Taeyoung/Examples/Graph142.lean`.  Formalization must not replace this
argument by the still-unproved weighted-link inequality recorded in failed
attempt 18.

The informal Turan-local methodology
also contains the small-support needle polynomial, the higher-order Boolean
threshold audit, the continuum-flat threshold simplex certificates, the exact
coarse-profile product-triangle certificates with a single aggregate threshold
repair, the full arbitrary-fibre pair-kernel certificates for Atlas 130, 153,
171, 174, and 188, the Atlas 152 arbitrary-fibre overlap obstruction and its
failed total-mass, geometric-mean, and independently
minimized overlap contractions, the exact failure of the stronger
$4\mathbb E[uv]^2$ contraction, the full Atlas 152 two-profile
indicator-fibre theorem (overlap monotonicity, the diagonal factorization,
and six degree-eight four-simplex determinant certificates), the
profile-count-free Atlas 152 axis theorem (zero-displacement deletion and
the exact same-axis/cross-axis factorizations), the Atlas 152
comparable-mean theorem for arbitrary fractional fibres (the deficit
four-simplex, its seven central and two side simplices, their exact
face-to-face incidence audit, and nine exact
degree-four coefficient certificates), the equal-displacement Atlas 152
theorem (one three-simplex, four face-to-face-audited tetrahedra, and four
exact degree-four certificates), the bounded-dispersion Atlas 152 theorem for arbitrary
fractional fibres (symmetry, two Gram
marginals, Jensen, the exact scalar margin, the
$12(\mathbb E|e_u|+\mathbb E|e_v|)$ integrated error, its
$L^2$ consequence, and its $24\varepsilon$ $L^\infty$ corollary), plus the
positive pointwise theorem for the entire
comonotone nested-fibre subcone, and the exact Atlas 152 five-step
fractional-fibre counterexample (including its negative $2\times2$ kernel
matrix and full $5^6$ assignment enumeration), the
exact interior continuum zero set, the full mass-cone
copositivity and zero-face audit, and exact no-hit certificates at
$T_{\chi(H)-1}$ and $T_{\chi(H)}$ on the historical audit snapshot.  The companion
axis-zero-set theorem for Atlas 137, 139, 145, and 148 should be formalized
as a complementary small-support result. Its normalized needle
identities are $4u^2v^2,4u^2v^2,8u^2v^2,4u^2v^2$. On the union of the two zero
axes, all same-axis and opposite-axis arbitrary-fibre pair kernels, for both
Boolean mutual-cell endpoints, reduce to
$\kappa_H(1-x)(1-y)$ with
$\kappa_H=1/2,1/2,1,3/4$. Affinity gives every mutual-cell value, and Fubini
gives the integrated square $\kappa_H(\int(1-x))^2$. The formal statement
must retain the caveat that $x=1$ leaves arbitrary exceptional-internal
kernels invisible at quadratic order. They cannot be contracted to their
means at cubic order: the equal-mean kernels $R\equiv1/2$ and
$R=\left(\begin{smallmatrix}1&1/2\\1/2&0\end{smallmatrix}\right)$ give cubic
pairs $(5/512,27/2048)$ on Atlas 137 and 139, $(1/64,5/256)$ on Atlas 145,
and $(1/128,5/512)$ on Atlas 148. A formal higher-order continuation must
retain rooted-degree and mixed internal moments. That continuation is now
available for every fixed endpoint direction. If the two endpoint types
have masses $\alpha,\beta=1-\alpha$ and arbitrary internal graphons
$R_0,R_1$, the raw and formally repaired cubics coincide. They are
$$
 \frac{\alpha^3(t(K_3,R_0)+2t(P_3,R_0))
 +\beta^3(t(K_3,R_1)+2t(P_3,R_1))}{8}
$$
for Atlas 137 and 139, and
$$
 \frac{\alpha^3t(P_3,R_0)+\beta^3t(P_3,R_1)}2,
 \qquad
 \frac{\alpha^3t(P_3,R_0)+\beta^3t(P_3,R_1)}4
$$
for Atlas 145 and 148. The cross-type kernel cancels exactly. Jensen gives
$t(P_3,R_i)\ge(\int R_i)^2$, which settles the above-threshold raw branch;
the below-threshold branch has an exact nonnegative repair to density $1/2$.
The statement is uniform in endpoint data. If $D>0$ is the raw density
excess coefficient, the exact identity
$$
 \alpha^2r_0-D-\beta^2
 =\beta^2(1-r_1)+2\alpha\beta(1-c)
$$
and Jensen make the cubic at least $q_HD^2$, with
$q_H=1/4,1/4,1/2,1/4$. Retaining only the positive colourings with three
exceptional vertices gives the factor $(1-2\varepsilon)^6$ and exact support
radii $1/10,1/10,1/20,1/32$. Formalize the finite coloured-moment
enumeration, density coercivity, and positive-subintegral bound. The
good-set continuation then closes the complete arbitrary-fibre zero-axis
cone with the common support radius $1/100$. Its formal interface should
define the total fibre deficits $d_0,d_1$, the raw excess
$E=D_0+2d_1-(d_0+d_1)/\varepsilon$, and prove
$$
 E\leq D_0,\qquad
 d_0+d_1\leq\frac{\varepsilon D_0}{1-2\varepsilon},
 \qquad D_0\leq\alpha^2r_0.
$$
With good-set threshold $1/16$, Markov's inequality leaves internal edge
mean at least $r_0(1-32\varepsilon/(1-2\varepsilon))$; the $P_3$ inequality
and an eight-factor union bound give
$$
 t(H,W_{\rm raw})\geq
 q_HE^2\varepsilon^3
 \frac12(1-2\varepsilon)^4(1-34\varepsilon)^2.
$$
The four exact slacks at $1/100$ are
$6276868289/125000000000$ twice,
$3777868289/62500000000$, and
$1277868289/125000000000$. The final gluing theorem removes the axis
restriction and gives the common support radius $1/10000$. For a general
profile define
$$
 w=\min(u,v),\quad x=\max(u,v),\quad
 m=\int w,\quad n=\int(1-x),\quad
 B_1=\int uv,\quad A_2=\int u^2v^2,
$$
partition by $u\leq v$ or $v<u$, and let
$D_0=\int R-2\mu\{v<u\}$. Formalize the exact density identity
$$
 \delta=\varepsilon(m-n)
 +\varepsilon^2(D_0+2d_1-2m_0)
$$
and its consequence $(1-2\varepsilon)n<m+\varepsilon D_0$ when
$\delta>0$. In the case $m\geq2\varepsilon D_0$, the pointwise inequalities
$(w+x-1)_+\leq uv$ and
$w\leq2uv+(1-w-x)_+$ imply $m\leq7B_1$; the one-exceptional-vertex
subintegral is
$$
 t(H,W)\geq c_H\varepsilon(1-2\varepsilon)^5A_2,
 \qquad c_H=1/16,1/16,1/8,1/16.
$$
In the complementary case,
$n<3\varepsilon D_0/(1-2\varepsilon)$; projection to the nearer axis and
the good-set proof give
$$
 t(H,W)\geq q_HD_0^2\varepsilon^3
 \frac12(1-2\varepsilon)^4(1-98\varepsilon)^2.
$$
Formalize the two exact minimum slacks
$40471936237751224951/2450000000000000000000$ and
$371296887848737563915027482401/
3123750125000000000000000000000$. No profile regime remains in the
single-exceptional-set hierarchy. The companion
arbitrary-$L^\infty$ theorem turns the strict interior first variation into
an explicit graphon-local stability radius at every $T_k$ with
$k\geq\chi(H)$ for the 29-row pre-Atlas-152 snapshot, and hence for all 22
current open rows; it applies to arbitrary
measurable cell kernels, not only step perturbations. Its tangent-cone
extension gives exact threshold radii for Atlas 127, 147, 151, 157,
168, 169, 178, 181, 185, 194, 196, and 199, as well as the now-positive
Atlas 126 and 160; formalization should use
$D-O\geq0$ and the slope
$\min\{A_H(r),(2A_H(r)+B_H(r))/4\}/r^{v(H)-1}$. A second quantitative
threshold theorem now covers the coercive critical-addition rows Atlas 43,
118, 122, 124, and 203. Formalization should split $U=F-V$ according to the
diagonal and off-diagonal Turan cells, define the normalized cell means $d_i$
and rooted-degree squares $s_i$, and set $S=\sum_i s_i$. The key measurable
pair-energy lemma is
$$
 D^2\le S/r^3,
 $$
and every term containing at least three copies of $F$ is bounded by
$K_D\lVert F\rVert_\infty S$. Every nonlinear term containing $V$ is bounded
by $K_O\lVert U\rVert_\infty\int V$ and is absorbed by the strict deletion
slope $\beta=B_H(r)/(2r^{v(H)-1})$. The exact Hessian coercivities are
$q_H=1/32$ for Atlas 43, $1/64$ for Atlas 118, 122, and 124, and $11/729$ for
Atlas 203. The certified radii are respectively $1/5544$, $1/33808$ for each
of the middle three rows, and $1/14251389$.

Two further lemmas now close every remaining threshold neighbourhood. For
Atlas 153, 171, 174, and 188, formalize the exact factorization
$$
 \Phi_H(p)=p(2p-1)C_H(p).
$$
The quadratic $C_H'$ has positive leading coefficient and negative
discriminant, while the four values $C_H(7/12)$ are
$-47/1728,-67/1728,-17/1728,-37/1728$. Hence $C_H<0$ on
$[1/2,7/12]$, and nonnegativity of homomorphism density proves the theorem
for every graphon in this strip. The induced threshold $L^\infty$ radius is
$1/12$.

For Atlas 130, 137, 139, 145, and 148, formalize the positive
two-defect-colouring subintegral. Relative to the balanced $T_2$ partition,
write the two diagonal additions as $F_0,F_1$, the cross deletion as $G$,
and $s=\int F_0+\int F_1$. Threshold feasibility gives
$0\le p-1/2\le s/4\le\eta/2$. Retaining only vertex two-colourings with
exactly two monochromatic edges gives
$$
 t(H,W)\ge(1-\eta)^{e(H)-2}R_H(F_0,F_1),
$$
where the exact arbitrary-kernel coercivities
$R_H\ge q_Hs^2$ are
$$
 q_H=1/16,1/32,1/32,7/128,5/128.
$$
Direct scalar comparison with the five factored targets gives radii
$1/16,1/8,1/8,1/16,1/40$. The exact radius slacks are
$130511/524288$, $34705/262144$ on each middle pair,
$7595623/16777216$, and $153726161/819200000$. Together with the strict and
critical-addition branches, this proves a complete threshold $L^\infty$
neighbourhood theorem for all 22 current open rows. The high-density
companion proves a uniform explicit positive gap for every fixed
bounded normalized complement on the same 29-row snapshot and hence all 22
current open rows. The exact
one-clique-hole theorem in
`notes/singular_clique_complement_high_density_test.tex` additionally
excludes the canonical singular family
$1-\mathbf 1_{S\times S}$ on the complete admissible interval for all 29
snapshot rows. It also excludes every finite or countable union of clique blocks,
with an arbitrary leftover dust set on which the graphon is zero, on the
complete admissible interval by exact bivariate rational and
$\mathbb Q(\sqrt3)$ Bernstein certificates. The complete-cut complement is
the two-block special case, while one clique plus dust is the canonical
persistent-hub complement. Its
power-sum defect theorem further excludes every finite or
countable complete-multipartite complement uniformly at sufficiently high
density, including the critical $r\asymp1/(1-p)$ scale and arbitrary part
imbalances. Only a non-clique or otherwise moving singular shape remains.
For an arbitrary complement, the exact universal rank-two term is the
positive combination of degree variance
$t(P_3,V)-q^2$ and transitivity defect
$t(P_3,V)-t(K_3,V)$; their common zero set is exactly the balanced Turan
family. The independent operator-spectral theorem closes the higher-rank
bridge for every arbitrary measurable complement of exact constant degree,
uniformly at sufficiently high density and without an equal-cell or
finite-step hypothesis. The further theorem in
`notes/maximum_degree_complement_high_density_stability.tex` removes exact
regularity whenever the complement degree is uniformly small. Its
tree-indexed Markov representation proves that every tree density lies
between its constant-degree value and the matching star moment; a pointwise
path telescoping bounds every long failed closure by triangle failures. The
resulting exact inequality is
$$
\Gamma_H(1-V)\ge
(c_H-\Lambda_H\Delta)\bigl(t(P_3,V)-q^2\bigr)
+(N_3(H)-\Omega_H\Delta)
 \bigl(t(P_3,V)-t(K_3,V)\bigr),
\qquad \Delta=\lVert d_V\rVert_\infty.
$$
All 29 snapshot rows have explicit positive rational radii, from $7/8079$ to
$8/161$. Formalization should expose the tree Markov identity, the
relative-entropy and Holder bounds, the scalar path-chain inequality, and the
component-product telescoping before certifying the four finite constants.
This theorem still leaves high-density families with complement-degree hubs
bounded away from zero. The exact companion in
`notes/two_block_hub_high_density_stability.tex` closes the full constant
two-block hub cube: if an exceptional block has mass $0\le s\le1/3$ and
the complement values on its cut and diagonal are arbitrary
$a,r\in[0,1]$, then every current open row is nonnegative. The proof is the
exact vertex-subset density formula followed by native trivariate Bernstein
nonnegativity after dividing out the endpoint factor $s$. Formalization
should certify the complete coefficient arrays reconstructed by
`two_block_hub_high_density_audit`; no status module changes. Persistent hub
families with nonconstant fibres are further controlled by
`notes/arbitrary_fibre_hub_high_density_stability.tex`. If $W=1$ on a
complete core $B^2$, the cut and exceptional-square kernels may be arbitrary.
Writing $s=\mu(A)$ and
$E_2=\int_A(\int_B(1-W(z,y))\,d\mu_B(y))^2d\mu_A(z)$, the theorem proves
$$
\Gamma_H(W)\ge s(2e(H)-v(H))E_2-K_Hs^2.
$$
All 29 snapshot rows have exact adaptive radii $s\le\rho_HE_2$, with
$9/817\le\rho_H\le7/172$. The formal proof should separate the exact
zero/one-exceptional-vertex contribution, the scalar degree-sequence
convexity lemma, and the absolute chromatic-target remainder. A sharper
global-union-bound comparison proves
$$
\Gamma_H(W)\ge
s(1-s)^{v(H)-1}(2e(H)-v(H))E_2-C_Hq^2.
$$
When the complement is supported only on the cut, this closes every energy
scale for an explicit fixed interval $s\le\sigma_H$, with radii from
$9/817$ to $1/22$. The union-bound remainder is moreover superadditive
between cut and internal defect edges. Combining the exact cut gain with the
maximum-degree theorem for the internal-only complement and one Young
inequality proves the fully arbitrary complete-core theorem: whenever
$W=1$ on $B^2$ and $\mu(A)=s\le\tau_H$, both remaining kernels are arbitrary.
The 29 snapshot radii range from $63/1963067$ to $7/9825$. Formalization should
add the superadditive remainder identity, the scaled internal variance bound,
and the target-difference estimate before certifying $D_H,g_H,\Lambda_H,
N_3(H),\Omega_H,\tau_H$. This already permits any number of interacting hubs
inside $A$. The independent culmination in
`notes/arbitrary_graphon_high_density_stability.tex` removes the complete-core
hypothesis. For arbitrary $V=1-W$, split at
$A=\{d_V>\delta_H\}$ with $\delta_H$ equal to half the maximum-degree radius.
The $B^2$ residual is controlled by the maximum-degree theorem, while Markov's
bound and the quantitative complete-core margin control all pairs incident to
$A$. The mixed target estimate
$$
|R_H(x+y)-R_H(x)-R_H(y)|\le J_Hxy,
\qquad J_H=\sum_{j\ge2}j(j-1)|b_j|,
$$
then gives a uniform arbitrary-graphon radius
$$
\varepsilon_H=\min\{\delta_H^2/2,\delta_H\tau_H/2,
(2e(H)-v(H))\delta_H^2/(16J_H)\}.
$$
All 29 snapshot radii are positive, ranging from $49/895333652544$ to $1/703570$.
Formalization should isolate the polynomial mixed-remainder lemma, the
measurable high-degree split, Markov's bound, and the elementary fibre-energy
lower bound before certifying the exact table. Thus the high-density endpoint
is closed for every graphon. Symmetric doubly
stochastic equal-cell matrices are a corollary; on the canonical segment
$B_\theta=(1-\theta)I_r+\theta J_r/r$, exact bivariate Bernstein
certificates remove the large-$r$ restriction for all 29 snapshot rows and every
$r\geq\chi(H)-1$; Atlas 188 uses one explicit quadratic sum-of-squares
repair. Most of these are no-hit methodologies, but the fractional-fibre
test changes Atlas 152 to negative. A formal worker should therefore update
the methodology documentation and shared polynomial-audit layer and inspect
`Examples/Graph152.lean`; no other example status file changes. The second command
prints the axioms of the checked pure-chordal and (C_5) theorems; these must
not contain `sorryAx`. Warnings about `sorry` elsewhere are expected scaffolds
and must correspond exactly to rows marked `believed`.

Regenerate the example layer with:

```powershell
python codes/generate_lean_examples.py
```

Tensor notation in generated text always has lexical whitespace, for example
`T_a \otimes T_b`; the operator command is never concatenated with the next
symbol.
