# Failed proof attempts and reusable warnings

This is a proof-safety ledger for the Taeyoung-conjecture catalogue. Its purpose is to prevent an attractive but invalid argument from being reused after the surrounding calculation has been forgotten. An entry means only that the stated route failed; it does not determine whether the graph itself is positive or negative.

The standing rule is: numerical evidence may suggest a lemma, but a catalogue row moves to positive only after a proof for every graphon on the full required density interval.

## 1. Universal-vertex and join closure

**Tempting claim.** If $F$ is positive, then $K_1\vee F$ is positive; more generally, positivity is preserved by graph joins.

**Why it fails as an argument.** For a graphon $W$, integrating the universal vertex produces a rooted density in a reweighted neighbourhood graphon. Its edge density and normalization depend on the root. The hypothesis for $F$ cannot simply be applied with the original global edge density $p$. There is no general inequality that moves the nonlinear target through this rooting operation.

**Safe replacement.** Use only a separately proved cone theorem whose hypotheses are checked for the particular base graph. The finite list in `notes/six_verified_base_cones.tex` and the structural theorem in `notes/forest_cone_graphon_bound.tex` are not evidence for a general closure rule.

**Recovery condition.** A valid general lifting theorem would need an explicit rooted graphon identity, a pointwise or averaged bound valid for all root degrees, and a proof of the resulting one-variable inequality on the full density range.

## 2. Mixed-size chordal clique trees

**Tempting claim.** The entropy proof in `notes/pure_chordal.tex` extends unchanged to every chordal graph, even when maximal cliques have different sizes.

**Why it fails as an argument.** The construction glues uniform clique homomorphisms along separator marginals. Uniform homomorphisms of $K_a$ and $K_b$, with $a\ne b$, do not in general induce the same probability distribution on a common $K_s$. Conditional sampling from the child therefore need not reproduce the law already present on the separator. The asserted entropy increment is then taken under the wrong marginal.

**Why the pure case is different.** When every maximal clique is $K_r$, coordinate-permutation symmetry gives one common separator law for each separator size. An induction shows that every exposed clique retains the uniform $K_r$-homomorphism marginal. This invariant is now written explicitly in `notes/pure_chordal.tex`.

**Recovery condition.** One needs compatible clique measures for all bag sizes, or a new weighted entropy inequality that accounts for the mismatch. Neither is currently proved.

## 3. Completing small chordal bags to a common size

**Tempting claim.** Enlarge every smaller maximal clique of a mixed chordal graph to size $r$, apply the pure-chordal theorem to the supergraph, and delete the added vertices.

**Why it fails as an argument.** Although deleting edges or vertices can compare some homomorphism integrands, the chromatic target changes in the wrong direction. The pure completion generally has a smaller multipartite target than the original graph. A lower bound by that smaller quantity does not prove the required original bound.

**Recovery condition.** A completion proof must establish a target comparison in the required direction as an explicit polynomial inequality, not merely a graph containment relation.

## 4. Arbitrary pendant-leaf closure

**Tempting claim.** If $F$ is positive, attaching a leaf to any vertex preserves positivity, because the target gains a factor $p$.

**Why it fails as an argument.** If $f(x)$ is the rooted density of $F$ at the attachment vertex and $d(x)=\int W(x,y)\,dy$, then

$$
t(F+\text{leaf},W)=\int f(x)d(x)\,dx.
$$

The known bound controls $\int f$, while the desired conclusion would require a positive-correlation inequality between $f$ and $d$. No such inequality holds merely from their means.

In fact, even the first instance needed for a triangle fails as a universal
rooted correlation statement.  Partition the probability space into sets
$A,B$ of measures $1/3,2/3$, and take the two-step graphon

$$
W=\begin{pmatrix}0&1\\1&1/3\end{pmatrix}
$$

on $A,B$.  Exact integration gives

$$
p=\frac{16}{27},\qquad
t(K_3,W)=\frac{116}{729},\qquad
t(\text{paw},W)=\frac{616}{6561}.
$$

Therefore

$$
t(\text{paw},W)-p\,t(K_3,W)
=-\frac8{19683}<0.
$$

This does not contradict the proved paw lower bound: the latter uses a
weighted rooted-Goodman inequality and compares directly with the chromatic
target, not with $p\,t(K_3,W)$.  It does rule out a perfect-elimination
induction that attaches each simplicial leaf by multiplying the current
homomorphism density by $p$.

**Safe replacement.** Whiskering may be used only in the exact form already proved in the accepted whiskering document, with all of its hypotheses. Other leaf configurations require a new rooted estimate.

## 4a. Normalized tree domination for the Atlas 100 broom

**Tempting claim.**  In the pointwise rooted-triangle reduction for Atlas 100,
let $Z=t(S_4,W)=\int T_W(d^2)$, where $S_4$ is the three-edge star, and let
$K$ be the density of the five-edge tree obtained by attaching a two-edge
path at a leaf of $S_4$.  Prove the needed weighted mean by the stronger
normalized domination

$$
K^3\ge Z^5.
$$

Together with $Z\ge p^3$, this would imply $K/Z\ge p^2$.

**Why the stronger claim is false.**  The five-edge tree has smaller
bipartition class of size $2$.  The characterization of tree-versus-star
domination in Behague--Crudele--Noel--Simbaqueba,
[*Sidorenko-Type Inequalities for Pairs of
Trees*](https://arxiv.org/abs/2305.16542), says that a tree $H$ dominates the
$k$-vertex star precisely when
$e(H)\ge(k-1)\sigma(H)$.  Here this would require
$5\ge3\cdot2=6$, which fails.  Thus some finite host violates the proposed
normalized inequality.

**The weaker universal claim also fails.**  Write
$T=S_4\sqcup2K_2$, so that $t(T,W)=Zp^2$, and let $H$ denote the five-edge
tree defining $K$.  The forest-domination linear program of
Behague--Crudele--Noel--Simbaqueba has a particularly short exact dual
certificate here.  Give weight $5/2$ to the centre vertex of the $S_4$
component of $T$, weight $1$ to each of the two isolated $K_2$ edges, and
weight zero to every other vertex and edge of $T$.  Since $H$ is connected,
each homomorphism $H\to T$ lands in one component.  If it lands in $S_4$,
the centre receives one bipartition class of $H$, of size $2$ or $4$, so its
dual load is at least $2(5/2)=5$.  If it lands in either $K_2$, all five
edges of $H$ load that target edge, again giving load $5$.  Thus the dual is
feasible and has objective
$$
\frac52+1+1=\frac92<5=e(T).
$$
By the exact forest-domination characterization, $H$ does not dominate
$T$.  Hence some finite host violates
$$
t(H,G)^5\ge t(T,G)^5,
$$
equivalently the universal inequality $K\ge p^2Z$.

**Resolution by an edge-density-sensitive route.**  Atlas $100$ is now
positive, but neither failed domination statement is repaired or used.  The
proof in `notes/triangle_two_leaf_broom.tex` keeps the rooted variables
$d$ and $A=T_Wd$, uses
$$
T_W(d^2)\ge \frac{A^2}{d},
\qquad
\tau\ge(2A-p)_+,
$$
and proves a sharp supporting-plane inequality on the genuinely dense
feasible region
$$
0\le A\le d,
\qquad A\ge d-(1-p),
\qquad p\ge\frac12.
$$
The supporting plane contains a multiple of $A-d^2$, whose integral is
zero.  This gives the exact target after integration and explains precisely
how the dense-range hypothesis supplies information absent from universal
forest domination.  Future workers may reuse that rooted supporting-plane
method, but must not cite it as $K\ge p^2Z$; that universal inequality
remains false.

## 5. Vertex gluing of unrelated positive graphs

**Tempting claim.** If two positive graphs are identified at a vertex, their rooted densities multiply and hence so do their lower bounds.

**Why it fails as an argument.** The glued density is $\int f(x)g(x)\,dx$. Separate lower bounds for $\int f$ and $\int g$ give no lower bound for the integral of the product: the two nonnegative rooted densities may be negatively correlated.

**Safe replacement.** Use proved self-amalgamation theorems only. Their symmetry or conditional-expectation hypotheses supply structure absent from arbitrary gluing.

## 6. Two leaves attached at different triangle vertices

**Attempt.** For a triangle with leaves at two distinct roots, use

$$
W(x,y)W(y,z)\ge W(x,y)+W(y,z)-1
$$

inside the rooted integral and reduce to moment terms $J_1,J_2$.

**Failure.** The resulting expression contained $2J_2-J_1$. A lower bound for $J_1$ was substituted even though $J_1$ has a negative coefficient. This reverses the useful direction and invalidates the proposed bound. Available upper estimates for $J_1$ were too weak to recover the exact target on all $p\ge 1/2$.

**Resolution by a different route.** The signed-moment route above remains invalid, but the graph is no longer open. The geometric-mean argument in `notes/two_root_triangle_leaf_cones.tex` symmetrizes the two rooted degree powers, compresses them to $Z=\sqrt{d(x)d(y)}$ under the edge-biased measure, proves $\mathbb E Z\ge p$ by two Cauchy--Schwarz inequalities, and applies Jensen to $z^n(2z-1)_+^m$. This repairs precisely the missing lower-bound direction and proves the larger two-root book-edge leaf family. The invalid substitution into $2J_2-J_1$ must still not be reused.

## 7. Odd unicyclic graphs with attachments at several cycle vertices

**Tempting claim.** Apply the weighted odd-cycle Goodman inequality independently at each attachment root and multiply the conclusions.

**Why it fails as an argument.** A one-root estimate controls one marginal. Attachments at several cycle vertices require a joint correlation estimate for several rooted cycle variables. Their product is not controlled by the individual averages. The difficulty is especially visible below $p=2/3$, where crude pointwise degree bounds have no useful positivity.

**Additional failed route.** Replacing the rooted quantities by a convex degree polynomial and applying Jensen produced a convex envelope strictly below the chromatic target on part of the required interval. Thus that relaxation loses essential correlation information.

**Recovery condition.** Prove a genuine multi-root odd-cycle inequality, or find a decomposition covered by an accepted amalgamation theorem.

## 8. Pointwise degree and minimum-degree substitutions

**Tempting claim.** From average degree $\int d=p$, treat $d(x)\ge 2p-1$, $d(x)\ge p$, or a similar inequality as holding pointwise.

**Why it fails.** Edge density is only an average. An arbitrary graphon may have points of degree zero even when $p$ is large. No regularity, minimum degree, or pointwise lower bound is available unless it is explicitly proved from additional hypotheses.

**Safe rule.** Every use of Jensen, Cauchy--Schwarz, or a pointwise inequality must display the actual random variable, its measure, the sign of every coefficient, and whether the needed input is an upper or lower bound.

## 9. Injective copies versus homomorphism densities

**Tempting claim.** A count of injective copies in a finite host graph is automatically the graphon homomorphism density used by the conjecture.

**Why it fails as an exact statement.** Homomorphism counts include all maps. Injective and non-injective normalizations differ at finite $n$, even though their difference is $O_H(1/n)$. Passing between them without a collision estimate creates a gap.

**Safe replacement.** Use homomorphism counts throughout, or state the collision bound explicitly. The revised `notes/pure_chordal.tex` avoids finite-host counts entirely and works directly with graphon integrals.

## 10. Unjustified graphon approximation

**Tempting phrase.** “Prove it for finite graphs and pass to graphons by the usual approximation argument.”

**Why it is inadequate for formal verification.** The precise approximants, simultaneous convergence of every density in a quotient, treatment of zero denominators, and continuity form are left implicit.

**Safe replacement.** Prefer a direct graphon proof when available. The pure-chordal proof uses $W_\varepsilon=\varepsilon+(1-\varepsilon)W$ and the explicit estimate $|t(F,W_\varepsilon)-t(F,W)|\le e(F)\varepsilon$. If finite-host approximation is genuinely necessary elsewhere, state a simultaneous $W$-random sampling lemma and prove its collision and variance bounds.

## 11. Zero denominators at threshold densities

**Tempting manipulation.** Divide by a clique density or by a factor such as $A_r(p)$ throughout the closed interval.

**Why it fails.** At the Turán threshold $p=1-1/(r-1)$, one has $A_r(p)=0$, and extremal graphons can also have $t(K_r,W)=0$. A quotient proof silently excludes the equality case.

**Safe replacement.** Keep the proof cross-multiplied through the threshold, as in the revised pure-chordal certificate proof. If division is unavoidable, split off the threshold and prove every denominator positive before dividing.

## 12. Tensor--Turán numerical evidence

**Tempting claim.** Failure of a tensor search to find a counterexample supports positivity.

**Why it fails.** The search covers only a finite, highly structured family of graphons and cannot certify an inequality over all graphons. Floating-point comparisons near equality can also have the wrong sign.

**Safe rule.** Tensor searches may discover negative certificates, which must then be checked exactly. They never move a graph to positive. Per the positive-only research scope, do not run or extend these searches while looking for positive results.

## 13. TeX tensor-token parsing

**Observed failure.** Concatenating the `\otimes` command immediately with the following `T` makes TeX read one undefined control sequence instead of an operator followed by the symbol $T$.

**Safe spelling.** Always put lexical whitespace around the operator and before the next command or letter:

```tex
U \otimes W
\bigotimes_{j=1}^{Q} T_{Q(k-1)+j}
T_a \otimes T_b
```

Generated strings should join factors with the literal separator `" \\otimes "`. A repository check should reject every operator command that is immediately followed by a letter rather than lexical whitespace.

## 14. Higher-rank page-book leaves from unweighted Moon--Moser

**Tempting claim.** Replace the common edge in the page-rooted triangle-book theorem by a common $K_{r-1}$, attach each page vertex completely to that spine, distribute private leaves among the pages, and repeat the same H\"older compression using the ordinary Moon--Moser clique ratio.

**Precise obstruction.** Let $t_j=t(K_j,W)$, let $c_r(p)=1-(r-1)(1-p)$, and let $I_h$ be the density of $K_r$ with a real degree weight $d^h$ at its page vertex. If there are $m$ pages and $n$ leaves, H\"older gives an exponent $\alpha=n/m$ and reduces the argument to

$$
t_{r-1}^{,1-m} I_\alpha^m.
$$

The exact chromatic target would follow from the weighted ratio

$$
I_\alpha\ge p^\alpha c_r(p)t_{r-1}.
$$

The accepted common-leaf estimate supplies only

$$
I_\alpha\ge p^\alpha A_r(p)
=p^\alpha c_r(p)A_{r-1}(p),
$$

while Moon--Moser gives $t_{r-1}\ge A_{r-1}(p)$. Thus the available replacement is smaller than the required one; substituting it into the negative power $t_{r-1}^{,1-m}$ loses the exact target. This is a direction failure, not unfinished algebra. In particular, the unweighted adjacent-clique inequality does not prove the needed fractional-degree-weighted ratio.

**Valid special case and recovery condition.** For $r=3$, `notes/page_rooted_triangle_book_leaves.tex` proves the stronger real-exponent rooted-triangle estimate directly, so the page-rooted triangle family remains valid. For $r\ge4$, including the analogous route toward Atlas 178, no status may change unless the displayed weighted ratio (or a different sufficient joint rooted inequality) is proved for arbitrary graphons on the full threshold interval.

**Failed sharper-recurrence repair for Atlas 178.** A more informative valid
clique inequality is

$$
t(K_4)\ge \frac12\left(\frac{3t(K_3)^2}{t(K_2)}-t(K_3)\right).
$$

After symmetrizing the half-weight as $d^{1/8}$ on all four clique vertices,
this recurrence does retain the triangle density of the biased graphon.  On
the sharp Goodman boundary $q=r(2r-1)$ it becomes
$\Gamma(q)=q(3r-2)$, and exact differentiation really does show that
$\Gamma(q)/q^{4/3}$ and $\Gamma(q)/q^{8/7}$ are increasing on
$[2/9,1]$; the cleared numerators are $2(3r^2+r-1)$ and
$2(15r^2-5r-1)$.  The attempted bridge to the original triangle density,
however, is false.  If $F$ is the triangle integrand, $T=\int F$,
$X=d(x_1)d(x_2)d(x_3)$, and

$$
J=\int F X^{1/8},\qquad K=\int F X,
$$

the tempting interpolation
$J\ge T^{7/8}K^{1/8}$ reverses Jensen's inequality: $x^{1/8}$ is concave, so
Jensen gives the opposite inequality.  The universally valid lower estimate
from $0\le X\le1$ is only $J\ge K$, which loses the required triangle factor.
Targeted two- and three-block searches found no violation of Atlas 178, and
the biased sharper recurrence stayed nonnegative numerically, but neither is
a proof.  This route therefore did not settle Atlas 178.

**Failed base-specific leaf correlation.**  Even the weaker-looking shortcut
from the already positive $K_5-e$ core is false.  On masses $(1/3,2/3)$ with

$$
 W=\begin{pmatrix}0&1\\1&3/5\end{pmatrix},\qquad p=\frac{32}{45},
$$

exact enumeration gives

$$
 t(H_{178},W)-p\,t(K_5-e,W)
 =-\frac{10672}{791015625}<0.
$$

The actual Atlas 178 target is still respected, with gap
$1120177744/64072265625>0$.  Thus the higher-rank weighted-ratio obstruction
cannot be bypassed by asserting positive degree correlation at the page
vertex of $K_5-e$.

**Later resolution.**  Atlas 178 is now positive by the half-degree
weighted-\(K_4\) theorem in
notes/atlas178_half_degree_weighted_k4.tex.  The successful proof retains
the two page vertices together: page Cauchy introduces the exact
\(d^{1/2}\) weight, rooted-link Goodman reduces the weighted \(K_4\) ratio
to rooted-triangle moments, and two exact supporting planes close those
moments.  It does not use either false interpolation or the failed
base-specific leaf correlation above.

## 15. Constant-graphon high-density witnesses for the pre-local open rows

**Principled test.** Compare the target attained by the complete multipartite
graphon at $p=1-1/x$ with the constant graphon of the same edge density.  The
constant graphon is a counterexample exactly when

$$
R_H(x)=x^{e(H)-v(H)}\chi_H(x)-(x-1)^{e(H)}>0.
$$

**Why this route has no current hit.** If $g$ is the girth and $N_g(H)$ is
the number of shortest cycles, Whitney's expansion gives the principled
asymptotic formula

$$
R_H(x)=(-1)^gN_g(H)x^{e(H)-g+1}+O(x^{e(H)-g}).
$$

Every one of the 43 rows in the historical pre-local baseline has odd girth:
42 contain a triangle and Atlas 104 has girth five.  Thus all have the wrong
asymptotic sign for a constant-graphon counterexample.  More strongly, exact
expansion at the start of the required interval gives
$R_H(y+\chi(H)-1)$ with every coefficient strictly negative for every one of
the 43 rows.  Hence the constant graphon stays above the target throughout
that full interval, not only asymptotically.

The same exact coefficient test was also run on the then-current 32-row open
snapshot.  All 32 shifted polynomials are coefficientwise strictly negative
(in 21 coefficient classes).  The 29-row pre-Atlas-152 snapshot forms a subset, and its
shifted polynomials have been rerun separately in 20 coefficient classes, so
later catalogue changes do not alter this no-hit conclusion.

The endpoint test has now been strengthened to every bounded normalized
complement. If $W=1-qU$, $\int U=1$, and $0\leq U\leq M$ for a fixed $M$,
the complete quadratic gap coefficient is

$$
P_2(H)(t(P_3,U)-1)+N_3(H).
$$

Cauchy's inequality makes the first term nonnegative, and every current open
row has $N_3(H)>0$. An explicit finite remainder bound proves strict
positivity for $0<q<N_3(H)/C_H(M)$. Thus none of the 29 snapshot rows admits a
high-density counterexample whose normalized complement has a fixed
$L^\infty$ bound. See
`notes/bounded_complement_high_density_stability.tex`.

The canonical singular direction has also been tested exactly. For
$W_s=1-\mathbf 1_{S\times S}$ with $\mu(S)=s$, independent-set enumeration
gives

$$
t(H,W_s)=\sum_{I\in\mathcal I(H)}s^{|I|}(1-s)^{v(H)-|I|}.
$$

On all 29 rows in that audit snapshot the full gap factors as
$s^3(1-s)^\ell R_H(s)$, and exact strictly positive Bernstein coefficients
prove $R_H>0$ throughout the complete admissible interval. Thus even this
$\|U_s\|_\infty=(1-p)^{-1}$ concentrating complement gives no hit. See
`notes/singular_clique_complement_high_density_test.tex`.

The same note proves more generally that a union of $r$ deleted diagonal
cliques is strictly positive whenever $rq<\alpha_H$ for an explicit
graph-dependent constant, uniformly over their masses. If
$q=\sum_i s_i^2$, the leading term
is $(P_2(H)-N_3(H))(\sum_i s_i^3-q^2)$ and the exact rank-at-least-three
remainder is $O_H(q^2)$. Power mean gives
$\sum_i s_i^3\geq q^{3/2}/\sqrt r$. All current rows have
$P_2(H)-N_3(H)>0$. This includes every $r=o(1/q)$ family.

The part-count restriction has now been removed as well.  With
$m=\max_i s_i$ and $D=\sum_i s_i^3-q^2$, exact power-sum defect propagation
and the cluster-rank identity give

$$
\Gamma_H(W)\geq(c_H-\Lambda_H\sqrt q)D,
\qquad c_H=P_2(H)-N_3(H)>0,
$$

for an explicit finite $\Lambda_H$.  Hence every finite or countable
complete-multipartite graphon is nonnegative sufficiently near $p=1$,
uniformly over the number and sizes of its parts. Equality is exactly the
balanced Turan family. All 29 snapshot rows pass this theorem.

For an arbitrary complement $V=1-W$, the entire graphic-rank-two term has
also been identified exactly as

$$
(P_2(H)-N_3(H))(t(P_3,V)-q^2)
+N_3(H)(t(P_3,V)-t(K_3,V)).
$$

Both defects are nonnegative. On every current open row both coefficients
are strict, and simultaneous equality characterizes exactly a union of equal
clique blocks, hence a balanced Turan complement. Thus the remaining
high-density issue is specifically quantitative stability of graphons which
are simultaneously almost regular and almost transitive; it is not an
unstructured search over singular complements.

That quantitative step is now available in two complementary regimes.  Put
$\Delta=\|d_V\|_\infty$, $X=t(P_3,V)-q^2$, and
$Y=t(P_3,V)-t(K_3,V)$.  Exact spanning-tree remainder estimates give

$$
\Gamma_H(1-V)\geq
(c_H-\Lambda_H\Delta)X+(N_3(H)-\Omega_H\Delta)Y.
$$

Every current open row has a positive rational maximum-degree radius, from
$7/8079$ to $8/161$.  This excludes every arbitrary measurable complement
with sufficiently small maximum degree; the independent spectral theorem
also excludes every sufficiently sparse complement of exact constant degree.
See `notes/maximum_degree_complement_high_density_stability.tex` and
`notes/stochastic_block_high_density_stability.tex`.

The opposite hub regime is also excluded whenever the defect support is
incident to a small measurable exceptional set.  If $W=1$ on $B^2$ and
$s=\mu(\Omega\setminus B)$, then the cut and exceptional-square kernels may
both be completely arbitrary.  Superadditivity of the union-bound remainder,
the preceding maximum-degree theorem on the exceptional square, and one
Young inequality prove $\Gamma_H(W)\geq0$ for $s\leq\tau_H$.  The 29 exact
radii range from $63/1963067$ to $7/9825$.  This includes any number of
interacting hubs contained in the same exceptional set, not only a two-block
or rank-one shape.  See
`notes/arbitrary_fibre_hub_high_density_stability.tex`.

The two regimes combine to remove the remaining support assumption.  For an
arbitrary complement, split at the high-degree set
$A=\{d_V>\delta_H\}$, where $\delta_H$ is half the certified maximum-degree
radius.  Markov makes $A$ small when $q=1-p$ is small; the residual on $B^2$
has low maximum degree, while the defect incident to $A$ has a quantitative
complete-core gap.  The latter absorbs the exact mixed target error
$J_Hq_Aq_B$.  This proves a uniform arbitrary-graphon interval
$q\leq\varepsilon_H$, with exact radii from $49/895333652544$ to $1/703570$
for the 29 snapshot rows.  See
`notes/arbitrary_graphon_high_density_stability.tex`.

Finally, the complete fixed-density segment from each balanced Turan graphon
to the constant graphon has a full-interval exact Bernstein certificate for
all 29 rows and every admissible part count.  Thus the constant comparison is
not rescued by a convex interpolation between its two endpoints.

**Safe lesson.** The method remains structurally promising for graphs of even
girth, where the leading sign reverses.  For these 43 rows, neither numerical
extension to larger $x$ nor another fixed bounded complement shape can
succeed.  For every one of the 29 rows still open, the endpoint is now closed
for all arbitrary graphons, including moving singular complements.  Further
negative work on these rows must stay a definite distance away from $p=1$.
This endpoint result is not a proof at intermediate densities.

## 16. Small-support needle perturbations of the Turan candidates

**Principled test.** A fixed-cell expansion can miss graphons that differ
from $T_k$ by order one on a vertex set of mass $\varepsilon$.  Split such a
microclass from one Turan part and allow an arbitrary connection profile
$\boldsymbol w\in[0,1]^k$ to the bulk parts.  Section 6 of
`notes/turan_local_and_high_density_negative_tests.tex` derives the complete
first-order polynomial $Q_{H,k}(\boldsymbol w)$, including density repair at
the threshold; it is not a preselected rewiring direction.

**Exact no-hit result.** For all rows in the historical 32-row open snapshot,
exact rational
Bernstein certificates on the whole profile cube prove a common KKT support
at $T_{\chi(H)-1}$.  Exact homogeneous barycentric certificates on the
symmetry-reduced ordered simplex prove $Q_{H,\chi(H)}\geq0$ as well.  The
required degree elevations are recorded row by row in the proof document.
The same calculation rediscovers the established Atlas 206 instability at
the exact profile $(1/2,1,1)$, so the test is not vacuous.

Away from the critical threshold, this local test has since been upgraded
from selected cell directions to a genuine arbitrary-kernel theorem.  For
every current open row and every balanced interior $T_k$ with
$k\geq\chi(H)$, the strict first variation and an explicit finite remainder
give a positive $L^\infty$ radius for all symmetric measurable perturbations.
Thus no direction in such a neighborhood was omitted.  See
`notes/turan_arbitrary_linfty_local_stability.tex`.

**Precise remaining obstruction.** At the critical threshold, these
certificates control only the coefficient linear in the exceptional mass.
When that coefficient is zero, two or more exceptional vertices contribute
at the next order and require new rooted two-point data.  The $L^\infty$
interior theorem does not include this threshold boundary and is not a
cut-distance local-minimality theorem.  Hence the no-hit result cannot make
any row positive.

**Safe lesson.** Future local work should begin with a second-order expansion
on the zero set of $Q_{H,k}$ (including exceptional--exceptional edges), or a
uniform-in-$k$ certificate.  Repeating fixed-amplitude cell Hessians or
sampling isolated microclass profiles does not repair this missing step.

## 17. Crossed edge self-amalgamation for Atlas 130

**Tempting claim.** Atlas 130, the graph consisting of two vertex-disjoint
triangles joined by one bridge, looks like a two-fold edge self-amalgam of the
paw along its pendant edge.  Apply the accepted edge self-amalgamation theorem
and conclude positivity from the paw bound.

**Precise obstruction.** The accepted theorem uses a distinguished *ordered*
edge and identifies corresponding endpoints.  If the pendant edge of the paw
is rooted from its leaf to its triangle vertex, its edge-rooted density after
removing the root edge is $g(x,y)=\tau(y)$, where $\tau$ is the rooted triangle
density.  Corresponding gluing gives

$$
\int W(x,y)\tau(y)^2\,dx\,dy,
$$

which Jensen controls and which produces a different already covered graph.
Atlas 130 reverses the root order in the second copy and has density

$$
\int W(x,y)\tau(x)\tau(y)\,dx\,dy.
$$

The normalized edge measure is symmetric, but symmetry alone does not give
$\int g(x,y)g(y,x)\ge(\int g)^2$: for a symmetric product measure, the
nonnegative function $g(x,y)=\mathbf1_{x<y}$ already makes the left side zero
and the mean positive.  Thus the Jensen step in the accepted ordered
self-amalgamation theorem genuinely disappears; changing the endpoint labels
does not repair it.

**What remains possible.** The special function $g(x,y)=\tau(y)$ has graphon
structure absent from the generic counterexample, so this does not disprove
Atlas 130.  A successful proof would need a new edge-correlation inequality

$$
\int W(x,y)\tau(x)\tau(y)\,dx\,dy
\ge p^3(2p-1)^2
$$

on $p\ge1/2$, or a different direct reduction.  Until such an inequality is
proved, Atlas 130 remains open and must not be classified by edge
self-amalgamation.

## 18. Extending the clique link proof to a two-edge tail (Atlas 142)

**Proposed extension.** Atlas 142 is $K_4$ with a pendant path of length two
at one clique vertex.  More generally, let $H$ be $K_r$ with such a tail,
write $d=T_W\mathbf1$, $A=T_Wd$, and condition on the tail-bearing clique
root.  The exact link identity is

$$
t(H,W)=\int d(x)^{r-1}A(x)t(K_{r-1},W_x)\,dx.
$$

The moment $\int d^{r-1}A$ is the density of a tree with $r+1$ edges, so
the accepted tree inequality gives the sharp bound $p^{r+1}$.  Thus the
common-leaf tangent argument would prove the exact target $p^2A_r(p)$ if one
could establish the weighted link estimate

$$
\int d^{r-3}A\,\tau
\ge \frac{2p-1}{p}\int d^{r-1}A,
\tag{18.1}
$$

where $\tau$ is the rooted triangle density.  For Atlas 142 this is
$\int dA\tau\ge((2p-1)/p)\int d^3A$ on $p\ge2/3$.

**Precise failure of the accepted proof.** The weighted rooted-Goodman lemma
proves the corresponding statement with weight $d^h$.  Its complement-kernel
step sets $U=1-W$, $u=1-d$, and uses

$$
\langle d^h,T_Uu\rangle\ge\int d^hu^2.
$$

After symmetrization, the difference is an integral of
$(u(y)-u(x))(d(x)^h-d(y)^h)$ against $U(x,y)$, whose sign is nonnegative
because $d=1-u$.  In (18.1) the required weight is $d^hA$ with $A=T_Wd$.
The value of $A$ is not a pointwise function of $u$ and has no proved
monotone ordering along complement edges.  Consequently that signed-pair
argument has no determined sign.  Simply inserting $A$ into the established
lemma is therefore invalid; the sharp tree moment controls the later Jensen
step but does not repair this missing link-average inequality.

**Recovery condition.** A proof of (18.1) for arbitrary graphons in the full
dense range would prove the whole $K_r$ two-edge-tail family.  That weighted
inequality remains unproved and must not be cited.

**Successful replacement for Atlas 142.** Atlas 142 is nevertheless now
positive by the different argument in `notes/k4_two_edge_tail.tex`.  Goodman
is first applied inside the rooted $K_4$ link, and only then is the pointwise
bound $\tau\geq(2A-p)_+$ inserted.  The resulting function of the feasible
pair $(d,A)$ has a sharp supporting plane containing the zero-integral term
$A-d^2$.  Its global validity is certified by an exact cubic discriminant and
a positive Bernstein expansion.  Thus the replacement retains the joint
rooted data and does not assert (18.1).

## 19. Higher-order Boolean needle profiles

**Principled extension tested.** The one-microclass needle calculation left
open profiles whose linear gap coefficient vanishes.  For every row in the
historical 32-row open snapshot, the threshold test was extended over every
Boolean connection profile
and both Boolean exceptional self-cell values through the first nonzero term
of the full exact gap polynomial.  When the raw perturbation left the density
interval, a diagonal cell in an unchanged Turan part was assigned the unique
polynomial weight that restored the threshold exactly.  At the first interior
point, the nonnegative ordered-simplex certificates were used to prove that
the full continuum zero set consists exactly of the permutations of
$(0,1,\ldots,1)$.  All these zero types were then mixed simultaneously with
arbitrary nonnegative masses, Boolean extreme self-cells, and Boolean extreme
mutual cells; the exact rooted two-vertex coefficient matrix was checked for
copositivity.

**Exact no-hit result.** The threshold audit contains 174 full gap
polynomials, 106 of them density-repaired.  Thirty-two vanish identically;
the remaining first nonzero orders are 105 quadratic, 21 cubic, 13 quartic,
and 3 sextic, always with positive coefficient.  At $T_{\chi(H)}$, there are
exactly 107 zero profiles across the 32 rows.  Their full mixtures produce
12608 exact quadratic matrices, all copositive; all 441 singular augmented
stationarity systems are exactly inconsistent.  The audit is reconstructed by
`codes/needle_higher_order_tests.py`.  No catalogue status changes.

At the threshold, the exact Bernstein-support audit isolates all six
continuum-flat one-profile rows: Atlas 130 and 152 on
$w_0+w_1\geq1$, and Atlas 153, 171, 174, and 188 on the exactly repaired
triangle $w_0+w_1\leq1$.  Both endpoint internal-cell values on every region
have nonnegative homogeneous simplex coefficients without degree elevation,
giving 12 exact continuum certificates and no hit.

The common-repair problem is now closed for arbitrary mixtures of **coarse**
profiles, meaning that each exceptional-to-bulk fibre is constant on each
bulk part. For each of the six flat triangles, direct two-root enumeration
produces a mixed quadratic kernel in two profiles and their mutual cell
value. Its 12 endpoint pullbacks to the product of two triangles have
coefficientwise nonnegative bihomogeneous forms without degree elevation.
Thus any measurable distribution of coarse profiles has nonnegative full
quadratic coefficient; on the four repaired faces a single repair is made
from the aggregate density displacement.

The coarse restriction has now also been removed for Atlas 130, 153, 171,
174, and 188. For these five rows all positive-degree overlap coefficients
are nonnegative, so the sharp Frechet lower overlaps are worst. Their two
switches cut the profile product into six exact four-simplices; the ten
endpoint kernels have 60 coefficientwise nonnegative homogeneous
certificates without degree elevation. This proves the complete
arbitrary-fibre quadratic cone for those five rows. See
`notes/turan_threshold_arbitrary_fibre_second_order.tex`.

**Exact obstruction for Atlas 152.** For arbitrary measurable fibres the
two-root kernel also depends on overlap moments $h_i=\int f_if_i'$, which are
not products of their means. The Atlas 152 kernel is not pointwise
nonnegative. With mutual cell zero, take flat
profiles $(1/6,1)$ and $(5/6,2/3)$ and indicator fibres having overlaps
$h_0=0$, $h_1=2/3$. The exact mixed entry is $-1/324$. This does not produce
a negative quadratic direction: the complete two-profile matrix is

$$
\begin{pmatrix}5/288&-1/324\\-1/324&2/9\end{pmatrix},
\qquad \det=101/26244>0.
$$

It genuinely rules out closing the Atlas 152 arbitrary-fibre threshold
problem by proving pointwise nonnegativity of the pair kernel. An integrated
positive-definiteness or moment inequality is required.

**Precise remaining obstruction.** The rooted profile polynomial need not be
multiaffine because several neighbours of an exceptional vertex may receive
the same bulk colour, producing powers such as $w_i^d$.  The ordered-simplex
support audit overcomes this only for the exact zero set at the first interior
point.  It does not give the uniform quantitative control needed when a
profile depends on $\varepsilon$ and approaches that zero set. The exact
stationary audit now shows that every zero of the interior mass-cone matrices
is merely a Turan-part refinement, so no other exact flat mass ray remains.
At the threshold, five arbitrary-fibre cones and every coarse mixture are
settled. For Atlas 152, every two-profile indicator mixture, every mixture
supported on the two profile axes, and every comonotone indicator mixture is
also settled; arbitrary fractional fibres with sufficiently small
mean-profile dispersion and arbitrary fibres supported on a coordinatewise
chain of mean profiles are settled as well; so are arbitrary fibres on one
constant-displacement profile line. The remaining overlap problem must put
positive mass on the strict profile interior
$u<1,v<1,u+v>1$, exceed the exact
$12(\mathbb E|u-\bar u|+\mathbb E|v-\bar v|)$ dispersion bound, and give
positive product measure to incomparable mean profiles; in the indicator
case, it requires at least three crossing profiles, and the density
displacement must genuinely vary. A future extension should
prove a uniform or integrated moment inequality on that residual cone, not
repeat selected Boolean or coarse numerical profiles.

## 20. Bonferroni recovery from a positive spanning subgraph

**Principled route tested.**  Let $F$ be an accepted positive spanning
subgraph of an open graph $H$, obtained by deleting $k$ edges.  Writing
$U=1-W$ and applying the elementary product union bound to the deleted
edges gives

$$
t(H,W)
\geq t(F,W)-k(1-p)
\geq \Phi_F(p)-k(1-p).
$$

Thus this route would prove $H$ if
$\Phi_F(p)-k(1-p)\geq\Phi_H(p)$ throughout the required density interval.
This formulation searches every deletion direction simultaneously; it is
not a selected one-edge perturbation.

**Exact no-hit result.**  Every accepted positive spanning-subgraph instance
of each row in the 31-row open snapshot immediately before the page-rooted
book-tail theorem was enumerated, including isolated vertices and disconnected
subgraphs.  There are 15,329 such labelled instances.  (Atlas 123 and 142
have since become positive by unrelated rooted arguments.)  At
the exact interior point $p=3/4$ for the $3$-chromatic rows and $p=5/6$ for the
$4$-chromatic rows, even the best candidate for every row has strictly negative

$$
\Phi_F(p)-k(1-p)-\Phi_H(p).
$$

One exact failure point in the required interval is sufficient to rule out
the proposed uniform proof for that $F$.  The enumeration, graph
isomorphisms, chromatic targets, and all rational gaps are reconstructed by
`codes/positive_edge_deletion_tests.py`.

**Precise obstruction.**  The estimate charges the full missing-edge mass
$1-p$ for each deletion independently and discards its correlation with the
$F$-homomorphism integrand.  Near a balanced multipartite equality graphon,
that lost correlation is exactly the information required to recover the
chromatic target.  Adding more accepted positive spanning subgraphs cannot
repair the present audit unless one of them changes the best candidate; a
successful extension must replace the uniform $k(1-p)$ loss by a rooted or
conditional estimate.

**Safe lesson.**  Do not retry edge deletion with a different hand-picked
positive subgraph and the same union bound.  A new attempt must retain
rooted information about the deleted nonedges.  The $T_Wd$-weighted lemma in
`notes/triangle_book_two_edge_tail.tex` is an example of such a recovery:
it controls the relevant correlation rather than paying a global
$1-p$ penalty.

## 21. Comparing page-rooted and spine-rooted tails on a diamond

**Tempting comparison.**  Atlas 120 and Atlas 123 are both a diamond with a
two-edge tail.  In Atlas 120 the tail root belongs to the two-vertex spine
orbit, while in Atlas 123 it belongs to the two-vertex page orbit.  It is
tempting to assert that the page-rooted density is always at least the
spine-rooted density and transfer the accepted Atlas 120 theorem directly.

**Exact counterexample to the comparison.**  On two equal classes, take the
step graphon matrix

$$
W=\begin{pmatrix}0&1\\1&1\end{pmatrix},
\qquad p=\frac34.
$$

Direct exact integration gives

$$
t(F_{123},W)=\frac14
<\frac{17}{64}=t(F_{120},W).
$$

Both values remain above their common target
$p^3(2p-1)^2=27/256$, so this refutes only the proposed orbit comparison,
not either graph.  The arithmetic is reconstructed in
`codes/verify_triangle_book_page_two_edge_tail.py`.

**Successful replacement.**  The proof in
`notes/triangle_book_page_two_edge_tail.tex` symmetrizes only within the page
orbit and keeps the page variables conditionally independent.  It reduces to
the convex function $a^{1/m}\max\{2a-p,0\}$ and proves Atlas 123 without any
comparison to Atlas 120.  Future work should use that fractional rooted
triangle lemma rather than attempt to order the two diamond orbits.

## 22. A single tangent plane for the rooted $C_4$ reduction of Atlas 126

**Promising exact reduction.**  Atlas 126 is a triangle and a $4$-cycle
amalgamated at one vertex.  Put $d=d(x)$, $A=(T_Wd)(x)$, and let $\tau(x)$
be the rooted triangle density.  If $c_4(x)$ is the rooted $4$-cycle density,
write $C(x,z)=\int W(x,y)W(y,z)\,dy$.  Splitting the square norm of $C(x,\cdot)$
over $W(x,z)$ and $1-W(x,z)$ and applying Cauchy--Schwarz gives the sharp
pointwise estimate

$$
c_4(x)\geq \frac{\tau(x)^2}{d(x)}
 +\frac{(A(x)-\tau(x))^2}{1-d(x)}.
$$

The zero-denominator cases have their evident limiting interpretations.  On
balanced multipartite graphons this is an equality, so the reduction remains
potentially useful.

**False supporting-plane lemma.**  Set

$$
F(d,a,t)=\frac{t^3}{d}+\frac{t(a-t)^2}{1-d},
\qquad
T_p=p^2(2p-1)(3p^2-3p+1).
$$

The tangent plane at the multipartite data
$(d,a,t)=(p,p^2,p(2p-1))$, in the integrable coordinates
$(d,a-d^2,t)$, has coefficients

$$
\begin{aligned}
\beta_p&=p(2p-1)(p^2+4p-1),\\
\gamma_p&=2p^2(2p-1),\\
\lambda_p&=p(7p^2-9p+3).
\end{aligned}
$$

It is tempting to assert

$$
F(d,a,t)\geq T_p+\beta_p(d-p)+\gamma_p(a-d^2)
 +\lambda_p\bigl(t-p(2p-1)\bigr)
$$

on the rooted feasible region.  This scalar statement is false.  At the
exact feasible tuple

$$
p=\frac35,\qquad d=\frac7{10},\qquad
a=\frac{31}{100},\qquad t=\frac15,
$$

one has $a\geq d+p-1$, $0\leq t\leq\min\{a,d^2\}$, and
$t\geq2a-p$, but

$$
F=\frac{2047}{105000}
<\frac{66}{3125}=L,
\qquad F-L=-\frac{853}{525000}.
$$

This does not refute Atlas 126: the listed scalar constraints need not
characterize globally realizable rooted triples.  It does show that the
otherwise successful one-plane strategy used for Atlas 100 and 142 cannot be
reused verbatim.  A successful continuation must exploit an additional
global relation among $d,A,\tau$, or use several supporting pieces whose
integrals are controlled with the correct coefficient signs.

## 23. Separate marginal contractions for the Atlas 152 fibre cone

**Exact remaining functional.** On the arbitrary-fibre threshold face for
Atlas 152, let $F_z,G_z$ be the connections of an exceptional point to the
two Turan parts, with means $u(z),v(z)$ and $u+v\geq1$. Define

$$
\begin{array}{ll}
P=\mathbb E[vF\otimes F],&Q=\mathbb E[uG\otimes G],\\
X=\mathbb E[uvF],&Y=\mathbb E[vF],\\
Z=\mathbb E[uvG],&T=\mathbb E[uG],\\
L=\mathbb E[uF\otimes G],&M=\mathbb E[vF\otimes G],
\end{array}
$$

and $C=\mathbb E[uv]$, $\delta=\mathbb E[u+v-1]$. Exact two-root
enumeration gives, at the worst internal exceptional value,

$$
8Q_{152}=\|P\|_2^2+\|Q\|_2^2+2\langle X,Y\rangle
+2\langle Z,T\rangle+2\langle L,M\rangle+C^2-4\delta^2.
$$

An arbitrary internal kernel adds a nonnegative term. This identity is
documented and reconstructed in
`notes/turan_threshold_arbitrary_fibre_second_order.tex` and
`codes/needle_higher_order_tests.py`.

**Insufficient tempting bound.** Put
$A=\mathbb E[u^2v]$ and $B=\mathbb E[uv^2]$. Marginal contraction and
$X\leq Y$, $Z\leq T$ give the valid bounds

$$
\|P\|_2^2+2\langle X,Y\rangle\geq3A^2,
\qquad
\|Q\|_2^2+2\langle Z,T\rangle\geq3B^2.
$$

If $J=\mathbb E[F\otimes G]$, then $0\leq L,M\leq J$ and
$L+M\geq J$. The pointwise inequality
$LM\geq(L+M-J)^2$ therefore also gives
$\langle L,M\rangle\geq(A+B-C)^2$. These correct estimates reduce the
desired statement to the stronger scalar inequality

$$
3A^2+3B^2+2(A+B-C)^2+C^2\geq4\delta^2.
$$

That stronger inequality is false. Give equal mass to the two profiles
$(1,\eta)$ and $(\eta,1)$. Its difference is

$$
\eta^2\left(-\frac32+3\eta+\frac72\eta^2\right),
$$

which is negative for all sufficiently small positive $\eta$.

**Safe lesson.** This does not itself refute the true Atlas 152 quadratic
functional; the exact examples tested at this stage remained positive. It
rules out deciding the functional by contracting its three Hilbert-space
sectors independently. Any valid classification must retain a joint relation
among $P,Q,L,M$ (or the common fibres $F,G$), rather than replacing each
sector by its scalar mean. The later exact fractional-fibre counterexample
does precisely this.

## 24. Total-mass contraction of the joint Atlas 152 kernel

**Sharper joint reformulation.** The seven positive terms of the exact
Atlas 152 functional in Attempt 23 do admit one common factorization. If
$h_F(z,z')=\int F_zF_{z'}$, $h_G(z,z')=\int G_zG_{z'}$, and

$$
\mathcal A(z,z')=v(z)h_F(z,z')+u(z)h_G(z,z')+u(z)v(z),
$$

then

$$
\|P\|_2^2+\|Q\|_2^2+2\langle X,Y\rangle+2\langle Z,T\rangle
+2\langle L,M\rangle+C^2
=\int\mathcal A(z,z')\mathcal A(z',z)\,dz\,dz'.
$$

Also $\int\mathcal A=A+B+C$, and the valid pointwise inequality
$uv(u+v+1)\geq2(u+v-1)$ on $u+v\geq1$ gives
$A+B+C\geq2\delta$. Thus it is tempting to finish with

$$
\int\mathcal A(z,z')\mathcal A(z',z)\,dz\,dz'
\geq\left(\int\mathcal A\right)^2.
$$

**Exact failure.** This last inequality is false despite the special form of
$\mathcal A$. Give the exceptional space two atoms of mass $1/2$, the first
bulk part two atoms of mass $1/2$, and the second bulk part one atom. Set

$$
F_1=(0,1/3),\quad F_2=(1,1/3),\qquad G_1=1,\quad G_2=1/3.
$$

The mean profiles are $(1/6,1)$ and $(2/3,1/3)$, hence lie on the admissible
upper triangle. Exact calculation gives

$$
A=\frac{19}{216},\quad B=\frac{13}{108},\quad C=\frac7{36},
\quad\delta=\frac1{12},
$$

and

$$
\int\mathcal A(z,z')\mathcal A(z',z)=\frac{1867}{11664},
\qquad
\int\mathcal A\mathcal A^T-(A+B+C)^2=-\frac{101}{46656}.
$$

This is only a failed proof inequality: the true eightfold Atlas 152
quadratic expression is still
$1867/11664-4\delta^2=1543/11664>0$ on this example.

**Safe lesson.** Keeping the joint kernel is necessary but not by itself
sufficient. Do not apply an unrestricted trace-versus-total-mass inequality
to its nonsymmetric kernel. Any successful estimate must compare directly
with $\delta$ and use further fibre consistency. The exact factorization and
example are reconstructed in `codes/needle_higher_order_tests.py` and
documented in
`notes/turan_threshold_arbitrary_fibre_second_order.tex`.

## 25. Geometric-mean contraction of the joint Atlas 152 kernel

**Natural strengthened attempt.** Since the total-mass contraction in
Attempt 24 fails for the nonsymmetric kernel, one can instead try to retain
both orientations pointwise. Cauchy--Schwarz would prove the required
quadratic inequality if

$$
\int \sqrt{\mathcal A(z,z')\mathcal A(z',z)}\,dz\,dz'
\geq 2\delta.
$$

**Exact failure.** Let the exceptional space, the first bulk part, and the
second bulk part each have two equal atoms. Take

$$
F_1=(0,0),\quad F_2=(0,1/2),\qquad
G_1=(1,1),\quad G_2=(1,1).
$$

The mean profiles are $(u_1,v_1)=(0,1)$ and
$(u_2,v_2)=(1/4,1)$, so both belong to the admissible upper triangle. The
exact joint kernel and density displacement are

$$
\bigl(\mathcal A(i,j)\bigr)_{i,j=1}^2
=\begin{pmatrix}0&0\\[2pt]1/2&5/8\end{pmatrix},
\qquad \delta=\frac18.
$$

Consequently

$$
\int\sqrt{\mathcal A\mathcal A^T}=\frac5{32}
<\frac14=2\delta,
$$

so the proposed bound fails by $3/32$. Again this is not a negative Atlas
152 direction: the actual joint contribution is $25/256$, and hence the
true eightfold quadratic remainder is

$$
\frac{25}{256}-4\left(\frac18\right)^2=\frac9{256}>0.
$$

**Safe lesson.** Neither total mass nor the symmetrized geometric mean of
the two orientations controls the density displacement. A proof must use
the full structured product $\mathcal A(z,z')\mathcal A(z',z)$ together
with fibre consistency, not a scalar contraction of that product. The
example is reconstructed exactly in `codes/needle_higher_order_tests.py`.

## 26. Independent minimization of all Atlas 152 fibre overlaps

**Proposed relaxation.** For a fibre $F_z:[0,1]\to[0,1]$ of mean $u(z)$,
one has

$$
\int F_z^2\geq u(z)^2,
\qquad
\int F_zF_{z'}\geq\max\{0,u(z)+u(z')-1\},
$$

and analogously for the $G$ fibres. It is tempting to substitute every one
of these individually sharp lower bounds into the exact Atlas 152 kernel and
prove copositivity of the resulting profile-only kernel.

**Exact obstruction.** Take the two upper-triangle profiles

$$
(u_1,v_1)=(49/50,2/5),\qquad (u_2,v_2)=(1/50,1).
$$

Use the square-mean bounds on the diagonal and the Fréchet lower bounds off
the diagonal. The resulting relaxed kernel matrix is

$$
M_{\mathrm{rel}}=
\begin{pmatrix}
11438061/312500000&-33/31250\\
-33/31250&201/50000000
\end{pmatrix},
$$

with

$$
\det M_{\mathrm{rel}}
=-\frac{15124949739}{15625000000000000}<0.
$$

Because both diagonal entries are positive and the off-diagonal entry is
negative, this matrix is not copositive. For example the positive vector
$(-M_{12},M_{11})$ gives quadratic value
$M_{11}\det M_{\mathrm{rel}}<0$.

**Why this is not a negative graphon direction.** The minimizing overlaps
cannot be attained simultaneously. Achieving the off-diagonal
$h_F(1,2)=0$ with means $49/50$ and $1/50$ is possible using complementary
indicator fibres, but their diagonal overlaps are then $u_i$, not $u_i^2$.
With these common $F$ fibres and constant $G$ fibres, the actual matrix is

$$
M_{\mathrm{comp}}=
\begin{pmatrix}
120119/3125000&-33/31250\\
-33/31250&1/4000
\end{pmatrix},
\qquad
\det M_{\mathrm{comp}}=\frac{530899}{62500000000}>0.
$$

Thus the exact compatible example is positive definite.

**Safe lesson.** Pairwise Fréchet bounds and diagonal Jensen bounds must not
be minimized independently. The common-fibre Gram consistency is precisely
strong enough to repair this relaxed negative matrix and is indispensable
in any proof of the Atlas 152 cone. Both matrices are reconstructed in
`codes/needle_higher_order_tests.py`.

## 27. Replacing the Atlas 152 density displacement by $C=\mathbb E[uv]$

**Proposed strengthening.** The exact Atlas 152 joint-kernel representation
has

$$
8Q_{152}=\int \mathcal A(z,z')\mathcal A(z',z)\,dz\,dz'-4\delta^2,
\qquad
\delta=\mathbb E[u+v-1].
$$

Since $uv\geq u+v-1$ on the upper profile triangle, it is natural to seek
the stronger contraction

$$
\int \mathcal A(z,z')\mathcal A(z',z)\,dz\,dz'
\stackrel{?}{\geq}4C^2,
\qquad C=\mathbb E[uv].
$$

**Exact compatible obstruction.** Give two exceptional profile classes
masses $3/5$ and $2/5$. On the first bulk space take constant fibres
$F_1\equiv9/10$ and $F_2\equiv1/4$. On a second bulk space with four equal
atoms take

$$
G_1=(2/5,0,0,0),\qquad G_2=(0,1,1,1).
$$

The two profiles are $(9/10,1/10)$ and $(1/4,3/4)$, so their density
displacements, and hence $\delta$, vanish. The exact joint-kernel matrix is

$$
\begin{pmatrix}
207/1000&9/80\\
57/160&27/64
\end{pmatrix}.
$$

Therefore

$$
C=\frac{129}{1000},\qquad
\int\mathcal A\mathcal A^T=\frac{25255881}{400000000},
$$

but

$$
\int\mathcal A\mathcal A^T-4C^2
=-\frac{1369719}{400000000}<0.
$$

This is a genuine failure of the proposed contraction using fully compatible
fibres. It is not a negative Atlas 152 direction: because $\delta=0$, the
true eightfold quadratic remainder is the strictly positive number
$25255881/400000000$.

**Safe lesson.** The larger moment $C$ erases boundary information essential
to the desired inequality. Any future contraction must retain the actual
density displacement $\delta$ and more of the oriented common-fibre geometry.
The exact example is reconstructed in `codes/needle_higher_order_tests.py`.

**Subsequent resolution.** The full cone is in fact negative. The compatible
five-step witness in
`notes/atlas_152_fractional_fibre_local_counterexample.tex` uses two
incomparable profiles with unequal displacement, complementary indicator
fibres in one bulk part, and constants $1/16,1$ in the other. Its exact
quadratic matrix has negative determinant and its full graphon gap is
strictly negative at $\varepsilon=1/3000$.

## 28. Replacing the critical-axis exceptional square by its three coarse means

**Proposed continuation.** For Atlas 137, 139, 145, and 148, the repaired
threshold needle is a positive multiple of $u^2v^2$. The only zero profiles
are therefore the axes, and their full arbitrary-fibre pair kernel is the
nonnegative factor $\kappa_H(1-x)(1-y)$. At the remaining endpoint $x=1$,
one might try to finish the higher-order hierarchy by replacing the kernels
inside the two exceptional profile types and between them by their three
scalar means $r_0,r_1,c$.

The resulting two-type constant-cell model is deceptively clean. If the two
endpoint types have proportions $\alpha,1-\alpha$, its repaired cubic is

$$
\frac{\alpha^3(r_0^3+2r_0^2)
 +(1-\alpha)^3(r_1^3+2r_1^2)}8
$$

for Atlas 137 and 139, while it is

$$
\frac{\alpha^3r_0^2+(1-\alpha)^3r_1^2}{2},\qquad
\frac{\alpha^3r_0^2+(1-\alpha)^3r_1^2}{4}
$$

for Atlas 145 and 148. On the cubic-zero face $r_0=r_1=0$, the respective
quartics factor as

$$
2(1-\alpha)^2(1-\alpha c)^2,\quad
2(1-\alpha)^2(1-\alpha c)^2,\quad
4(1-\alpha)^2(1-\alpha c)^2,\quad
3(1-\alpha)^2(1-\alpha c)^2.
$$

These formulas are valid for constant internal cells, but the reduction to
three means is false.

**Exact obstruction to the reduction.** Give each endpoint type mass
$\varepsilon/2$. Split the first type into two equal microclasses, take the
second-type square and the cross-type kernel to be zero, and put the exact
constant repair $7\varepsilon^2/2$ on the bulk $B^2$ cell. Compare two kernels
on the first type:

$$
R_{\mathrm{const}}\equiv\frac12,\qquad
R_{\mathrm{var}}=
\begin{pmatrix}1&1/2\\[2pt]1/2&0\end{pmatrix}
$$

on two equal atoms. Both have mean $1/2$, so all three proposed coarse means
are identical. Nevertheless their exact cubic coefficients are

$$
\begin{array}{c|cc}
H&R_{\mathrm{const}}&R_{\mathrm{var}}\\ \hline
137,139&5/512&27/2048\\
145&1/64&5/256\\
148&1/128&5/512.
\end{array}
$$

Thus the cubic genuinely sees rooted-degree and other internal homomorphism
moments. This does not provide a negative direction---all displayed values are
positive---and it does not affect the valid arbitrary-fibre axis-pair theorem.

**Safe lesson.** The endpoint square must remain an arbitrary graphon in any
higher-order proof. A viable continuation has to retain at least its rooted
$P_3$ density and the mixed exceptional-square correlations; a constant-cell
or mean-only calculation cannot establish a uniform local theorem. The exact
two-kernel comparison is reconstructed in
`codes/needle_higher_order_tests.py`.

**Subsequent resolution for every fixed endpoint direction.** The required
rooted data can be retained exactly. If the two endpoint types have
proportions $\alpha,\beta=1-\alpha$, arbitrary internal graphons $R_0,R_1$,
and an arbitrary cross kernel, direct coloured-moment enumeration gives the
raw and repaired cubic

$$
\frac{\alpha^3(t(K_3,R_0)+2t(P_3,R_0))
 +\beta^3(t(K_3,R_1)+2t(P_3,R_1))}{8}
$$

for Atlas 137 and 139. For Atlas 145 and 148 it is respectively

$$
\frac{\alpha^3t(P_3,R_0)+\beta^3t(P_3,R_1)}2,
\qquad
\frac{\alpha^3t(P_3,R_0)+\beta^3t(P_3,R_1)}4.
$$

These functionals are nonnegative and are independent of the cross kernel.
The resolution is uniform, not merely directional. If $D$ is the raw
second-order density excess, then

$$
\alpha^2r_0-D-\beta^2
=\beta^2(1-r_1)+2\alpha\beta(1-c)\geq0,
$$

so Jensen makes the cubic at least $D^2/4$ (or $D^2/2$ on Atlas 145).
Keeping only its positive three-exceptional-vertex colourings loses at most
$(1-2\varepsilon)^6$. Direct comparison with the order-four or order-six
target gives uniform support radii $1/10,1/10,1/20,1/32$. If the raw density
lies below the threshold, the exact nonnegative bulk repair makes the target
zero. Thus even endpoint kernels depending on the support scale are settled.
The failed mean contraction remains false; the proof succeeds precisely
because it retains $t(P_3,R_i)$ and $t(K_3,R_i)$.

The same rooted-moment method now covers the full axes, not only their
endpoint. If $d$ is the total exceptional-to-bulk fibre deficit and $E>0$ is
the raw density-excess coefficient, exact density algebra gives
$d\leq\varepsilon D_0/(1-2\varepsilon)$ and $E\leq D_0$. Removing vertices
whose rooted fibre deficit exceeds $1/16$, applying the two-edge-path
inequality to the surviving internal kernel, and retaining only positive
three-exceptional-vertex colourings gives the common arbitrary-fibre support
radius $1/100$. Thus no scale-dependent kernel or profile family supported
on the exact zero axes remains.

The final two-sided approach is also resolved without reviving the false
mean contraction. Project each profile to its nearer zero axis and let $m$
be the total deleted smaller-fibre mass. If
$m\geq2\varepsilon D_0$, the exact one-exceptional-vertex contribution
$\varepsilon\int u^2v^2$ dominates the target. If
$m<2\varepsilon D_0$, the projected rooted-moment contribution survives a
quantified good-set loss. The two cases give the uniform support radius
$1/10000$ for the complete measurable profile square.

## 29. Four-microclass Boolean self-amalgams on the critical axis endpoint

**Tested construction.** The remaining endpoint of the Atlas 137, 139, 145,
and 148 axis cone has exact Turan connections to the two bulk parts but an
arbitrary kernel on its exceptional square. To test whether this hidden
square produces a negative self-amalgam, it was split into four microclasses.
The audit exhausted:

- all $16$ assignments of the four classes to the two endpoint profile types;
- all $35$ mass vectors on the quarter grid;
- all $2^{10}=1024$ symmetric Boolean exceptional-square matrices, including
  the four diagonal cells;
- support masses $1/1000,1/100,1/20,1/10,1/5$; and
- all four Atlas rows.

For each configuration the bulk connections were the exact endpoint
connections, the full homomorphism density was evaluated over all $6^6$
macro-assignments, and only configurations with $p\geq1/2$ were retained.

**Outcome.** No negative value was found. The smallest floating values were
$-4.45\cdot10^{-16}$ at $p=1/2$, and direct inspection identifies them as
roundoff at exact zero configurations. This is only a finite numerical
no-hit result: the mass grid is finite, internal values are Boolean, and no
interval-arithmetic or symbolic certificate was extracted. It therefore
changes no graph status and is not used in any positive theorem.

**Safe lesson.** Repeating a denser Boolean grid would not have addressed the
actual obstruction exposed in Attempt 28. The exact rooted-moment cubic and
its positive-subintegral lower bound now prove the endpoint uniformly even
when its internal kernels vary with the support size, superseding this finite
scan. The formerly remaining two-sided corner has since been closed by the
exact one-vertex/rooted-moment dichotomy just described. A larger floating
step search would not have supplied either arbitrary-kernel quantifier or
the uniform $1/10000$ radius.

## 30. Absorbing every higher critical term by an absolute Taylor remainder

**Tempting claim.** For the nine remaining all-direction or density-neutral
threshold rows, combine the nonnegative arbitrary-kernel Hessian with the
general estimate

$$
 |R_{\geq3}(U)|\leq C_H\lVert U\rVert_\infty\lVert U\rVert_1
$$

and choose a sufficiently small universal $L^\infty$ radius. This is the
argument that works when the first variation is strict.

**Why this estimate cannot prove the claim.** On these critical faces the
available quadratic coercivity can scale like
$Q_H(U)\asymp\lVert U\rVert_1^2$. For a kernel of height $\eta$ supported on
a set of relative measure $\rho$, the absolute remainder bound scales like
$\eta^2\rho$, while the quadratic lower bound can scale like
$\eta^2\rho^2$. Their ratio is of order $1/\rho$, independently of how small
the proposed universal radius is. Thus shrinking the support defeats the
absorption step. This does not show that the actual signed remainder is
negative; it shows that the absolute-value estimate discards the decisive
sign and cannot establish a uniform theorem.

**Successful replacement.** The obstruction is bypassed without a support
lower bound. For Atlas 153, 171, 174, and 188, the chromatic target itself is
nonpositive on the exact strip $1/2\leq p\leq7/12$, so nonnegativity of
homomorphism density settles every graphon there. For Atlas 130, 137, 139,
145, and 148, retain only homomorphisms whose Turan two-colouring has exactly
two monochromatic edges. This is a positive subintegral, not a signed Taylor
truncation: its remaining cross edges contribute at least
$(1-\eta)^{e(H)-2}$ pointwise. Exact arbitrary-kernel enumeration gives a
lower bound $q_Hs^2$, where $s$ is the total diagonal-addition mean, and the
density constraint bounds the scalar target in terms of the same $s^2$.
This yields the complete radii documented in
`notes/turan_arbitrary_linfty_local_stability.tex`.

**Safe lesson.** When a critical Hessian controls a quadratic mass energy,
an $O(\eta\lVert U\rVert_1)$ absolute remainder is the wrong scale for
arbitrarily concentrated kernels. Preserve a nonnegative portion of the
original homomorphism integral, or exploit the sign of the target, instead
of taking absolute values term by term.

## 31. Elementary proofs of the $(3,5)$ odd-walk ratio for Atlas 102

Write $a_k=t(P_k,W)=\langle\mathbf1,T_W^k\mathbf1\rangle$, so $a_0=1$ and $a_1=p$. Appendix A of `notes/triangle_three_edge_tail.tex` reduces Atlas 102 to the single inequality

$$a_5\ \geq\ p^2a_3,$$

strictly weaker than the odd-walk theorem $a_5^3\geq a_3^5$ the body of that note cites. Everything else in the row is already machine-checked. Four routes to the reduced inequality were tried and all fail; they are recorded here because each looks convincing until it is evaluated on the complete bipartite graphon $W_s$ with parts of measure $s$ and $1-s$, where

$$p=2s(1-s),\quad a_2=s(1-s),\quad a_3=2s^2(1-s)^2,\quad a_4=s^2(1-s)^2,\quad a_5=2s^3(1-s)^3.$$

**Tempting claim (a): Hölder in the Blakley–Roy pattern.** Factor $Wdd'=(WAA')^{1/3}(Wd^3d'^3/(AA'))^{1/3}W^{1/3}$ and apply Hölder with exponents $(3,3,3)$, obtaining $a_3^3\leq a_5\cdot J\cdot p$ with $J=\iint W(d^3/A)(d'^3/A')$. **Why it fails.** One needs $J\leq p^3$; on $W_s$, $J=2s^2(1-s)^2$ and $p^3=8s^3(1-s)^3$, so $J\leq p^3$ forces $(1-2s)^2\leq0$.

**Tempting claim (b): Hölder with exponents $(5/3,5/2)$.** This reduces the goal to $\langle h,T_Wh\rangle\leq1$ for $h=d^{5/2}/A^{3/2}$. **Why it fails.** On every regular graphon $\langle h,T_Wh\rangle=1$ exactly, so the reduced statement is tight on a whole family and no crude estimate can close it. (An earlier note in this project recorded this as "fails on the constant graphon because $(\int h)^2=\int h^2=1/p>1$"; that is a mis-diagnosis — the quantity that matters, $\langle h,T_Wh\rangle$, equals $1$ there, so the route is tight rather than false.)

**Tempting claim (c): a positive-definite correction.** With $u=A-pd=T_W(d-p)$ one has $\langle u,T_Wu\rangle=a_5-2pa_4+p^2a_3$. If that were nonnegative, the goal would follow from $a_4\geq p\,a_3$, itself a consequence of $a_3\leq(a_2a_4)^{1/2}$, $a_4\geq a_2^2$ and $a_2\geq p^2$. **Why it fails.** $\langle u,T_Wu\rangle\geq0$ is not automatic: $T_W$ is not positive semidefinite and $u$ is not pointwise nonnegative. On $W_s$, $u=\mp s(1-s)(1-2s)$ on the two parts and $\langle u,T_Wu\rangle=-2s^3(1-s)^3(1-2s)^2<0$ for $s\neq1/2$.

**Tempting claim (d): tilting.** Writing $a_5=a_2^2p_A$ and $a_3=p^2p_d$ for the edge densities $p_A,p_d$ of $W$ under $A\dd\mu/a_2$ and $d\dd\mu/p$, the goal would follow from $a_2\geq p^2$ together with $p_A\geq p_d$. **Why it fails.** $p_A\geq p_d$ is $a_5p^2\geq a_3a_2^2$, which on $W_s$ reads $4s(1-s)\geq1$.

**The structural obstruction.** No argument that uses only the spectral measure $\sigma$ of $\mathbf 1$ can work. The inequality $\int\lambda^5\geq(\int\lambda)^2\int\lambda^3$ is false for general probability measures — take $\sigma=\frac1{17}\delta_{-1}+\frac{16}{17}\delta_{1/2}$, where $\int\lambda^3=\frac1{17}>0$ but $\int\lambda^5=-\frac1{34}<0$ — and it stays false after adding a small atom at $+1$, which is enough to satisfy the Perron–Frobenius constraint $\operatorname{supp}\sigma\subseteq[-\lambda_{\max},\lambda_{\max}]$ with $\sigma(\{\lambda_{\max}\})>0$. So nonnegativity of $W$ must enter other than through the spectrum. All it gives for free is $a_{2k+1}=\langle T_W^k\mathbf1,T_W T_W^k\mathbf1\rangle\geq0$.

**Numerical status, and what it does not license.** The stronger supermultiplicativity $a_{m+n}\geq a_ma_n$ (which would give the goal via $a_5\geq a_2a_3\geq p^2a_3$, and also contains Blakley–Roy via $a_3\geq a_1a_2\geq a_1^3$) held on roughly $5\times10^6$ pseudorandom graphons for every pair with $m+n\leq7$, with equality only at regular kernels. Under the standing rule this is a suggestion, not a proof, and Atlas 102 stays `believed`.

**Recovery condition.** Either a direct analytic proof of $a_5\geq p^2a_3$ that uses nonnegativity of $W$ beyond its spectrum, or a formalization of the finite Blekherman–Raymond $(3,5)$ theorem together with the sampling transfer of Lemma 2.2 of the note. The second needs a product probability space, a conditional Bernoulli construction, a second-moment estimate and convergence in probability, none of which the catalogue currently has.

## 32. Universal homomorphism-domination transfer for mixed chordal rows

**Proposed transfer.** Let $F$ be an open mixed-chordal graph and let $G$ be
an already-positive graph on the same number of vertices with
$P_F(q)=P_G(q)$.  The universal inequality

$$
 t(F,W)\geq t(G,W)
$$

would immediately transfer the accepted chromatic lower bound from $G$ to
$F$.  Isolated vertices were added when needed to compare the leaf-extension
rows with a product target, since they do not change graphon homomorphism
density.  This is a global, arbitrary-graphon test rather than a local Turan
expansion.

**Exact entropy-LP audit.** The Kopparty--Rossman chordal-source formula was
implemented sparsely in `codes/positive_hde_tests.py`.  The floating solver is
used only to locate a point: each coordinate is reconstructed over
$\mathbb Q$, and all monotonicity, submodularity, graphical-Markov,
normalization, and homomorphism-functional constraints are then checked
exactly.  Every comparison with an already-positive chordal graph having the
same chromatic polynomial gave an objective below $1$:

$$
\begin{array}{c|c|c}
F&\text{positive target Atlas IDs}&\text{exact feasible objectives}\\ \hline
130&111,112,117,120,123,115,113,114,119&0\text{ in every case}\\
137&135,136,144,150,138&3/4,5/6,6/7,8/9,3/4\\
139&135,136,144,150,138&3/4,5/6,6/7,8/9,3/4\\
157&156,165&1/2,1/2\\
160&156,165&1/2,1/2\\
178&177&2/3\\
181&179,180,183&1/2,1/2,0
\end{array}
$$

The simpler product comparisons also fail: Atlas 137 and 139 versus their
five-vertex pure-triangle core disjoint union $K_2$ give $1/2$, while Atlas
157 and 160 versus $K_4\sqcup K_3$ give $1/3$.

**What this rules out.** For the targets with maximum clique size three
(all targets used for Atlas 130, 137, and 139, including the product target),
the target is series-parallel, so the equality case of the
Kopparty--Rossman theorem makes the subunit value an obstruction to the
proposed universal domination itself.  For the targets containing $K_4$
(the Atlas 157, 160, 178, and 181 comparisons), the computation only shows
that this entropy lower-bound method cannot certify exponent at least one;
it does not prove that universal domination is false.

**Safe lesson.** Chromatic-polynomial matching is not enough to order these
mixed chordal densities by a density-independent homomorphism-domination
inequality.  A future transfer would have to exploit the restricted density
range $p\geq1-1/(\chi(F)-1)$, or prove a new weighted clique-page inequality;
rerunning the same universal LP at higher numerical precision cannot supply
that missing density-sensitive information.  No catalogue status follows
from this audit.

**Later resolution for two rows.** Atlas 137 and 139 are now positive by the
page-rooted triangle--leaf branch theorem in
`notes/triangle_book_page_paw_branch.tex`.  That proof does not revive any
domination comparison above: it symmetrizes the exceptional branch over the
book pages and uses a density-sensitive weighted rooted-triangle inequality.

## 33. Positive correlation of two rooted triangles across the Atlas 130 bridge

**Tempting strengthening.**  If $T=t(K_3,W)$ and $H_{130}$ is two triangles
joined by an edge between distinguished triangle vertices, then

$$
t(H_{130},W)\stackrel{?}{\ge}pT^2.
$$

Together with Goodman $T\ge p(2p-1)$, this would prove the exact Atlas 130
target $p^3(2p-1)^2$.

**Exact obstruction.**  Take two classes of masses $(5/8,3/8)$ and

$$
W=\begin{pmatrix}3/8&1\\1&0\end{pmatrix}.
$$

Then

$$
p=\frac{315}{512},\qquad
T=\frac{46575}{262144},\qquad
t(H_{130},W)=\frac{10518811875}{549755813888},
$$

and exact subtraction gives

$$
t(H_{130},W)-pT^2
=-\frac{10103686875}{35184372088832}<0.
$$

This does not refute Atlas 130: its gap above the catalogue target is

$$
t(H_{130},W)-p^3(2p-1)^2
=\frac{59499289125}{8796093022208}>0.
$$

Thus the two rooted-triangle densities are not automatically positively
correlated under the bridge-edge measure.  Any successful proof must retain a
correction depending on the triangle excess or finer rooted data.  The exact
enumeration is in `codes/verify_open_route_obstructions.py`.

## 34. Squaring the triangle density for the house graph (Atlas 43)

**Tempting strengthening.**  The house graph is a triangle and a $4$-cycle
sharing an edge.  A bound

$$
t(H_{43},W)\stackrel{?}{\ge}t(K_3,W)^2
$$

would supply a useful high-triangle regime toward its target.

**Exact obstruction.**  On two equal classes take

$$
W=\begin{pmatrix}1&2/5\\2/5&1\end{pmatrix}.
$$

This graphon is regular and has

$$
p=\frac7{10},\qquad
t(K_3,W)=\frac{37}{100},\qquad
t(H_{43},W)=\frac{6629}{50000}.
$$

Therefore

$$
t(H_{43},W)-t(K_3,W)^2=-\frac{27}{6250}<0.
$$

The actual Atlas 43 target is still respected, with exact gap
$1449/50000>0$.  Hence neither regularity nor the edge-rooted
$T_W^2$--$T_W^3$ representation licenses the square comparison.  The same
verification script reconstructs every fraction.

## 35. Mixed $K_4$--triangle clique gluing for Atlas 181

**Tempting strengthening.**  Atlas 181 consists of a central $K_4$ with a
triangle page on each of two opposite central edges.  The formally compatible
clique-tree product would be

$$
p^2t(H_{181},W)\stackrel{?}{\geq}t(K_4,W)t(K_3,W)^2.
$$

Together with the accepted clique bounds, this would give the exact target.
It would also follow by applying the one-page comparison
$p,t(K_4+\text{triangle page})\geq t(K_4)t(K_3)$ twice.

**Exact obstruction.**  Take class masses $(41/50,9/50)$ and

$$
W=\begin{pmatrix}2786/5043&1\\1&0\end{pmatrix}.
$$

Its edge density is exactly $p=2/3$, and direct rational enumeration gives

$$
p^2t(H_{181},W)-t(K_4,W)t(K_3,W)^2
=-
\frac{275063626170634894374246741629932943}
{13892215242665415394535250091552734375000}<0.
$$

The one-page comparison fails on the same graphon.  This is not a
counterexample to Atlas 181: at $p=2/3$ its catalogue target is zero, whereas
$t(H_{181},W)>0$.  Thus equal separator size does not repair the incompatible
$K_4$-edge and $K_3$-edge marginals.  A proof must be density-sensitive and
must retain the slack above the sharp clique bounds.

## 36. Edge-gluing the triangle to $C_4$ or $C_5$

**Tempting strengthenings.**  Atlas 43 is a triangle and a $4$-cycle glued
along an edge, while Atlas 127 is a triangle and a $5$-cycle glued along an
edge.  Their chromatic targets factor in the corresponding way.  This suggests

$$
pt(H_{43},W)\stackrel{?}{\geq}t(K_3,W)t(C_4,W),
\qquad
pt(H_{127},W)\stackrel{?}{\geq}t(K_3,W)t(C_5,W).
$$

For Atlas 127 the two rooted factors are the even path kernels $T_W^2$ and
$T_W^4$, but their Gram-kernel structure does not imply positive correlation
under the edge-biased measure.

**Exact obstructions.**  For Atlas 43, take two equal classes and

$$
W=\begin{pmatrix}1/6&1\\1&1/6\end{pmatrix}.
$$

Then $p=7/12$ and

$$
pt(H_{43},W)-t(K_3,W)t(C_4,W)
=-\frac{3125}{1492992}<0,
$$

while the actual target gap is $1225/746496>0$.  For Atlas 127, take masses
$(1/4,3/4)$ and

$$
W=\begin{pmatrix}0&1\\1&1/2\end{pmatrix}.
$$

Here $p=21/32$ and

$$
pt(H_{127},W)-t(K_3,W)t(C_5,W)
=-\frac{405}{4194304}<0,
$$

whereas the actual target gap is $58755/4194304>0$.  Hence neither row can be
proved by multiplying the separate sharp bounds across their common edge.

## 37. Cubing the triangle density for the triangular prism

**Tempting strengthening.**  Atlas 174 is the triangular prism.  Its density
is a triangle density on an edge-biased pair space, suggesting

$$
t(H_{174},W)\stackrel{?}{\geq}t(K_3,W)^3.
$$

**Exact obstruction.**  On two equal classes let

$$
W=\begin{pmatrix}1&3/4\\3/4&1\end{pmatrix}.
$$

Then $p=7/8$, $t(K_3,W)=43/64$, and

$$
t(H_{174},W)-t(K_3,W)^3=-\frac{205}{524288}<0.
$$

The catalogue target remains smaller, with exact gap $6265/524288>0$.
Moreover, even a hypothetical triangle-cube inequality would not finish the
scalar comparison on the full interval, since

$$
\bigl(p(2p-1)\bigr)^3-\Phi_{H_{174}}(p)
=p(p-1)^2(2p-1)(4p^2-9p+4),
$$

whose last factor is negative on part of $[1/2,1]$.  The pair-space
representation therefore needs a sharper density-sensitive input than the
ordinary Goodman triangle bound.

## 38. A heterogeneous link-tree product for Atlas 139

**Tempting strengthening.**  Conditioning Atlas 139 at a branch root leads
to a link probability measure $\nu$.  Write $z=\int W\,d\nu^2$ for its edge
density, let $d$ retain the ambient graphon degree, and put

$$
 a=\int d(x_0)\,d\nu(x_0),\qquad
 Q=\int d(x_0)W(x_0,x_1)W(x_1,x_2)W(x_2,x_3)\,d\nu^4.
$$

A heterogeneous Sidorenko-type product $Q\geq z^3a$ would separate the
ambient leaf weight from the three link edges and complete that conditional
route.

**Exact obstruction.**  Take two classes of masses $(1/4,3/4)$ and

$$
 W=\begin{pmatrix}1&1/4\\1/4&1\end{pmatrix},
$$

and condition at a point in the first class.  The ambient degree vector and
normalized link masses are

$$
 d=(7/16,13/16),\qquad \nu=(4/7,3/7).
$$

Direct rational enumeration gives

$$
 z=\frac{31}{49},\qquad a=\frac{67}{112},\qquad
 Q=\frac{11267}{76832},
$$

and hence

$$
 Q-z^3a=-\frac{127413}{26353376}<0.
$$

This only refutes the pointwise conditional product.  Atlas 139 is positive
by the different page-orbit symmetrization and fractional edge-rooted paw
estimate in `notes/triangle_book_page_paw_branch.tex`.

## 39. Edge-gluing the diamond to $C_4$ for Atlas 145

**Tempting strengthening.**  Atlas 145 is a diamond and a $4$-cycle glued
along their common spine edge, and its chromatic target is the corresponding
clique-sum product.  Thus one might try

$$
 pt(H_{145},W)\stackrel{?}{\geq}t(K_4-e,W)t(C_4,W).
$$

**Exact obstruction.**  On two equal classes take

$$
 W=\begin{pmatrix}1/4&1\\1&1/4\end{pmatrix}.
$$

Then

$$
 p=\frac58,\quad t(H_{145},W)=\frac{33617}{2097152},\quad
 t(K_4-e,W)=\frac{545}{8192},\quad
 t(C_4,W)=\frac{353}{2048},
$$

and exact subtraction gives

$$
 pt(H_{145},W)-t(K_4-e,W)t(C_4,W)
 =-\frac{6075}{4194304}<0.
$$

The catalogue target is still respected, with gap
$9297/2097152>0$.  Hence the new page-branch proof for Atlas 137 and 139
does not extend to Atlas 145 merely by multiplying the sharp diamond and
$C_4$ bounds across their spine edge.

**Successful replacement.**  Atlas 145 is now positive by
`notes/c4_triangle_page_concentration.tex`.  Regard it as a $4$-cycle with
two triangle pages on the same edge.  Moving one page to an adjacent edge
produces Atlas 148, and reflection symmetry of the cycle gives the exact
identity
$$
 t(H_{145},W)-t(H_{148},W)
 =\frac12\int (S(x_0,x_1)-S(x_0,x_3))^2\,d\Lambda\geq0.
$$
The full Atlas 148 theorem then supplies the common chromatic target.  This
square comparison retains the complete $C_4$ measure and does not validate
the false diamond--$C_4$ product above.

## 40. A two-triangle--$C_4$ product for Atlas 148

**Tempting strengthening.**  The target of Atlas 148 factors exactly as the
balanced-multipartite values of two triangles and a $4$-cycle.  Both the
constant graphon and every balanced multipartite graphon suggest

$$
 p^2t(H_{148},W)\stackrel{?}{\geq}t(K_3,W)^2t(C_4,W).
$$

**Exact obstruction.**  On two equal classes take

$$
 W=\begin{pmatrix}1/4&1\\1&1/4\end{pmatrix}.
$$

Then

$$
 p=\frac58,\quad t(H_{148},W)=\frac{31025}{2097152},\quad
 t(K_3,W)=\frac{49}{256},\quad t(C_4,W)=\frac{353}{2048},
$$

and

$$
 p^2t(H_{148},W)-t(K_3,W)^2t(C_4,W)
 =-\frac{8991}{16777216}<0.
$$

The true target gap is $6705/2097152>0$.  Hence equality on the constant and
balanced multipartite models does not license this product decomposition;
a proof for Atlas 148 must retain the covariance structure shared by its two
triangles and connecting path.

**Successful replacement.**  Atlas 148 is now positive by
`notes/atlas148_paw_bias_hilbert_projection.tex`.  On $[1/2,3/5]$ that proof
projects the exact density kernel onto constants and uses a sharp paw-bias
estimate derived from the clique density theorem.  On $[3/5,1]$ it projects
onto both $1$ and $W(x,\cdot)-d(x)$; the second coordinate retains precisely
the covariance discarded by the false product comparison.  The resulting
supporting-line inequalities have exact rational Bernstein certificates in
`codes/verify_atlas148_paw_bias_hilbert_projection.py`.  This replacement
does not validate the displayed product inequality, which remains false.

## 41. Direct same-target transfer from Atlas 145 or 148 to Atlas 147

**Tempting strengthening.**  Atlas 147 has the same chromatic polynomial
and target as the now-positive Atlas 145 and 148.  Since those two graphs are
the same-edge and adjacent-edge placements of two triangle pages on a
$4$-cycle, it is natural to ask whether either pointwise density comparison
$$
 t(H_{147},W)\geq t(H_{145},W),
 \qquad
 t(H_{147},W)\geq t(H_{148},W)
$$
could transfer their theorem.

**Exact obstructions.**  On two equal classes, first take
$$
 W=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$
Then $p=3/4$ and
$$
 t(H_{145},W)=\frac14,
 \qquad
 t(H_{147},W)=t(H_{148},W)=\frac{15}{64},
$$
so $t(H_{147},W)-t(H_{145},W)=-1/64$.  For
$$
 W=\begin{pmatrix}0&3/4\\3/4&1\end{pmatrix},
$$
one has $p=5/8$ and
$$
 t(H_{147},W)=\frac{94063}{1048576},
 \qquad
 t(H_{148},W)=\frac{23779}{262144},
$$
giving $t(H_{147},W)-t(H_{148},W)=-1053/1048576$.  The reverse ordering is
not valid either: the equal-class graphon
$$
 W=\begin{pmatrix}1/4&1\\1&1/4\end{pmatrix}
$$
gives $t(H_{147},W)-t(H_{148},W)=405/131072>0$.

All three Atlas 147 values remain strictly above their common catalogue
target; these are obstructions only to the transfer.  Exact enumeration is
included in `codes/verify_open_route_obstructions.py`.  A successful proof
for Atlas 147 must retain the covariance of its nested triangle page rather
than order the entire density against either completed page placement.

## 42. Paying for the house chord from the bare pentagon margin

**Tempting transfer.**  Atlas 43 is the house graph, obtained from a
$5$-cycle by adding the chord between the endpoints of its length-two side.
The accepted odd-cycle theorem gives
$$
 t(C_5,W)\geq p^5-p(1-p)^4,
$$
and the difference between this target and the house target is
$$
 \Phi_{C_5}(p)-\Phi_{H_{43}}(p)=p^2(1-p)(2p-1).
$$
It is therefore tempting to prove the house inequality by bounding the
density lost on insertion of the chord by this scalar margin.

**Exact obstruction.**  On two equal classes take
$$
 W=\begin{pmatrix}0&1\\1&1/2\end{pmatrix}.
$$
Then $p=5/8$ and exact enumeration gives
$$
 t(C_5,W)=\frac{101}{1024},
 \qquad
 t(H_{43},W)=\frac{125}{2048}.
$$
Thus the actual chord loss is $77/2048$, whereas the entire target margin is
only $75/2048$.  In particular,
$$
 \bigl(t(C_5,W)-t(H_{43},W)\bigr)
 -\bigl(\Phi_{C_5}(p)-\Phi_{H_{43}}(p)\bigr)
 =\frac1{1024}>0.
$$
The house itself still respects its target, with gap $15/1024>0$; this is
only an obstruction to transferring the bare odd-cycle lower bound.
Consequently a successful $C_5$-based proof must retain the pentagon excess
and couple it to the missing-chord term, rather than spend only the scalar
target margin.  The exact fractions are reconstructed in
`codes/verify_open_route_obstructions.py`.

## 43. Triangle--$C_4$ product transfer for the nested Atlas 147 page

**Tempting strengthening.**  Atlas 147 is a two-page triangle book with a
$4$-cycle glued along one edge of an exceptional page.  Its target factors
exactly as the product of two triangle targets and the edge-rooted
$4$-cycle target.  This suggests
$$
 p^2t(H_{147},W)\stackrel{?}{\geq}
 t(K_3,W)^2t(C_4,W).
$$
The scalar side of this route really is valid.  If
$T=t(K_3,W)$ and $C=t(C_4,W)$, then every graphon of density
$p\in[1/2,1]$ satisfies
$$
 T^2C\geq
 p^3(2p-1)^2(3p^2-3p+1).
$$
Here is a short proof, included to isolate the precise failure.  Put
$q=1-p$, $c=2p-1$, $f=3p^2-3p+1$, let
$S=T_W^2$ be the common-neighbour kernel, and set
$M=\int d^2=\int S$.  Projection of $S$ in $L^2(\Omega^2)$ onto
$1$ and $W-p$ gives, for $p<1$,
$$
 C=\int S^2\geq M^2+\frac{(T-pM)^2}{pq}.
$$
The formula remains valid when $W=p$ almost everywhere because then the
second numerator vanishes.  Also $M\geq p^2$, $T\leq M$, and Goodman's
inequality gives $T\geq pc$.  At fixed $T$ the displayed lower bound is
increasing for $M\geq T$, so its minimum occurs at
$M=\max\{p^2,T\}$.

If $T\leq p^2$, write $x=T/p\in[c,p]$.  After cancelling $p^3$, the
required inequality is
$$
 x^2\left(p^3+\frac{(x-p^2)^2}{q}\right)\geq c^2f.
$$
Equality holds at $x=c$, and the derivative of the left side is
$$
 \frac{2x}{q}\bigl(2x^2-3p^2x+p^3\bigr)\geq0.
$$
For $p\leq8/9$ the quadratic has nonpositive discriminant.  For
$p\geq8/9$ it is increasing on $x\geq c$, since
$4c-3p^2=(2-p)(3p-2)\geq0$, and its value at $c$ is
$q(5p^2-6p+2)>0$.  If $T\geq p^2$, the same projection gives
$C\geq T^2/p$, while
$$
 p^4-c^2f
 =q(11p^3-13p^2+6p-1)\geq0;
$$
after $p=(1+u)/2$ the last cubic is
$(11u^3+7u^2+5u+1)/8$.  This proves the joint scalar inequality; the
case $p=1$ is immediate.

**Exact obstruction to the gluing step.**  On classes of masses
$(1/4,3/4)$ take
$$
 W=\begin{pmatrix}0&1\\1&1/2\end{pmatrix}.
$$
Then
$$
 p=\frac{21}{32},\qquad
 t(H_{147},W)=\frac{33021}{1048576},\qquad
 t(K_3,W)=\frac{135}{512},\qquad
 t(C_4,W)=\frac{801}{4096},
$$
and exact arithmetic gives
$$
 p^2t(H_{147},W)-t(K_3,W)^2t(C_4,W)
 =-\frac{8991}{268435456}<0.
$$
This is not a counterexample to Atlas 147: its actual catalogue gap is
$90393/8388608>0$.  Thus the sharp triangle--$C_4$ projection reaches the
correct target, but multiplying the two rooted margins loses a small
negative covariance.  A successful proof must retain a correction for
that covariance; no refinement of the scalar projection alone can repair
the route.  All fractions above are reconstructed by
`codes/verify_open_route_obstructions.py`.

## 44. A tangent triangle--$C_4$ correction for the house graph

**Tempting strengthening.**  Write
$$
 T=t(K_3,W),\qquad C=t(C_4,W),\qquad
 q=1-p,\qquad c=2p-1.
$$
The two-coordinate projection used in the Atlas 147 audit suggests the
tangent comparison
$$
 t(H_{43},W)\stackrel{?}{\geq}
 cC+2cq\bigl(T-pc\bigr).
$$
It is exact at every balanced complete multipartite graphon.  Moreover, the
projection lower bound for $C$ has derivative $-2q$ at $T=pc$, so this is
precisely the correction that would turn that scalar projection into the
Atlas 43 target.  This makes the claim substantially sharper than the false
uncorrected product comparisons above.

**Exact obstruction.**  Take two equal classes and, for a scalar $x$, put
$$
 W_x=\begin{pmatrix}x&1\\1&x\end{pmatrix}.
$$
Direct enumeration gives
$$
 \begin{aligned}
 p&=\frac{1+x}{2},\\
 T&=\frac{x(x^2+3)}4,\\
 C&=\frac{x^4+6x^2+1}{8},\\
 t(H_{43},W_x)
 &=\frac{x(x+1)(x^4-x^3+5x^2+x+2)}{16}.
 \end{aligned}
$$
The proposed remainder factors as
$$
 t(H_{43},W_x)-cC-2cq(T-pc)
 =\frac{x^2(x-1)^2(x^2+4x-1)}{16}.
$$
It is therefore negative for $0<x<\sqrt5-2$.  The rational choice $x=1/5$
has
$$
 p=\frac35,\quad T=\frac{19}{125},\quad
 C=\frac{97}{625},\quad
 t(H_{43},W)=\frac{561}{15625},
$$
and the proposed remainder is exactly
$$
 -\frac4{15625}<0.
$$
This still is not a counterexample to Atlas 43.  Its true target is
$21/625$, and hence its actual gap is
$$
 t(H_{43},W)-p(2p-1)(3p^2-3p+1)
 =\frac{36}{15625}>0.
$$
Thus even the projection-tangent coefficient loses a small covariance on a
one-parameter family interpolating away from the balanced bipartite
graphon.  Any successful joint triangle--$C_4$ route must retain another
positive term; the scalar projection and this tangent correction alone do
not suffice.  The polynomial identities and rational witness are checked in
`codes/verify_open_route_obstructions.py`.

## 45. Completing the missing cone edge in Atlas 157

**Tempting reduction.**  Atlas 157 consists of a $K_4$, a triangle page on
one clique edge, and a leaf at one of the two clique vertices off that edge.
One endpoint of the page edge is adjacent to every vertex except the leaf.
Adding precisely that missing edge turns the leaf into a second triangle
page and produces the chordal graph with maximal cliques $K_4,K_3,K_3$.
Since adding an edge only decreases a homomorphism density, the completed
graph is a valid lower bound for Atlas 157.

**Exact loss at the target.**  Put
$$
 c=2p-1,\qquad r=3p-2.
$$
The completed chordal graph has chromatic target
$$
 p c^3r,
$$
whereas Atlas 157 has target
$$
 p^2c^2r.
$$
Their difference is
$$
 p^2c^2r-pc^3r= p(1-p)c^2r.
$$
It is strictly positive for every $2/3<p<1$.  This is not merely a loose
comparison on an artificial family: both chromatic targets are attained by
every balanced complete $k$-partite graphon, $k\geq4$.  Thus the completed
graph loses exactly the factor $c/p$ on the canonical equality graphons and
cannot prove Atlas 157 except at the endpoints.

A sharper still-viable reduction should not be confused with this failed
completion.  If $J_1$ is $K_4$ with one leaf and $J_2$ is $K_4$ with leaves
at two adjacent clique vertices, applying $ab\geq a+b-1$ to the two edges of
the triangle page gives
$$
 t(H_{157},W)\geq2t(J_2,W)-t(J_1,W).
$$
The density-sensitive inequality
$$
 2t(J_2,W)-t(J_1,W)\stackrel{?}{\geq}p^2c^2r
$$
has not been disproved and would settle the row, but it does not follow from
the separate accepted lower bounds for $J_1$ and $J_2$ because the first
term is subtracted.  Any future use must prove this signed strengthening (or
retain an equivalent covariance term), rather than invoke the completed
chordal target.  The graph identifications and target difference are checked
in `codes/verify_open_route_obstructions.py`.

## 46. Closing Atlas 126 from separate $C_4$-tail target bounds

**Valid signed reduction.**  Write $R_4(x)$ for the rooted $4$-cycle
density and $A(x)=(T_Wd)(x)$.  The pointwise rooted Goodman inequality
$\tau(x)\geq 2A(x)-p$ gives
$$
 t(H_{126},W)
 \geq 2J-pC,
 \qquad
 J=\int A(x)R_4(x)\,dx,
 \quad C=t(C_4,W).
$$
Here $J$ is the density of Atlas 103, a $4$-cycle with a two-edge tail.
The formal chromatic targets appear to cancel perfectly:
$$
 2\bigl(p^3(3p^2-3p+1)\bigr)
 -p\bigl(p(3p^2-3p+1)\bigr)
 =p^2(2p-1)(3p^2-3p+1).
$$

**Why separate target bounds cannot be substituted.**  The $C_4$ term has
a negative coefficient, so lower bounds for $J$ and $C$ do not imply a
lower bound for $2J-pC$.  In fact, the signed target comparison itself is
false.  On two classes of masses $(1/3,2/3)$ take
$$
 W=\begin{pmatrix}0&1\\1&1/2\end{pmatrix}.
$$
Exact enumeration gives
$$
 p=\frac23,
 \qquad J=\frac{68}{729},
 \qquad C=\frac{17}{81},
$$
and hence
$$
 2J-pC=\frac{34}{729}
 <\frac4{81}=\Phi_{H_{126}}(p),
 \qquad
 (2J-pC)-\Phi_{H_{126}}(p)=-\frac2{729}.
$$
This is not a counterexample to Atlas 126: on the same graphon
$$
 t(H_{126},W)=\frac{79}{1458},
 \qquad
 t(H_{126},W)-\Phi_{H_{126}}(p)=\frac7{1458}>0.
$$

**Recovery condition.**  The sharp rooted $C_4$ projection remains viable:
with $d=d(x)$, $a=A(x)$, and $t=\tau(x)$ it gives
$$
 R_4(x)\geq \frac{t^2}{d}+\frac{(a-t)^2}{1-d}.
$$
Numerical dual searches show that its scalar relaxation closes after adding
the exact Fisher--Reiher triangle-density slack on $1/2<p<2/3$, but the
density-dependent supporting plane still needs an exact uniform certificate.
The invalid separate-tail substitution above must not be used in its place.

## 47. A neighbourhood--complement split for the Atlas 157 page

**Valid rooted decomposition.**  Use clique vertices $0,1,2,3$, put the
triangle page on $12$, and attach the leaf at $0$.  Fix $x=x_0$, write
$d=d(x)$, $a=(T_Wd)(x)$, and let $t$ be the triangle density rooted at
$x$.  On the neighbourhood probability space

$$
 d\nu_x(y)=\frac{W(x,y)}d\,d\mu(y)
$$

the link graphon has edge density $z=t/d^2$.  Splitting the common-neighbour
integral of the page edge between $\nu_x$ and the complementary probability
measure gives a useful lower bound.  The inside part is a diamond density;
pure triangle gluing and Goodman give

$$
 t(K_4-e,W_x)\geq z(2z-1)_+^2.
$$

For the outside part, two applications of $rs\geq r+s-1$, followed by
Jensen for the positive part, give a lower bound in terms of

$$
 b=\frac{a-t}{d(1-d)}.
$$

Consequently the Atlas 157 density is at least the integral of

$$
 \mathcal F(d,a,t)
 =d^5z(2z-1)_+^2
  +d^4(1-d)\bigl(2b+z(2z-1)_+-2\bigr)_+.
$$

The formula is used only for $0<d<1$; zero and unit degree fibres can be
handled before division.  On every balanced complete multipartite graphon
the two displayed terms add to the exact Atlas 157 target
$p^2(2p-1)^2(3p-2)$, so this split repairs exactly the target loss of the
simple chordal completion in Attempt 45.

**Exact obstruction to a pointwise scalar finish.**  The rooted feasible
region also has

$$
 \max\{0,2a-p,a-d(1-d)\}\leq t\leq\min\{a,d^2\}.
$$

At the exact feasible tuple

$$
 p=d=\frac7{10},\qquad a=\frac{49}{100},\qquad t=\frac{29}{100},
$$

one has

$$
 z=\frac{29}{49},\qquad b=\frac{20}{21},\qquad
 2b+z(2z-1)-2=\frac{97}{7203}>0,
$$

but

$$
 \mathcal F(d,a,t)=\frac{757}{175000}
 <\frac{49}{6250}=p^2(2p-1)^2(3p-2),
 \qquad
 \mathcal F-\Phi_{157}=-\frac{123}{35000}.
$$

Thus the valid neighbourhood--complement decomposition does not close by a
pointwise comparison with the target, even after all of the elementary
rooted feasibility constraints above are retained.  This scalar tuple is
not asserted to be realized by a graphon and is not a counterexample to
Atlas 157.

**Recovery condition.**  A successful use of the split must retain another
global moment, such as the actual link-triangle/rooted-$K_4$ density, or a
quantitative compatibility constraint coupling the inside and outside link
pieces.  Substituting their separate sharp clique targets loses precisely
that information.

## 48. Truncating both rooted triangles in Atlas 130

**Tempting reduction.**  If $\tau(x)$ is the rooted triangle density and
$A=T_Wd$, rooted Goodman gives

$$
 \tau(x)\geq u(x):=(2A(x)-p)_+.
$$

Since Atlas 130 is two triangles joined by an edge, positivity of $W$ gives
the valid lower bound

$$
 t(H_{130},W)=\int W(x,y)\tau(x)\tau(y)\,d\mu^2
 \geq\int W(x,y)u(x)u(y)\,d\mu^2.
$$

It is tempting to compare the last energy directly with the exact target
$p^3(2p-1)^2$.

**Exact obstruction.**  Take two classes of masses $(1/5,4/5)$ and

$$
 W=\begin{pmatrix}0&4/5\\[2pt]4/5&2/5\end{pmatrix}.
$$

Then

$$
 p=\frac{64}{125},\qquad
 d=\left(\frac{16}{25},\frac{12}{25}\right),\qquad
 A=\left(\frac{192}{625},\frac{32}{125}\right),
$$

and hence $u=(64/625,0)$.  The only class on which $u$ is positive has
zero diagonal kernel value, so

$$
 \int W(x,y)u(x)u(y)\,d\mu^2=0
 <\frac{2359296}{30517578125}=p^3(2p-1)^2.
$$

This is not a counterexample to Atlas 130.  Exact enumeration gives

$$
 t(H_{130},W)=\frac{11010048}{1220703125},\qquad
 t(H_{130},W)-\Phi_{130}(p)
 =\frac{272891904}{30517578125}>0.
$$

The discarded triangle surplus lives on the second class and is exactly
what reconnects the two rooted factors across the bridge.  Any repair must
retain that surplus or a finer rooted statistic; no inequality involving
only the truncated function $(2T_Wd-p)_+$ can prove the row.

## 49. Lifting the Atlas 48 tensor witness through the cone Atlas 203

**Tempting counterexample construction.**  Atlas 203 is exactly the cone
$K_1\vee H_{48}$: its unique universal vertex is vertex $1$, and deleting it
leaves a graph isomorphic to the negative Atlas 48.  Start with the established
Atlas 48 tensor witness $U=T_4\otimes T_4$, give its sixteen cells total mass
$1-s$, and add one independent cell of mass $s$ which is complete to the old
space.  The resulting graphon $W_s$ has
$$
 p(s)=\frac9{16}(1-s)^2+2s(1-s)
     =\frac{(1-s)(23s+9)}{16}.
$$
If $S$ is the labelled set of source vertices sent to the new cell, then $S$
must be independent.  The remaining induced graph maps to
$T_4\otimes T_4$, so exact enumeration of the $64$ subsets gives
$$
 t(H_{203},W_s)
 =\sum_{\substack{S\subseteq V(H_{203})\\S\text{ independent}}}
 s^{|S|}(1-s)^{6-|S|}
 \frac{P_{H_{203}-S}(4)^2}{16^{6-|S|}}
 =\frac{9(1-s)^4(881s^2+206s+1)}{65536}.
$$

**Exact obstruction to this counterexample route.**  On the admissible
interval $p(s)\ge2/3$, the gap from the Atlas 203 target is strictly positive.
Indeed,
$$
 t(H_{203},W_s)
 -p(s)(2p(s)-1)(3p(s)-2)(10p(s)^2-14p(s)+5)
 =\frac{Q(s)}{262144},
$$
where
\begin{align*}
Q(s)={}&96545145s^{10}-293833050s^9+341199181s^8
-177536632s^7+22854662s^6\\
&+19016396s^5-10236146s^4+2214328s^3
-230911s^2+5326s+1701.
\end{align*}
Admissibility forces $s\in[1/7,1/2]$.  All eleven exact degree-$10$
Bernstein coefficients of $Q$ on this larger rational interval are strictly
positive.  For example, at $s=1/4$,
$$
 p=\frac{177}{256},\qquad
 t(H_{203},W_s)-\Phi_{203}(p)
 =\frac{740757729}{274877906944}>0.
$$
Thus negativity of a base graph does not lift through this natural symmetric
cone construction.  The displayed polynomial identity, its admissible
interval, and the stated positive Bernstein coefficients are the exact
no-hit certificate; this entry does not depend on a separate proof note.

**Recovery condition.**  Numerically allowing the old--new value and new-cell
diagonal to vary, then allowing four stabilizer-orbit cross values, and finally
splitting the exceptional cell into two fibres all returned to the symmetric
positive minimum.  Those numerical searches are not an impossibility proof.
A future negative construction must use a genuinely different base graphon or
a nonsymmetric fibre mechanism not captured by these lifts; merely adjoining
a universal part to the known Atlas 48 witness should not be retried.

## 50. Closing the Atlas 43 common-neighbour reduction by a whiskered $C_4$

**Tempting reduction.**  Write
$$
 S(x,y)=\int W(x,z)W(y,z)\,d\mu(z),
 \qquad
 B(x,y)=\int W(x,a)W(a,b)W(b,y)\,d\mu^2(a,b).
$$
Then the house graph and the $4$-cycle have densities
$$
 t(H_{43},W)=\int W(x,y)S(x,y)B(x,y)\,d\mu^2,
 \qquad
 C=t(C_4,W)=\int W(x,y)B(x,y)\,d\mu^2.
$$
The common-neighbour union bound $S(x,y)\ge d(x)+d(y)-1$ gives
$$
 t(H_{43},W)\ge 2J-C,
 \qquad
 J=\int W(x,y)B(x,y)d(x)\,d\mu^2.
$$
Thus the attractive candidate $t(H_{43},W)\ge(2p-1)C$ would follow from
the apparently natural whiskering inequality $J\ge pC$.

**Exact obstruction.**  Take class masses $(4/9,5/9)$ and
$$
 W=\begin{pmatrix}0&1\\[2pt]1&1/4\end{pmatrix}.
$$
Direct rational calculation gives
$$
 p=\frac{185}{324},\qquad
 d=\left(\frac59,\frac7{12}\right),\qquad
 C=\frac{237425}{1679616},\qquad
 J=\frac{180575}{2239488},
$$
and hence
$$
 J-pC=-\frac{10975}{136048896}<0.
$$
The full common-neighbour slack repairs this small deficit on the same
graphon:
$$
 t(H_{43},W)-(2p-1)C
 =\frac{6381925}{2176782336}>0.
$$
Thus this example does not disprove the surviving house--$C_4$ comparison,
let alone the Atlas 43 target.  It shows that the rooted union bound cannot be
closed by a separate leaf-to-core comparison.  A successful proof must retain
the positive term
$\int WB\,[S-d(x)-d(y)+1]$, equivalently the complement common-neighbour
kernel, together with the negative rooted-degree covariance.

## 51. Comparing the Atlas 157 signed leaf reduction with $K_4$

**Tempting strengthening.**  Let $K=t(K_4,W)$, let $J_1$ be the density of
$K_4$ with one pendant leaf, and let $J_2$ be the density of $K_4$ with one
leaf at each of two distinct clique vertices.  The valid triangle-page
reduction from Attempt 45 is
$$
 t(H_{157},W)\ge 2J_2-J_1.
$$
Since the sharp clique target is
$A_4(p)=p(2p-1)(3p-2)$, the strengthening
$$
 2J_2-J_1\stackrel{?}{\ge}p(2p-1)K
$$
would combine with $K\ge A_4(p)$ to give exactly the Atlas 157 target
$p^2(2p-1)^2(3p-2)$.

**Exact obstruction.**  Take class masses $(5/7,2/7)$ and
$$
 W=\begin{pmatrix}13/25&1\\[2pt]1&0\end{pmatrix}.
$$
Then
$$
 p=\frac{33}{49},\qquad
 d=\left(\frac{23}{35},\frac57\right),
$$
and exact enumeration gives
$$
 K=\frac{59751809}{937890625},\qquad
 J_1=\frac{1401754107}{32826171875},\qquad
 J_2=\frac{4695997423}{164130859375}.
$$
Consequently
$$
 (2J_2-J_1)-p(2p-1)K
 =-\frac{20573182552}{56296884765625}<0.
$$
This is not an obstruction to the valid signed route itself.  Indeed its
gap above the Atlas 157 target is
$$
 (2J_2-J_1)-p^2(2p-1)^2(3p-2)
 =\frac{36981403729352}{2758547353515625}>0.
$$
The surplus $K-A_4(p)$ is therefore essential: it compensates for a small
failure of the normalized signed leaf ratio.  Any completion of Attempt 45
must couple that clique surplus to the degree covariance rather than first
lower-bound $K$ and then compare the signed expression to a fixed multiple
of its actual value.

## 52. The first high-density rooted-moment plane for Atlas 130

**Valid reduction.**  Let $d=T_W\mathbf1$, $a=T_Wd$, let $\tau$ be the
rooted triangle density, and put $T=\int\tau$.  Writing $U=1-W$ and applying
$2\tau(x)\tau(y)\leq\tau(x)^2+\tau(y)^2$ gives the arbitrary-graphon bound
$$
 t(H_{130},W)
 =T^2-\int U(x,y)\tau(x)\tau(y)\,d\mu^2
 \geq T^2-\int(1-d)\tau^2\,d\mu.
$$
This part of the route remains valid.

**Tempting supporting plane.**  For $c=2p-1$, set
$$
 \gamma_0=-2p^2c-3(1-p)^3,
 \qquad \beta_0=\gamma_0-5p^2c^2.
$$
The proposed pointwise inequality on $2/3\leq p\leq1$ was
$$
 (1-d)t^2\stackrel{?}{\leq}
 p^2c^2(1-p)+2pc(t-pc)
 +\beta_0(d-p)+\gamma_0(a-d^2).
 \tag{52.1}
$$
After integration, the last two terms vanish and (52.1) would leave the
perfect square $(T-pc)^2$ above the Atlas 130 target.

**Exact obstruction.**  Put $u=1/100$ and take the feasible scalar tuple
$$
 p=1-u-\frac{u^2}{8}=\frac{79199}{80000},\qquad
 d=1-u=\frac{99}{100},
$$
$$
 a=d+p-1=\frac{78399}{80000},\qquad
 t=d^2+p-1=\frac{77607}{80000}.
$$
It lies on the face $a=d+p-1$, $t=d^2+p-1$.  All eight rooted constraints
$$
 a,\ d-a,\ a-d-p+1,\ t,\ t-2a+p,\
 t-a+d(1-d),\ a-t,\ d^2-t\geq0
$$
hold exactly.  Nevertheless, the right side of (52.1) minus its left side is
$$
 -\frac{202093779043001}{204800000000000000000000}<0.
$$
More generally, along
$p=1-u-u^2/8$, $d=1-u$, $a=d+p-1$, $t=d^2+p-1$, the residual factors as
$$
 -\frac{u^4}{2048}
 \left(u^6+30u^5+304u^4+976u^3-1472u^2-5376u+256\right),
$$
so the failure occurs arbitrarily close to $p=1$ and was invisible to
ordinary random sampling.

**Successful repair and remaining limitation.**  Replacing the coefficient
by
$$
 \gamma=\frac{-9p^3-p^2+5p-1}{2},
 \qquad \beta=\gamma-5p^2c^2
$$
produces a valid exact supporting plane on $2/3\leq p\leq1$.  The resulting
336-box rational certificate proves the arbitrary-graphon bound on that high
interval.  This repairs the high subinterval only; Atlas 130 remains open on
$1/2<p<2/3$ and therefore remains open in the catalogue.

## 53. A $P_4$-biased Cauchy determinant for Atlas 130

**Tempting closure.**  In the Atlas 130 notation, put
$$
 B=\int d(x)a(x)\,d\mu(x)=t(P_4,W),
 \qquad
 F=\int a(x)\tau(x)\,d\mu(x).
$$
The accepted $T_Wd$-weighted rooted-triangle theorem and Sidorenko's path
bound give
$$
 F\geq(2p-1)B,
 \qquad B\geq p^3.
$$
Consequently the determinant inequality
$$
 t(H_{130},W)B\stackrel{?}{\geq}F^2
 \tag{53.1}
$$
would imply the exact target.  Equivalently, under the $P_4$-biased edge
measure proportional to $W(x,y)d(x)d(y)d\mu^2$, (53.1) asserts nonnegative
endpoint covariance of $\tau/d$.

**Exact obstruction.**  Take four equal cells and let the step matrix be the
adjacency matrix of $K_4$ with the edge $23$ deleted, with zero diagonal:
$$
 W_{ij}=\mathbf1\{i\ne j,\ \{i,j\}\ne\{2,3\}\}.
$$
Then exact enumeration gives
$$
 p=\frac58,qquad
 B=\frac{33}{128},qquad
 F=\frac5{64},qquad
 t(H_{130},W)=\frac3{128}.
$$
Thus
$$
 t(H_{130},W)B-F^2=-\frac1{16384}<0.
$$
The edge-weighted bilinear form is not positive semidefinite even on the
special pair of rooted functions $d$ and $\tau$; ordinary Cauchy--Schwarz
cannot justify (53.1).

**What survives.**  This graphon does not disprove the more precise
density-sensitive comparison
$$
 t(H_{130},W)\stackrel{?}{\geq}(2p-1)F.
 \tag{53.2}
$$
Indeed,
$$
 t(H_{130},W)-(2p-1)F=\frac1{256}>0,
$$
and its gap above the Atlas target is $67/8192$.  Thus a proof of (53.2)
cannot pass through a bare determinant: it must couple the small negative
$P_4$-biased covariance to the positive surplus $F-(2p-1)B$.  The exact
obstruction is checked by `codes/verify_open_route_obstructions.py`.

## 54. Extending the Atlas 130 complement-moment relaxation below \(2/3\)

**Tempting closure.**  The valid complement reduction from Attempt 52 gives
\[
 t(H_{130},W)\geq T^2-R,\qquad
 R=\int(1-d)\tau^2.
\]
One might hope that a different supporting plane, or a nonlinear moment
argument, could prove \(T^2-R\geq p^3(2p-1)^2\) on \(1/2<p<2/3\) using only
the rooted feasible region and the identities
\[
 \int d=p,\qquad \int a=\int d^2,\qquad \int\tau=T.
\]

**Exact scalar obstruction.**  At \(p=3/5\), put weights \(17/35,18/35\)
on the two tuples
\[
 (d,a,t)=
 \left(\frac{21}{34},\frac{5673}{11560},\frac{441}{1156}\right),
 \qquad
 \left(\frac7{12},\frac{1451}{6120},0\right).
\]
At each atom all eight slacks
\[
 a,\ d-a,\ a-d-p+1,\ t,\ t-2a+p,\
 t-a+d(1-d),\ a-t,\ d^2-t
\]
are nonnegative.  The global identities also hold exactly:
\[
 \mathbb E d=\frac35,\qquad
 \mathbb E a=\mathbb E d^2=\frac{49}{136}.
\]
However,
\[
 T=\frac{63}{340},\qquad
 R=\frac{361179}{13363360},
\]
and hence
\[
 T^2-R-p^3(2p-1)^2
 =-\frac{11138769}{8352100000}<0.
\]

This is a distribution of scalar rooted data, not a graphon, so it does not
refute Atlas 130.  It does prove that no argument whose only conclusion is
the complement lower bound \(T^2-R\), and whose only further input is the
recorded scalar feasible region and its mean identities, can close the low
interval.  Additional kernel compatibility is indispensable.  The displayed
exact factorization is the complete obstruction needed for this entry.

## 55. Closing the Atlas 127 cycle compression by a separate pentagon whisker ratio

**Tempting closure.**  Let $C=t(C_5,W)$, and let $J$ be the density of
$C_5$ with one pendant leaf.  A valid exact five-cycle attachment compression
gives

\[
 t(H_{127},W)\geq
 \max\left\{0,J-\frac25C,2J-C\right\}.
\]

The common-neighbour union bound also makes the separate comparison
$J\geq pC$ especially attractive.  It would turn the last affine piece
into $2J-C\geq(2p-1)C$, after which the accepted pentagon bound would
give the Atlas 127 target.

**Exact obstruction.**  Take three equal cells and

\[
 W=\begin{pmatrix}
 3/5&19/40&19/40\\
 19/40&1&0\\
 19/40&0&1
 \end{pmatrix}.
\]

Then

\[
 p=\frac12,\qquad
 C=\frac{3446549}{97200000},\qquad
 J=\frac{1652897729}{93312000000},
\]

and therefore

\[
 J-pC=-\frac{1445791}{93312000000}<0.
\]

This is not a counterexample to Atlas 127, whose target is zero at
$p=1/2$.  Indeed, the middle piece retained by the cycle compression is

\[
 J-\frac25C=\frac{329422913}{93312000000}>0.
\]

Thus the nonlinear five-cycle slack repairs the negative leaf covariance,
but it cannot be discarded and replaced by a separate whisker-to-core
ratio.  The displayed rational matrix and exact evaluations make this
obstruction self-contained.  Atlas 127 itself is positive by the separate
smoothed-Goodman flag-SOS proof; only this attempted closure fails.

## 56. Adding the full triangle surplus to the Atlas 43 target

**Tempting strengthening.**  Put
\[
 T=t(K_3,W),\qquad q=1-p,\qquad c=2p-1,
 \qquad f=3p^2-3p+1.
\]
Extensive finite-step tests suggested the density-sensitive inequality
\[
 t(H_{43},W)\stackrel{?}{\geq}
 pcf+p^2c\bigl(T-pc\bigr).
 \tag{56.1}
\]
It is exact on every balanced complete multipartite graphon and on the
entire equal-cell family
\[
 W_x=\begin{pmatrix}x&1\\1&x\end{pmatrix}.
\]
Moreover, Goodman's decomposition
\[
 T-pc=2\left(\int d_{1-W}^2-q^2\right)
 +\left(t(P_3,1-W)-t(K_3,1-W)\right)
\]
makes the correction look like a natural payment for degree variance and
the complement transitivity defect.

**Exact obstruction.**  Take two equal cells and
\[
 W=\begin{pmatrix}
 4/5&999/1000\\[2pt]
 999/1000&4/5
 \end{pmatrix}.
\]
Then
\[
 p=\frac{1799}{2000},\qquad
 T=\frac{3634003}{5000000},\qquad
 t(H_{43},W)=\frac{5290255967286199}{10^{16}},
\]
and the residual in (56.1) is
\[
 -\frac{13890073603}{40000000000000000}<0.
\]
This failure is not numerical.  More generally, on equal cells put
\[
 1-W=\begin{pmatrix}a&b\\b&a\end{pmatrix}.
\]
The residual in (56.1) factors as
\[
 \frac{b(2-a-b)}{16}
 \left(
 3a^4-a^3b-a^3+5a^2b^2+3a^2b
 +ab^3-3ab^2+b^3
 \right).
\]
At (b=0), the parenthesized factor is (a^3(3a-1)).  Hence every
(0<a<1/3) has a sufficiently small positive cross-complement value (b)
that breaks the proposed strengthening.  The equality seen on (W_x)
is therefore unstable in a transverse regular direction.

**What survives.**  The same rational graphon is not a counterexample to
Atlas 43.  Its exact gap above the actual target is
\[
 \frac{52361333032449}{10000000000000000}>0.
\]
Thus Atlas 43 remains open.  A repair cannot charge the complete surplus
(T-pc) at coefficient (p^2c); it must retain an additional statistic
that distinguishes a purely block-diagonal complement from a complement
with a small cross-block value.  The exact fractions and the finite family
factorization are checked by
`codes/verify_open_route_obstructions.py`.

## 57. Transferring Atlas 157 from same-target positive Atlas 165

**Tempting comparison.**  Atlas 157 and Atlas 165 have the same chromatic
polynomial and target:
\[
 \chi(x)=x(x-1)^2(x-2)^2(x-3),
 \qquad
 \Phi(p)=p^2(2p-1)^2(3p-2).
\]
Atlas 165 is a (K_4) and a triangle sharing one vertex, and is already
positive.  Atlas 157 is a (K_4) with a triangle page on one clique edge
and a leaf at a clique vertex off that edge.  Smooth random step graphons on
(p\geq2/3) strongly suggested
\[
 t(H_{157},W)\stackrel{?}{\geq}t(H_{165},W).
 \tag{57.1}
\]
For an equal two-step regular graphon
(W=\left(\begin{smallmatrix}a&b\\b&a\end{smallmatrix}\right)), the
difference even factors as
\[
 \frac{a^2b(a-b)^4(a+b)^2}{32}\geq0.
\]

**Exact admissible obstruction.**  Take three cells with masses
\[
 \left(\frac45,\frac18,\frac3{40}\right)
\]
and step matrix
\[
 W=\begin{pmatrix}
 3/5&1&3/5\\
 1&0&1\\
 3/5&1&9/20
 \end{pmatrix}.
\]
Its edge density is
\[
 p=\frac{21673}{32000}>\frac23,
\]
but exact enumeration gives
\[
 t(H_{157},W)-t(H_{165},W)
 =-\frac{4479354904290777}{20971520000000000000}<0.
\]
Thus (57.1) fails inside the complete required interval, not merely below
the chromatic threshold.  A density-independent homomorphism-domination LP
also gives only the lower exponent (1/2), but the explicit graphon is the
decisive obstruction to the density-sensitive comparison.

**What survives.**  Neither row is violated on this graphon.  Their exact
gaps above the common target are, respectively,
\[
 \frac{252880303423946572953}{8388608000000000000000}>0,
 \qquad
 \frac{254672045385662883753}{8388608000000000000000}>0.
\]
The obstruction is strongly nonregular; the regular two-step factorization
above remains valid but cannot be promoted to arbitrary graphons.  A proof
of Atlas 157 must retain the surplus in its signed (K_4)-leaf reduction,
as already indicated by Attempt 51, rather than replace the whole density by
a same-target positive graph.  The exact fractions are checked by
`codes/verify_open_route_obstructions.py`.

## 58. Closing Atlas 168 from separate triangle, page-book, and clique bounds

**Valid reduction.**  For a spine edge (xy), put

\[
 L_{xy}(z)=W(x,z)W(y,z),\quad
 s=\int L_{xy},\quad
 A=\langle L_{xy},d\rangle,\quad
 C=\langle L_{xy},T_WL_{xy}\rangle.
\]
The exact Atlas 168 density is
\[
 \int W(x,y)s(x,y)\lVert T_WL_{xy}\rVert_2^2\,d\mu^2.
\]
Projection onto $1$ and $L_{xy}-s$ proves, for arbitrary graphons,
\[
 t(H_{168},W)\geq
 \frac{R^2}{T}+\frac{(K-R)^2}{p-T},
 \tag{58.1}
\]
where $T=t(K_3,W)$, $R=t(H_{41},W)$ is the page-rooted
two-triangle one-leaf density, and $K=t(K_4,W)$.  On every balanced Turan
graphon, the right side is exactly
\[
 p(2p-1)^2(5p^2-6p+2).
\]
In particular, the second projection supplies precisely the
$2p(2p-1)^2(1-p)^3$ missed by constant projection.  The full arbitrary-
graphon projection is valid; for this failed closure, equation (58.1) is the
starting inequality rather than the disputed step.

**Why the obvious scalar closure fails.**  The accepted separate bounds
\[
 T\geq p(2p-1),\qquad
 R\geq p^2(2p-1)^2,
\]
together with the Moon--Moser consequence
\[
 K\geq\max\left\{0,\frac{T(3T-p)}{2p}\right\},
\]
do not imply that (58.1) reaches the target.  At $p=3/5$, the abstract
scalar tuple
\[
 T=\frac3{25},\qquad R=K=\frac9{625}
\]
satisfies all those inequalities and $0\leq R,K\leq T\leq p$, but the
right side of (58.1) is $27/15625$, short of the target $3/625$ by
$48/15625$.  This tuple is not asserted to be graphon-realizable; it is an
exact obstruction to closing the valid projection by marginal substitutions.

**Required repair.**  Atlas 168 remains open.  A completion now has a precise
form: prove the joint three-density inequality
\[
 \frac{R^2}{T}+\frac{(K-R)^2}{p-T}
 \geq p(2p-1)^2(5p^2-6p+2).
\]
It must use compatibility among $(T,R,K)$, not only their separate sharp
lower bounds.  The displayed feasible scalar tuple is already sufficient to
show that marginal substitution cannot supply that compatibility.

## 59. Target-matched edge gluing of the $K_4$ and $C_4$ in Atlas 169

**Tempting comparison.**  Atlas 169 is a $K_4$ and a $4$-cycle glued along
one edge.  Write

\[
 K=t(K_4,W),\qquad C=t(C_4,W),\qquad p=t(K_2,W).
\]
Since the sharp targets of the two factors are

\[
 p(2p-1)(3p-2),\qquad
 p(3p^2-3p+1),
\]
respectively, the edge-gluing comparison

\[
 p\,t(H_{169},W)\stackrel{?}{\geq}KC
 \tag{59.1}
\]
would give exactly the Atlas 169 target on the complete admissible interval
$p\geq2/3$.  This is the $K_4$--$C_4$ counterpart of the already-false
triangle--cycle comparisons, but the higher density threshold leaves open
the possibility that (59.1) is density-sensitive.

**Exact admissible obstruction.**  Take two cells of masses $(7/12,5/12)$
and

\[
 W=\begin{pmatrix}9/20&1\\[2pt]1&1/6\end{pmatrix}.
\]
Then

\[
 p=\frac{5773}{8640}>\frac23,
\]
and exact enumeration gives

\[
 \begin{aligned}
 t(H_{169},W)&=
 \frac{540284314760268971563}{30091839012864000000000},\\
 K&=\frac{56571423674089}{967458816000000},\\
 C&=\frac{57060423841}{268738560000}.
 \end{aligned}
\]
Consequently

\[
 p\,t(H_{169},W)-KC
 =-\frac{726187086808446778151}
 {1733289927140966400000000}<0.
\]
This is not a counterexample to Atlas 169: its actual gap is

\[
 t(H_{169},W)-
 p(2p-1)(3p-2)(3p^2-3p+1)
 =\frac{530062858443546525313}
 {30091839012864000000000}>0.
\]
Thus the restricted density interval does not repair direct separator
correlation.  Any successful clique--cycle proof must retain a correction
coupling the $K_4$ and $C_4$ surpluses.  The exact arithmetic is checked by
`codes/verify_open_route_obstructions.py`.

## 60. Pointwise averaged rooted-triangle closure for Atlas 130

**Tempting strengthening.**  In the Atlas 130 notation, let $d=T_W\mathbf1$,
let $\tau$ be the rooted triangle density, put $a=T_Wd$, and set
$c=2p-1$.  The surviving density-sensitive comparison from Attempt 53 is

\[
 t(H_{130},W)\stackrel{?}{\geq}cF,
 \qquad F=\int a\tau.
 \tag{60.1}
\]
Together with the accepted chain $cF\geq p^3c^2$, this would prove Atlas
130 on its remaining low interval.  A natural pointwise route to (60.1) is

\[
 (T_W\tau)(x)\stackrel{?}{\geq}c(T_Wd)(x)
 \quad\text{for almost every }x,
 \tag{60.2}
\]
because multiplication by $\tau(x)$ and integration gives (60.1).

**Exact pointwise obstruction.**  Let $W$ be the disjoint union of cliques
of masses $1/6$ and $5/6$:

\[
 W=\begin{pmatrix}1&0\\0&1\end{pmatrix}.
\]
Its edge density is $p=13/18$, so $c=4/9$.  On the smaller clique,

\[
 d=\frac16,\qquad \tau=\frac1{36},\qquad
 T_Wd=\frac1{36},\qquad T_W\tau=\frac1{216},
\]
and hence

\[
 T_W\tau-cT_Wd=-\frac5{648}<0.
\]
Thus no proof of (60.1) may first discard the root weight and assert the
averaged rooted-triangle inequality pointwise.

**What survives.**  This example does not disprove the global comparison.
Indeed,

\[
 t(H_{130},W)=\frac{7813}{23328},\qquad
 F=\frac{521}{1296},\qquad
 t(H_{130},W)-cF=\frac5{32}>0.
\]
The large clique compensates for the pointwise deficit on the small clique.
A completion must therefore retain the global $\tau$-weighting or an exact
covariance correction.  These fractions are checked by
`codes/verify_open_route_obstructions.py`.

## 61. Replacing the rooted pentagon leaf by its mean degree in Atlas 127

**Tempting high-density closure.**  Let

\[
 C=t(C_5,W),\qquad
 J=t(C_5\text{ with one leaf},W),\qquad
 \varphi_5(p)=p^5-p(1-p)^4.
\]
The exact cycle compression for Atlas 127 gives, among its three branches,

\[
 t(H_{127},W)\geq 2J-C.
\]
On $p\geq3/5$, the mean-degree comparison

\[
 J\stackrel{?}{\geq}pC
 \tag{61.1}
\]
would reduce the high branch to $(2p-1)C$ and hence to the sharp target
$(2p-1)\varphi_5(p)$ by the accepted $C_5$ inequality.

**Exact admissible obstruction.**  Take four cells of masses

\[
 \left(\frac{297}{1000},\frac{83}{1000},
       \frac{221}{1000},\frac{399}{1000}\right)
\]
and kernel matrix

\[
 \frac1{1000}
 \begin{pmatrix}
 792&768&950&244\\
 768&621&681&447\\
 950&681&221&554\\
 244&447&554&939
 \end{pmatrix}.
\]
Its edge density is

\[
 p=\frac{607118993}{1000000000}>\frac35,
\]
but exact enumeration gives

\[
 J-pC=
 -\frac{236762108092938158335672003174957}
 {1000000000000000000000000000000000000000}<0.
\]
Thus even the restricted high-density interval does not make the rooted
leaf degree positively correlated with the pentagon weight.

**What survives.**  This graphon does not obstruct the compressed Atlas 127
bound.  In fact

\[
 2J-C-(2p-1)\varphi_5(p)=
 \frac{409561015543817615626277526465718516421807}
 {125000000000000000000000000000000000000000000}>0.
\]
The credible repair is therefore a direct inequality for $2J-C$ whose
negative covariance term is absorbed by the sharp $C_5$ surplus, rather
than the separate bound (61.1).  The exact arithmetic is checked by
`codes/verify_open_route_obstructions.py`.

## 62. Closing Atlas 43 after the square-row codegree slack bound

**Valid retained-slack bound.**  Put

\[
 S(x,y)=\int W(x,z)W(z,y)\,d\mu(z),\qquad
 B(x,y)=T_W^3(x,y),
\]
and

\[
 r(x)=\int W(x,z)^2\,d\mu(z).
\]
Writing $H=t(H_{43},W)$, direct expansion gives

\[
 H=C_4+C_5-P_4+E,
 \qquad
 E=\int(1-W)(1-S)B.
\]
Cauchy--Schwarz and arithmetic--geometric mean give
$S(x,y)\leq\sqrt{r(x)r(y)}\leq(r(x)+r(y))/2$.  Symmetry therefore yields
the valid arbitrary-graphon lower bound

\[
 E\geq\int(1-W)B(1-r(x)),
 \qquad
 H\geq C_5-X_r,
 \tag{62.1}
\]
where

\[
 X_r=\int(1-W(x,y))B(x,y)r(x)\,d\mu(x)d\mu(y).
\]
It remains tempting to compare the last expression directly with the house
target.

**Exact obstruction to the final comparison.**  Partition the probability
space into seven equal cells and let $W$ be the $0/1$ adjacency graphon with
edge set

\[
 \begin{split}
 \{&03,04,05,06,13,14,15,16,23,24,25,26,36,45\}.
 \end{split}
\]
This is the equal-cell graphon of NetworkX Atlas graph 1171.  It is
$4$-regular, so $p=r(x)=4/7$ almost everywhere.  Exact enumeration gives

\[
 C_5=\frac{780}{16807},\qquad
 X_r=\frac{432}{16807},\qquad
 C_5-X_r=\frac{348}{16807}.
\]
The sharp house target at $p=4/7$ is

\[
 p(2p-1)(3p^2-3p+1)=\frac{52}{2401}
 =\frac{364}{16807}.
\]
Hence the right side of (62.1) misses the target by exactly $16/16807$.
This is not a counterexample to Atlas 43: its actual house density is
$396/16807$, exceeding the target by $32/16807$.

Thus (62.1) remains a valid retained-slack estimate, but no proof can close
it using only the proposed scalar comparison.  A repair must recover some
of the Cauchy--Schwarz/codegree slack or couple it to the $C_5$ surplus.
All fractions and the Atlas edge set are checked by
`codes/verify_open_route_obstructions.py`.

## 63. Transferring Atlas 157 by moving its leaf to obtain Atlas 160

**Tempting same-target relocation.**  Both graphs consist of a $K_4$ and a
triangle page on one clique edge.  Atlas 157 puts its remaining leaf at a
$K_4$ vertex off the page edge, whereas positive Atlas 160 puts that leaf at
the page apex.  They have the same chromatic polynomial and target,

\[
 \chi(x)=x(x-1)^2(x-2)^2(x-3),\qquad
 \Phi(p)=p^2(2p-1)^2(3p-2).
\]
The relocation comparison

\[
 t(H_{157},W)\stackrel{?}{\geq}t(H_{160},W)
 \tag{63.1}
\]
would therefore transfer the accepted Atlas 160 theorem directly.  After
conditioning on the common page edge, (63.1) says that the degree average
at an endpoint of the additional edge between the two $K_4$ page vertices
dominates the degree average at an independent page apex.  Smooth random
tests often exhibit that ordering, but it is not universal.

**Exact interior obstruction.**  Take two cells of masses $(1/4,3/4)$ and

\[
 W=\begin{pmatrix}0&1\\[2pt]1&8/15\end{pmatrix}.
\]
Then

\[
 p=\frac{27}{40}>\frac23,qquad
 t(H_{157},W)=\frac{2203421}{105468750},qquad
 t(H_{160},W)=\frac{4457617}{210937500},
\]
and hence

\[
 t(H_{157},W)-t(H_{160},W)=-\frac{677}{2812500}<0.
\]
Thus the complete admissible interval does not repair this direct leaf
relocation.

**What survives.**  Neither row is violated.  Their exact gaps above the
common target are, respectively,

\[
 \frac{8422420541}{432000000000}>0,
 \qquad
 \frac{8526407741}{432000000000}>0.
\]
The failed relocation is small relative to the Atlas 160 surplus on this
example.  A viable transfer would have to couple the relocation covariance
to the quantitative surplus in the weighted-$K_4$ supporting-plane proof,
not discard that surplus by first applying the completed Atlas 160 theorem.
The exact arithmetic is checked by
`codes/verify_open_route_obstructions.py`.

## 64. A coefficientwise six-point proof of the Atlas 157 signed transfer

**Stronger surviving transfer candidate.**  Let $J$ be the $K_4$ with a
two-edge tail used in the accepted Atlas 160 proof, and put
$K=t(K_4,W)$.  That proof establishes

\[
 2t(J,W)-pK\geq p^2(2p-1)^2(3p-2)
 \qquad (p\geq2/3).
\]
Consequently Atlas 157 would be resolved by the additive comparison

\[
 t(H_{157},W)+pK-2t(J,W)\stackrel{?}{\geq}0.
 \tag{64.1}
\]
Unlike the direct Atlas 157--160 ordering in Attempt 63, (64.1) retains the
full signed lower certificate proved for Atlas 160.  It is exact on the
balanced multipartite equality graphons and remains a credible unproved
inequality.

**Why the elementary six-point finish fails.**  All three terms in (64.1)
can be represented on six sampled vertices: the middle graph is
$K_4\sqcup K_2$.  After averaging over all labelings of a fixed induced
six-vertex graph $G$, its coefficient is proportional to

\[
 \operatorname{inj}(H_{157},G)
 +\operatorname{inj}(K_4\sqcup K_2,G)
 -2\operatorname{inj}(J,G).
 \tag{64.2}
\]
For $G$ equal to Atlas 206, namely $K_6$ with the two independent edges
$14$ and $25$ deleted, the three exact injective counts are

\[
 80,\qquad192,\qquad144,
\]
so (64.2) is $80+192-2\cdot144=-16$.  Thus (64.1) cannot be proved merely
by expanding into induced six-vertex patterns and asserting every
coefficient is nonnegative.

**What survives.**  The negative induced coefficient is not a graphon
counterexample to (64.1).  On the equal six-cell adjacency graphon of Atlas
206 itself,

\[
 p=\frac{13}{18},\qquad
 t(H_{157})=\frac{20}{729},\qquad
 t(J)=\frac{13}{324},\qquad
 K=\frac2{27},
\]
and the left side of (64.1) is $1/1458>0$.  Repeated-cell assignments and
other induced patterns compensate for the single negative coefficient.
A proof of (64.1), if true, therefore needs a genuine consistency or
rooted-square argument (or a direct analytic inequality), not a
coefficientwise six-point expansion.  The Atlas identification, injective
counts, and equal-cell fractions are checked by
`codes/verify_open_route_obstructions.py`.

## 65. A bare Cauchy/log-convexity proof of the Atlas 157 signed transfer

**Tempting strengthening.**  Continue to write (J) for the (K_4) with a
two-edge tail and (K=t(K_4,W)).  The signed comparison (64.1) would follow
at once from

\[
 J^2\stackrel{?}{\leq}pK\,t(H_{157},W),
 \tag{65.1}
\]

because arithmetic--geometric mean would give

\[
 t(H_{157},W)+pK\geq2\sqrt{pK\,t(H_{157},W)}\geq2J.
\]

This is the natural log-convexity statement suggested by gluing the rooted
(K_4) statistics, and it retains the full surplus in the desired signed
transfer.

**Exact obstruction.**  Take two classes of masses ((3/4,1/4)) and

\[
 W=\begin{pmatrix}16/25&1\\[2pt]1&1/10\end{pmatrix}.
\]

Then

\[
 p=\frac{593}{800}>\frac23,
 \quad K=\frac{583528603369}{4000000000000},
 \quad J=\frac{12826282551257779}{160000000000000000},
\]

and

\[
 t(H_{157},W)
 =\frac{464515683664781303}{8000000000000000000}.
\]

Exact arithmetic gives

\[
 pK\,t(H_{157},W)-J^2
 =-\frac{377601852247947768223340019729}
 {2560000000000000000000000000000000}<0.
\]

**What survives.**  Neither the signed transfer nor the catalogue inequality
fails on this graphon.  Their respective exact gaps are

\[
 t(H_{157},W)+pK-2J
 =\frac{46968583033545903}{8000000000000000000}>0
\]

and

\[
 t(H_{157},W)-\Phi_{157}(p)
 =\frac{942185908651703337}{32000000000000000000}>0.
\]

Thus (64.1), if true, needs an additive consistency argument; a single
multiplicative Cauchy comparison is strictly stronger and false.  All
fractions are checked by `codes/verify_open_route_obstructions.py`.

## Checklist before reusing an abandoned route

1. Identify the exact line above that blocked the argument.
2. State the new lemma that overcomes it, with quantifiers and the full density interval.
3. Check coefficient signs before substituting bounds.
4. Check zero and threshold cases before dividing.
5. Check that the proof uses homomorphism densities of arbitrary graphons, not regular graphons, step graphons, injective copies, or minimum-degree assumptions.
6. Check the chromatic polynomial and target independently.
7. Compile the TeX and run a token scan for malformed tensor notation; compilation alone is not a mathematical check.
