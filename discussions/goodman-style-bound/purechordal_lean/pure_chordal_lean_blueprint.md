# Pure chordal graphs: a graphon-direct Lean blueprint

## Purpose of this revision

This is a replacement for the approximation-dependent part of the earlier blueprint.
The proof below stays inside graphon space. It does **not** use:

- finite-graph approximation of graphons;
- the cut norm or cut metric;
- compactness of graphon space;
- continuity of homomorphism densities in cut distance;
- regularity or sampling lemmas;
- any additional axiom standing for one of those results.

The only limiting argument is the elementary regularisation
$$
W_\varepsilon := \varepsilon +(1-\varepsilon)W,
\qquad 0<\varepsilon<1,
$$
followed by the pointwise estimate
$$
\bigl|t(F,W_\varepsilon)-t(F,W)\bigr|
\le |E(F)|\,\varepsilon.
$$
Thus the required analytic infrastructure is finite-product integration, Tonelli/Fubini,
Cauchy--Schwarz, the real logarithm, and finite algebra.

The source theorem is:

> Let `H` be a connected chordal graph whose maximal cliques all have size
> `r >= 3`. Let `W` be a graphon with edge density
> `p >= 1 - 1/(r-1)`. Then
> $$
> t(H,W)\ge (1-p)^{v(H)}\chi_H\!\left(\frac1{1-p}\right).
> $$

For formalisation, the primary right-hand side should be the clique-tree expression
$$
\frac{A_r(p)^m}{\prod_{e\in E(T)}A_{s_e}(p)},
\qquad
A_s(p)=\prod_{a=0}^{s-1}\bigl(1-a(1-p)\bigr),
$$
where `m` is the number of maximal cliques and `s_e` is the size of the
separator on the clique-tree edge `e`. The chromatic-polynomial identity is a
separate finite-combinatorial theorem.

---

## 1. Formal dependency boundary

There are three independent components.

### 1.1 Basic graphon layer

Required:

1. a graphon `W : Omega × Omega -> R`, measurable, symmetric, and a.e. in `[0,1]`;
2. homomorphism density of a finite simple graph;
3. finite product measures indexed by a finite type;
4. Tonelli/Fubini and elementary integral inequalities.

No quotient by weak isomorphism is required. No metric on graphons is required.
It is simplest to work with the unit interval with Lebesgue measure, although the
clique-tree gluing argument works on any probability space.

### 1.2 Finite graph structure layer

The analytic theorem should first assume an explicit clique-tree certificate.
The certificate records:

- a finite tree `T` indexing bags `C_i`;
- every bag is an `r`-clique;
- bags cover every vertex and every edge of `H`;
- the running-intersection property;
- distinct adjacent bags are distinct.

From this certificate one proves the separator and multiplicity lemmas used below.
The wrapper

```text
connected + chordal + every maximal clique has size r
    -> existence of a pure clique-tree certificate
```

is a separate graph-theoretic theorem. It is the main non-analytic structural
formalisation. It can be developed through perfect elimination orderings or a
standard maximal-clique tree theorem.

### 1.3 Clique-density layer

The source uses the Moon--Moser adjacent-clique inequality. It also has a direct
graphon proof; no finite approximation is needed. A convenient cross-multiplied
form is
$$
m\,t_m^2
\le t_{m-1}t_m +(m-1)t_{m-1}t_{m+1},
\qquad m\ge 2,
\tag{MM}
$$
where `t_j = t(K_j,W)` and `t_0=t_1=1`.

From `(MM)` one proves, under the relevant positivity hypotheses,
$$
\frac{t_j}{t_{j-1}}
\ge 1-(j-1)(1-p).
\tag{ratio}
$$

---

## 2. The combinatorial clique-tree certificate

A schematic structure is:

```lean
structure PureCliqueTreeDecomp
    (H : SimpleGraph V) (r : ℕ) where
  I                : Type*
  instFintypeI     : Fintype I
  instDecidableEqI : DecidableEq I
  T                : SimpleGraph I
  tree             : T.IsTree
  bag              : I → Finset V
  bag_card         : ∀ i, (bag i).card = r
  bag_clique       : ∀ i, H.IsClique (bag i : Set V)
  bag_injective    : Function.Injective bag
  vertex_cover     : ∀ v, ∃ i, v ∈ bag i
  edge_cover       : ∀ ⦃u v⦄, H.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i
  running_intersection :
    ∀ v i j,
      v ∈ bag i → v ∈ bag j →
      ∀ k, k ∈ T.path i j → v ∈ bag k
```

Exact field names depend on the tree API. It is acceptable to use a stronger,
rooted certificate if that makes the analytic proof simpler.

Fix a root `rho`. For each non-root bag `i`, let `parent i` be its parent and put
$$
S_i=C_i\cap C_{\operatorname{parent}(i)},
\qquad s_i=|S_i|,
\qquad N_i=C_i\setminus S_i.
$$
For the root, put `N_rho = C_rho`.

The required finite lemmas are as follows.

### 2.1 Separator size

For every non-root bag,
$$
s_i<r.
$$
Indeed, two distinct `r`-element bags cannot have an `r`-element intersection.
Consequently `s_i <= r-1`.

### 2.2 New-vertex partition

The sets `N_i` are pairwise disjoint and
$$
V(H)=\bigsqcup_i N_i.
$$
Equivalently, when a bag is processed after its parent, the vertices of that bag
that have already occurred are exactly its parent separator.

### 2.3 Tree edge count

If the clique tree has `m` nodes, then it has `m-1` edges. Thus there are
`m-1` non-root bags.

### 2.4 Vertex count

The partition gives
$$
v(H)=mr-\sum_{i\ne\rho}s_i.
\tag{VC}
$$

### 2.5 Edge-weight multiplicity identity

For a finite vertex set `A`, define its clique weight at an assignment `x` by
$$
\kappa_A(x)=\prod_{\{u,v\}\in\binom A2}W(x_u,x_v).
$$
Let
$$
\kappa_H(x)=\prod_{uv\in E(H)}W(x_u,x_v).
$$
Then
$$
\prod_{i\in I}\kappa_{C_i}(x)
=
\kappa_H(x)\prod_{i\ne\rho}\kappa_{S_i}(x).
\tag{EW}
$$

To prove `(EW)`, fix an edge `uv` of `H`. The bags containing both `u` and `v`
form a nonempty connected subtree. If it has `a` nodes, it has `a-1` tree edges.
Hence its exponent on the left is one larger than its exponent in the separator
product. This argument is pointwise and contains no graphon analysis.

For Lean, it may be profitable to expose `(EW)` directly as a theorem of the
certificate before starting any measure-theoretic work.

---

## 3. Homomorphism-density conventions

For a finite simple graph `F` on a finite vertex type,
$$
t(F,W)=
\int_{\Omega^{V(F)}}
\prod_{uv\in E(F)}W(x_u,x_v)\,d\mu^{V(F)}(x).
$$

Write
$$
t_s=t(K_s,W),
\qquad t_0=t_1=1.
$$

Use a cross-multiplied formulation for the clique-tree gluing theorem:
$$
t(H,W)\prod_{i\ne\rho}t_{s_i}
\ge t_r^m.
\tag{G}
$$
This statement is meaningful even when some clique density vanishes.

A schematic Lean statement is:

```lean
lemma cliqueTree_gluing_mul
    (D : PureCliqueTreeDecomp H r)
    (W : GraphonI) :
    homDensity H W *
        (∏ i : {i // i ≠ D.root}, cliqueDensity (D.sepCard i) W)
      ≥ (cliqueDensity r W) ^ Fintype.card D.I := by
  ...
```

The exact representation of the root and non-root subtype is flexible.

---

## 4. A local Gibbs inequality

The direct graphon gluing proof only needs the following elementary fact.

### Lemma 4.1: Gibbs inequality for bounded positive densities

Let `f,g` be strictly positive measurable functions on a probability space, with
$$
\int f=\int g=1,
$$
and assume all logarithmic expressions below are integrable. Then
$$
\int f\log\frac{g}{f}\le 0.
\tag{GI}
$$

Proof: for `u>0`, `log u <= u-1`. Apply this with `u=g/f`:
$$
f\log(g/f)\le g-f.
$$
Integrate.

There is no need to define Shannon entropy, conditional entropy, relative
entropy, or regular conditional probability as reusable abstractions. One local
integral lemma is sufficient.

Schematic Lean interface:

```lean
lemma integral_mul_log_div_nonpos
    {f g : Ω → ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_pos : ∀ᵐ x ∂μ, 0 < f x)
    (hg_pos : ∀ᵐ x ∂μ, 0 < g x)
    (hf_one : ∫ x, f x ∂μ = 1)
    (hg_one : ∫ x, g x ∂μ = 1)
    (hint : Integrable (fun x => f x * Real.log (g x / f x)) μ) :
    ∫ x, f x * Real.log (g x / f x) ∂μ ≤ 0 := by
  -- pointwise `Real.log_le_sub_one_of_pos`
  -- multiply by `f >= 0`, integrate, and use the two normalisations
  ...
```

In the application below all densities are bounded above and below by positive
constants, so integrability is immediate.

---

## 5. Direct graphon proof of clique-tree gluing

### 5.1 First assume a uniformly positive graphon

Assume
$$
0<\delta\le W(x,y)\le 1
$$
a.e. for some `delta>0`.
Then every finite clique weight and every clique density is strictly positive.
All logarithms below are bounded.

For every bag `C_i`, define the normalised `r`-clique density
$$
\mu_i(x_{C_i})=
\frac{\kappa_{C_i}(x_{C_i})}{t_r}.
$$
It is a probability density on `Omega^{C_i}`.

For a non-root bag `i`, define the separator marginal
$$
q_i(x_{S_i})
=
\int_{\Omega^{N_i}}
\mu_i(x_{S_i},y_{N_i})\,d\mu^{N_i}(y).
\tag{SM}
$$
Then `q_i` is a strictly positive probability density on `Omega^{S_i}`.

Define the conditional extension density
$$
K_i(y_{N_i}\mid x_{S_i})
=
\frac{\mu_i(x_{S_i},y_{N_i})}{q_i(x_{S_i})}.
\tag{CK}
$$
For every fixed separator assignment,
$$
\int K_i(\cdot\mid x_{S_i})=1.
$$
This is an explicit quotient of functions; no conditional-expectation API is
needed.

### 5.2 The junction-tree density

Define a density on assignments to all vertices of `H` by
$$
P(x)=
\mu_\rho(x_{C_\rho})
\prod_{i\ne\rho}K_i(x_{N_i}\mid x_{S_i}).
\tag{JT}
$$

Because the `N_i` partition the vertex set, `(JT)` is an ordinary measurable
function on `Omega^{V(H)}`.

### 5.3 Normalisation

Prove
$$
\int P=1.
\tag{P1}
$$

One formal route is leaf elimination. If `i` is a leaf different from the root,
all variables in `N_i` occur only in the factor `K_i`. Integrating those variables
removes that factor because it integrates to one. Repeat until only the root bag
remains, whose density also integrates to one.

A rooted topological-order proof is equivalent. Leaf elimination is often better
suited to induction on a finite tree.

### 5.4 Bag and separator marginals

For every bag `i`, the marginal of `P` on `C_i` is `mu_i`. Consequently, the
marginal of `P` on `S_i` is `q_i`.

The key consistency statement is that the restriction of the parent bag law to
`S_i` equals the restriction of the child bag law to `S_i`. Both are marginals of
the same normalised `r`-clique weight, and the two bags have the same cardinality
`r`. This is exactly where purity of the chordal graph is used analytically.

In Lean, isolate the coordinate-renaming lemma:

```lean
lemma cliqueLaw_separatorMarginal_eq
    (hC : C.card = r) (hD : D.card = r)
    (hS : S ⊆ C) (hS' : S ⊆ D)
    (hcard : (C \ S).card = (D \ S).card) :
    marginal (cliqueLaw W C) S = marginal (cliqueLaw W D) S := by
  -- rename the integrated coordinates by a finite equivalence
  ...
```

A more specialised theorem is acceptable.

### 5.5 Relating `P` to the `H`-weight

By `(EW)`,
$$
P(x)
=
\frac{\kappa_H(x)}{t_r^m}
\prod_{i\ne\rho}
\frac{\kappa_{S_i}(x_{S_i})}{q_i(x_{S_i})}.
\tag{PF}
$$

Let
$$
Q_H(x)=\frac{\kappa_H(x)}{t(H,W)}.
$$
This is a strictly positive probability density.

Apply `(GI)` to `f=P` and `g=Q_H`, or equivalently use the nonnegativity of
`integral P * log(P/Q_H)`. Expanding `(PF)` and using the separator marginals gives
$$
0
\le
\log t(H,W)-m\log t_r
+
\sum_{i\ne\rho}
\int q_i\log\frac{\kappa_{S_i}}{q_i}.
\tag{E1}
$$

For each separator, let
$$
\nu_i(x_{S_i})=\frac{\kappa_{S_i}(x_{S_i})}{t_{s_i}}.
$$
This is the normalised `K_{s_i}` density. Applying `(GI)` to `q_i` and `nu_i`
yields
$$
\int q_i\log\frac{\kappa_{S_i}}{q_i}
=
\log t_{s_i}
+
\int q_i\log\frac{\nu_i}{q_i}
\le
\log t_{s_i}.
\tag{E2}
$$

Combining `(E1)` and `(E2)`,
$$
0
\le
\log t(H,W)-m\log t_r+
\sum_{i\ne\rho}\log t_{s_i}.
$$
Exponentiating gives
$$
t(H,W)\prod_{i\ne\rho}t_{s_i}\ge t_r^m.
$$
Thus `(G)` holds for uniformly positive graphons.

### 5.6 Formal point about inequality directions

The clean formal chain is
$$
0\le D(P\|Q_H)
\le
\log t(H,W)-m\log t_r+
\sum_i\log t_{s_i}.
$$
The second inequality uses `(E2)`. Therefore the final logarithm is nonnegative.
This direction should be recorded explicitly in the blueprint to avoid a common
sign error.

---

## 6. Removing strict positivity without graphon approximation

For `0<epsilon<1`, define
$$
W_\varepsilon=\varepsilon +(1-\varepsilon)W.
$$
Then
$$
\varepsilon\le W_\varepsilon\le1,
$$
so the previous section applies:
$$
t(H,W_\varepsilon)
\prod_{i\ne\rho}t(K_{s_i},W_\varepsilon)
\ge
 t(K_r,W_\varepsilon)^m.
\tag{G-eps}
$$

### 6.1 Elementary product estimate

For numbers `a_j,b_j` in `[0,1]`,
$$
\left|\prod_{j=1}^d a_j-\prod_{j=1}^d b_j\right|
\le
\sum_{j=1}^d|a_j-b_j|.
\tag{TP}
$$
Prove `(TP)` by telescoping the product.

Since
$$
|W_\varepsilon-W|\le\varepsilon,
$$
`(TP)` gives, for every finite graph `F`,
$$
|t(F,W_\varepsilon)-t(F,W)|
\le |E(F)|\varepsilon.
\tag{HD-eps}
$$

This is stronger than the convergence needed here and avoids dominated
convergence entirely.

### 6.2 Passing to zero

Take, for example, `epsilon_n = 1/(n+2)`. By `(HD-eps)`, every density occurring
in `(G-eps)` converges to its density in `W`. Powers and finite products preserve
limits. Passing to the limit gives `(G)` for the original graphon.

A schematic Lean theorem is:

```lean
lemma homDensity_regularize_tendsto
    (F : SimpleGraph V) [Fintype V] (W : GraphonI) :
    Tendsto
      (fun n => homDensity F (regularize W (1 / (n + 2 : ℝ))))
      atTop
      (𝓝 (homDensity F W)) := by
  -- use the explicit bound `|...| <= F.edgeFinset.card / (n+2)`
  ...
```

No cut-distance continuity theorem appears.

---

## 7. Direct graphon Moon--Moser inequality

The following proof is entirely inside graphon space.

Let
$$
t_j=t(K_j,W).
$$
For `m>=2`, define, for `z=(z_1,...,z_{m-1})`,
$$
A(z)=\prod_{1\le a<b\le m-1}W(z_a,z_b),
\qquad
\eta(z)=\int_\Omega\prod_{a=1}^{m-1}W(x,z_a)\,d\mu(x).
$$
Then
$$
t_{m-1}=\int A,
\qquad
t_m=\int A\eta.
$$
Cauchy--Schwarz gives
$$
t_m^2\le t_{m-1}\int A\eta^2.
\tag{CS}
$$

It remains to prove
$$
\int A\eta^2
\le
\frac{t_m+(m-1)t_{m+1}}{m}.
\tag{SYM}
$$

### 7.1 The pointwise finite inequality

On an ordered `(m+1)`-tuple, write `a_e in [0,1]` for the graphon value on an
unordered coordinate edge `e`. Define

$$
K=\prod_e a_e,
$$
$$
B=\sum_e\prod_{f\ne e}a_f,
$$
and
$$
S=\sum_{v=1}^{m+1}
\prod_{e\subseteq [m+1]\setminus\{v\}}a_e.
$$
Then
$$
2B\le S+(m^2-1)K.
\tag{Cube}
$$

Both sides are affine in each edge variable. Hence it is enough to check
`a_e in {0,1}`. There are three cases:

1. at least two missing edges: `B=K=0`;
2. exactly one missing edge: `B=1`, `K=0`, `S=2`;
3. no missing edge: `B=binom(m+1,2)`, `K=1`, `S=m+1`.

In every case `(Cube)` holds, in fact with equality in the last two cases.
Symmetrising and integrating `(Cube)` gives `(SYM)`. Combining `(CS)` and
`(SYM)` yields
$$
m t_m^2
\le t_{m-1}t_m+(m-1)t_{m-1}t_{m+1}.
$$

### 7.2 Lean implementation of the cube reduction

Do not invoke a general theorem about extrema of multilinear polynomials unless
one is already convenient. A short induction over the finite edge set suffices.
For a multiaffine function `F` and a chosen coordinate `e`,
$$
F(a)=(1-a_e)F(a[e:=0])+a_eF(a[e:=1]).
$$
Thus nonnegativity on all Boolean vertices implies nonnegativity on the cube.

A reusable local lemma can be:

```lean
lemma multiaffine_nonneg_on_Icc_of_boolean
    {E : Type*} [Fintype E] [DecidableEq E]
    (F : (E → ℝ) → ℝ)
    (haff : ∀ e a, F a = (1-a e) * F (Function.update a e 0)
                         + a e * F (Function.update a e 1))
    (hbool : ∀ a : E → ℝ, (∀ e, a e = 0 ∨ a e = 1) → 0 ≤ F a)
    (ha : ∀ e, a e ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ F a := by
  ...
```

It may be simpler to specialise this lemma directly to the polynomial in
`(Cube)`.

---

## 8. Deriving the clique-ratio bound

Put
$$
q=1-p,
\qquad
c_j=1-(j-1)q.
$$
Assume
$$
p\ge 1-\frac1{r-1}.
$$
Then `c_j>=0` for `2<=j<=r`, and `c_j>0` for `2<=j<r`.

The base case is
$$
t_2=p=c_2t_1.
$$
Suppose `2<=m<r` and
$$
t_m\ge c_m t_{m-1}.
$$
Since `c_m>0`, the induction hypotheses imply `t_m>0` and `t_{m-1}>0`.
From `(MM)`,
$$
(m-1)t_{m-1}t_{m+1}
\ge t_m(mt_m-t_{m-1}).
$$
Also
$$
mt_m-t_{m-1}
\ge (mc_m-1)t_{m-1}
=(m-1)c_{m+1}t_{m-1}.
$$
Canceling positive factors gives
$$
t_{m+1}\ge c_{m+1}t_m.
$$
Therefore, for every `2<=j<=r`,
$$
t_j\ge c_jt_{j-1}.
\tag{Step}
$$

Iterating `(Step)` gives
$$
t_j\ge A_j(p),
\tag{A-lower}
$$
and, for `0<=s<=r`, whenever the quotient is needed,
$$
\frac{t_r}{t_s}
\ge
\frac{A_r(p)}{A_s(p)}.
\tag{A-ratio}
$$

For Lean, first prove the cross-multiplied version
$$
t_r A_s(p)\ge t_s A_r(p).
$$
Use division only after proving the denominator is positive.

---

## 9. Combining gluing and clique ratios

Let `m` be the number of bags and `s_i<r` the separator sizes.
The direct graphon gluing theorem gives
$$
t(H,W)
\ge
 t_r\prod_{i\ne\rho}\frac{t_r}{t_{s_i}},
$$
provided the displayed denominators are positive.

There are two cases.

### 9.1 Boundary case `A_r(p)=0`

The desired right-hand side is zero because every separator factor
`A_{s_i}(p)` is strictly positive. Since `t(H,W)>=0`, the theorem is immediate.

### 9.2 Positive case `A_r(p)>0`

Then `(A-lower)` gives `t_s>0` for all `s<=r`. Apply `(A-ratio)`:
$$
\begin{aligned}
t(H,W)
&\ge
 t_r\prod_{i\ne\rho}\frac{t_r}{t_{s_i}}\\
&\ge
 A_r(p)
 \prod_{i\ne\rho}\frac{A_r(p)}{A_{s_i}(p)}\\
&=
\frac{A_r(p)^m}{\prod_{i\ne\rho}A_{s_i}(p)}.
\end{aligned}
$$

This proves the explicit pure-chordal inequality without graphon approximation.

---

## 10. Chromatic-polynomial factorisation

The analytic proof should not depend on a general chromatic-polynomial library.
First prove the explicit `A`-formula. Then separately identify it with the source's
chromatic expression.

For a rooted clique tree, the root `K_r` has `(x)_r` proper colourings. A child
bag attached along a separator of size `s_i` contributes
$$
(x-s_i)_{r-s_i}=\frac{(x)_r}{(x)_{s_i}}.
$$
Therefore
$$
\chi_H(x)
=
\frac{(x)_r^m}{\prod_{i\ne\rho}(x)_{s_i}}.
\tag{CP}
$$
This can first be proved as an identity of natural-number colouring counts for
all sufficiently large natural `x`, and then promoted to a polynomial identity.
Alternatively, define the right-hand side after cancellation as the chromatic
polynomial of this certified graph and prove the universal evaluation property.

Using `(VC)` and
$$
A_s(p)=(1-p)^s\left(\frac1{1-p}\right)_s
\qquad (p\ne1),
$$
`(CP)` gives
$$
(1-p)^{v(H)}\chi_H\!\left(\frac1{1-p}\right)
=
\frac{A_r(p)^m}{\prod_iA_{s_i}(p)}.
$$
At `p=1`, use the polynomial or finite-product expression, not the rational
presentation.

---

## 11. Suggested theorem hierarchy

### 11.1 Pure analytic theorem from a certificate

```lean
/-- Clique-tree gluing, entirely in graphon space. -/
theorem homDensity_mul_sep_ge_cliqueDensity_pow
    (D : PureCliqueTreeDecomp H r)
    (W : GraphonI) :
    homDensity H W * D.separatorDensityProduct W
      ≥ (cliqueDensity r W) ^ D.numBags := by
  -- regularise, construct the junction density, apply Gibbs twice,
  -- then pass epsilon -> 0 by the explicit density bound
  ...
```

### 11.2 Direct adjacent-clique theorem

```lean
theorem cliqueDensity_moon_moser
    (W : GraphonI) (m : ℕ) (hm : 2 ≤ m) :
    (m : ℝ) * cliqueDensity m W ^ 2
      ≤ cliqueDensity (m-1) W * cliqueDensity m W
        + (m-1 : ℝ) * cliqueDensity (m-1) W
            * cliqueDensity (m+1) W := by
  ...
```

### 11.3 Iterated ratio theorem

```lean
theorem cliqueDensity_step_lower
    (W : GraphonI) {r : ℕ} (hr : 3 ≤ r)
    (hp : 1 - 1 / (r-1 : ℝ) ≤ edgeDensity W) :
    ∀ j, 2 ≤ j → j ≤ r →
      cliqueDensity j W
        ≥ (1 - (j-1 : ℝ) * (1-edgeDensity W))
            * cliqueDensity (j-1) W := by
  ...
```

### 11.4 Main explicit theorem

```lean
theorem pureCliqueTree_goodman
    (D : PureCliqueTreeDecomp H r)
    (hr : 3 ≤ r)
    (W : GraphonI)
    (hp : 1 - 1 / (r-1 : ℝ) ≤ edgeDensity W) :
    homDensity H W
      ≥ A r (edgeDensity W) ^ D.numBags
          / D.separatorAProduct (edgeDensity W) := by
  ...
```

### 11.5 Chordal wrapper

```lean
theorem pureChordal_goodman
    (hconn : H.Connected)
    (hchordal : H.IsChordal)
    (hpure : ∀ C, IsMaximalClique H C → C.card = r)
    ... :
    ... := by
  obtain ⟨D⟩ := exists_pureCliqueTreeDecomp hconn hchordal hpure
  exact pureCliqueTree_goodman D ...
```

The wrapper contains no analytic content. It should be implemented only after
the certificate theorem is complete.

---

## 12. Implementation order

A realistic order is:

1. define `A_s(p)` and prove its recurrence and positivity in the density range;
2. define the explicit clique-tree certificate;
3. prove separator cardinality, new-vertex partition, vertex count, and `(EW)`;
4. establish the basic clique-weight and marginal integration API;
5. prove the bounded positive-density Gibbs lemma;
6. for positive graphons, define `q_i`, `K_i`, and `P`;
7. prove normalisation and bag/separator marginals of `P`;
8. prove positive-graphon gluing by the two Gibbs applications;
9. prove the telescoping product estimate `(TP)`;
10. regularise and obtain gluing for arbitrary graphons;
11. prove the pointwise cube inequality and the graphon Moon--Moser recurrence;
12. derive the one-step and iterated clique-ratio bounds;
13. combine the two analytic ingredients;
14. formalise the chromatic-polynomial factorisation;
15. formalise the chordal-to-clique-tree wrapper.

The high-risk implementation points are coordinate bookkeeping in finite product
spaces and the clique-tree structural theorem. Cut-metric graphon theory is not
on the dependency path.

---

## 13. Minimal import philosophy

The proof should depend only on the graphon basic/hom-density layer plus ordinary
Mathlib measure theory and finite graph theory. In particular, no file defining
or proving facts about the following objects is logically needed:

- cut norm;
- cut distance;
- regularity partitions;
- graphon compactness;
- graphon sampling;
- convergence modulo measure-preserving relabellings.

A direct graphon-space implementation is therefore compatible with an
axiom-clean development whose theorem statement is about an actual graphon
representative rather than a quotient graphon space.

---

## 14. Sanity checks

### One bag

For `H=K_r`, the tree has one node and no separators. Gluing says `t_r>=t_r`.
The main theorem reduces to `t_r>=A_r(p)`.

### Two bags glued along `K_s`

The gluing theorem becomes
$$
t(K_r\cup_{K_s}K_r,W)t_s\ge t_r^2.
$$
Here it can also be checked directly by Cauchy--Schwarz:
$$
t(K_r\cup_{K_s}K_r,W)
=
\int \frac{R(x_S)^2}{\kappa_S(x_S)}\,dx_S
\ge
\frac{(\int R)^2}{\int\kappa_S}
=
\frac{t_r^2}{t_s}.
$$
This is a useful regression theorem for the general junction-tree code.

### Triangle books

For `r=3`, all separators in an ordinary triangle book have size `2`.
The formula gives
$$
t(B_{3,m},W)\ge p(2p-1)^m,
\qquad p\ge\frac12.
$$

---

## 15. Final dependency assessment

A proof with no custom axiom is feasible without formalising graphon limits.
The required new material is:

- a finite clique-tree decomposition interface;
- a direct junction-tree density argument using two elementary Gibbs inequalities;
- an elementary regularisation lemma;
- the direct graphon Moon--Moser recurrence;
- optionally, a chromatic-polynomial API;
- finally, the finite theorem that a chordal graph's maximal cliques admit a
  clique tree.

The graphon part is measure-theoretic but local. It does not require the global
geometry or topology of graphon space.
