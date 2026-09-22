# Compact verification of the Atlas126 supporting planes

This records the reductions used by the new Lean implementation. The original
supporting-plane statement is unchanged. A complete catalogue result still
requires the whole-row build and axiom audit; component checks alone do not
promote the row.

Write the cleared residual as

\[
R(d,a,t)=(1-d)t^3+dt(a-t)^2
-d(1-d)[C+\beta(d-p)+\gamma(a-d^2)+\lambda(t-g)].
\]

For positive t, its vertex in a is
\(a_*=t+\gamma(1-d)/(2t)\). Define

\[
H(d,t)=4t^4-d(1-d)\gamma^2
-4dt[C+\beta(d-p)+\gamma(t-d^2)+\lambda(t-g)].
\]

The exact identities are
\(4tR(d,a_*,t)=(1-d)H(d,t)\) and
\(R(d,a,t)=R(d,a_*,t)+dt(a-a_*)^2\).

## Only two boundary families are needed

Set \(s=t(p-t)-(1-d)\gamma\). The new certificates prove H nonnegative whenever
s is nonnegative, under a few elementary bounds. This is stronger than proving
H only when its vertex is feasible. It implies R nonnegative for **every** a.

If s is negative, the vertex is above (t+p)/2. Thus the minimum on the feasible
a interval occurs at its upper endpoint, min(d,(t+p)/2). It suffices to check
the faces a=d and a=(t+p)/2. There is no lower-boundary certificate family.
The t=0 case follows from monotonicity in a and is included separately.

`SlackPlane.polynomialPlane_of_upper_and_interior` formalizes this reduction.
Its hypotheses retain t <= p, which follows from t <= a and 2a-p <= t.

## Low-density slack coordinates

The density parameter is p(x)=(3+2x-x^2)/6 and the triangle profile is
g(x)=x(3-x)^2/18. The A, C and J intervals in x are [0,5/8], [5/8,15/16]
and [15/16,1], respectively. In edge density these are [1/2,247/384],
[247/384,341/512] and [341/512,2/3].

Let L=gamma-t(p-t) and Q=C-beta*p+(gamma+lambda)*t-lambda*g. Then

\[
S(s,t)=4\gamma^2t^4-(L+s)(\gamma-L-s)\gamma^2
-4\gamma t(L+s)Q-4\beta t(L+s)^2+4t(L+s)^3
\]

satisfies S(s,t)=gamma^2 H(d,t) when s=t(p-t)-(1-d)gamma.
For d<=1, gamma>0 and p<=2/3, feasible nonnegative s lies in [0,1/9].
The C and junction planes use this fixed box. The junction density coordinate
is reversed, r=1-x, and its entire slack box needs six numerical leaves.

For A there is a further reduction. Define

\[
r=(-4x^2+8x+3)/12,\qquad \gamma_A=r^2,\qquad \rho=1/2+5x/12.
\]

Here r>0 and p<=2r. Put t=2ru, v=s/r^2 and
N=r(1+v+4u^2)-2pu. Then N=rd. The polynomial

\[
4r^4(2u)^4-N(r-N)r^2
-4N(2u)[C-2r^2\rho p-\lambda g+(r^3+\lambda r)(2u)
+2r\rho N-N^2]
\]

equals H itself. The fixed box is x in [0,5/8], v,u in [0,1]. Its degrees are
(12,3,7), instead of (18,3,7) for the first slack construction. The equality
at (x,v,u)=(0,1/4,1/4) has a small quadratic-form neighborhood. Outside that
neighborhood, the exact subdivision has 72 numerical leaves, grouped into
eleven compilation units.

## High-density reductions

Write gamma=p*G, where G=2(9p^2-10p+3)>0. Scale t=p*u and s=p*v. For p in
[2/3,1], d<=1 and nonnegative s, one has u in [0,1] and v in [0,1/4]. The
polynomial in `HighScaledSlack` satisfies

\[
p^2 S_{\mathrm{high}}(p,v,u)=G^2 H(d,p u)
\]

when v=p*u*(1-u)-(1-d)*G. Its degree is (8,3,7), and four boxes suffice.
The unscaled box t in [0,1] is not valid in this density range: it includes
t>p. The scaling and the retained feasibility bound are essential.

The upper faces are covered by two cubes for a=d and six cubes for
a=(t+p)/2. `HighCoverage` proves this using closed-interval scaling, including
every zero-width endpoint case. The right/high cube has the exact form

\[
A((1-x)d)^2+B((1-x)d)(xu)+C(xu)^2.
\]

A,C and 4AC-B^2 are nonnegative on d<=1/2 and on x>=15/16. These two regions
cover the equality curve and the collapsed endpoints. Ten numerical boxes
cover the remaining region, replacing the original 5,785-box search.

The left/low cube similarly has a quadratic-form neighborhood at d=u=1 and
eight remaining numerical boxes. The first upper-face corner uses a sum of
nonnegative weighted squares and a nonnegative cross term on a radius-1/64
box; eighteen numerical boxes remain outside it.

## What the checker trusts

Python finds subdivisions and rational witnesses. Lean checks polynomial
identities, the complete subdivision, integer transformation tables and signs.
The numerical proofs use `decide +kernel`; no native arithmetic oracle or
external solver result is an axiom. The staged Bernstein checker shares input
tables and clears rational denominators before checking integer products.

The finite coloring calculation is isolated from the rooted graphon imports.
It checks the seven edges directly, after proving equivalence with the original
proper-coloring predicate. The surjective coloring counts for 0 through 6
colors are 0, 0, 0, 36, 360, 960 and 720. All are kernel checked; the last also
follows from the general factorial formula for bijective colorings.

Compilation is sequential. The acceptance measurement must rebuild every
row-specific source in the final dependency closure against the already built
common library. It must include the graphon bridge and coloring counts, stay
within one hour and 16 GiB, and end with an axiom audit of the catalogue theorem.
