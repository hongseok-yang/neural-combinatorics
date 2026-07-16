# Audit and Lean-oriented proof blueprint for `paper_region2_v2.pdf`

## Question

Determine whether the submitted article proves its stated odd-cycle inequality, distinguish standard mathematical terminology from manuscript-specific terminology, and rewrite the verified argument in standard language at a level suitable for planning a Lean formalisation.

## 1. Verdict

The PDF, by itself, is **not a complete proof of Corollaries 1.2 and 1.3**.

There are two distinct reasons.

1. The two decisive finite computations are absent. Lemma 5.3 is justified only by a reference to `zoneB_certifier.py`, and the range of Lemma 6.3 with
   \[
   \frac1{60}\le e\le \frac13-\frac1{1000}
   \]
   is justified only by a reference to `zoneC_certifier.py`. Neither program, its output, nor the finite list of certified boxes occurs in the supplied material. Section 8 describes a possible verification protocol but does not contain the certificate. Consequently, the scalar Theorem 1.1 is not established by the PDF alone.

2. The final corollaries invoke other results not supplied in the PDF: the cases \(m\le 13\), the range \(p\ge 2/3\), and hence the claimed theorem for all densities. These dependencies are attributed to an “earlier consolidated note”. They cannot be audited from this file.

The following substantial part *is* mathematically coherent and can be checked directly from the PDF:

- the operator decomposition;
- the Hilbert--Schmidt estimate;
- the reduction to the unique eigenvalue \(\alpha>q\), if such an eigenvalue exists;
- the eigenfunction inequalities;
- the reduction to the explicit scalar inequality
  \[
  R_m\le C_m\psi(\xi,\rho);
  \]
- the elementary formula for \(\psi\);
- the analytic arguments in Sections 4, 5.2, 6.1, 6.3, and the assembly, subject to routine verification of the displayed rational constants.

I found no counterexample to the central scalar inequality in an independent numerical stress test. This is evidence against a simple numerical error, but it is not a proof and does not replace the missing certificates.

Thus the appropriate classification is:

> **Plausibly correct central argument, but incomplete and not independently reproducible as supplied.**

## 2. Terminology audit

The rightmost column gives terminology suitable for a formal proof.

| Expression in the PDF | Status | Standard replacement |
|---|---|---|
| graphon | Standard | symmetric measurable \(W:[0,1]^2\to[0,1]\), up to null sets |
| homomorphism density \(t(F,W)\) | Standard | homomorphism density |
| integral operator \(T_U\) | Standard | Hilbert--Schmidt integral operator with kernel \(U\) |
| compression | Standard operator terminology | \(A=P_{\mathbf 1^\perp}T_UP_{\mathbf 1^\perp}\) |
| Hilbert--Schmidt budget | Manuscript label | the inequality \(\operatorname{tr}(A^2)+2\lVert g\rVert_2^2\le pq\) |
| one-sided spectral shift | Manuscript label | the trace/coefficient identity (equation (4)) |
| frontier eigenvalue | Nonstandard, manuscript-specific | the unique eigenvalue \(\alpha>q\) of \(A\), when it exists |
| no-frontier case | Manuscript label | the case \(\lambda_{\max}(A)\le q\) |
| forced variance | Manuscript label | the lower bound \(\lVert g\rVert_2^2\ge \alpha(\alpha-q)^2/[2(1-2\alpha)]\) |
| frontier ceiling | Manuscript label | the consequence \(\alpha^2+q\alpha-q\le0\) |
| master defect | Nonstandard, manuscript-specific | the lower bound in Proposition 2.7 for the target difference |
| coupling | Standard in broad operator language, but informal here | the scalar coefficient \(c=\langle g,\phi\rangle\) or the orthogonal component \(g-c\phi\) |
| direct channel | Manuscript-specific | the pointwise-kernel bound on \(c\) in Lemma 2.8 |
| safe channel | Manuscript-specific | the quadratic estimate involving \(g-c\phi\) and \(k\) in Lemma 2.9 |
| safe subspace | Manuscript-specific | \(\{\mathbf1,\phi\}^{\perp}\) |
| Huber elimination / Huber payment | At best an analogy; not needed | minimisation of the explicit convex function \(\rho v^2+(\xi-v+v^2)_+\) |
| payment | Manuscript metaphor | lower bound supplied by \(C_m\psi(\xi,\rho)\) |
| defect | Common generic word, but manuscript-specific here | \(R_m\), or simply “the scalar remainder” |
| pinch regime / pinch zone | Manuscript-specific | the parameter range \(e\le1/60\) |
| Zone A, B, C | Organisational labels, not mathematical terms | the three cases determined by \(e\lessgtr1/60\) and \(\xi\lessgtr1\) |
| battle | Manuscript-specific rhetoric | the explicit inequality requiring interval verification |
| Turán corner / sliver | Informal geometric description | the range \(0<\alpha-1/3<1/2000\) |
| three-geometric defect | Manuscript-specific | the identity expressing \(R_m\) as a combination of \(x^{m-2},s^{m-2},y^{m-2}\) |
| secant gate | Manuscript-specific | the necessary lower bound on \((m-2)d/q\) when \(R_m>0\) |
| bottom-out estimate | Manuscript-specific | a large-\(m\), small-\(\kappa\) tail estimate |
| exact rational interval certificate | Standard | finite interval-arithmetic certificate with rational outward bounds |

The function \(\psi\) resembles a Huber-type infimal convolution, but no identification with the classical Huber loss is used. A clean proof should simply define \(\psi\) and prove its formula.

## 3. Clean statement of the verified reduction

Let \(W:[0,1]^2\to[0,1]\) be a symmetric measurable function. Put
\[
p=\int_{[0,1]^2}W,\qquad q=1-p,\qquad U=1-W.
\]
Let \(T_U:L^2([0,1])\to L^2([0,1])\) be
\[
(T_Uf)(x)=\int_0^1U(x,y)f(y)\,dy.
\]
Write \(\mathbf1\) for the constant unit vector, let \(P\) be the orthogonal projection onto \(\mathbf1^\perp\), and define
\[
g=T_U\mathbf1-q\mathbf1,\qquad A=PT_UP\big|_{\mathbf1^\perp}.
\]
Relative to \(L^2=\mathbb R\mathbf1\oplus\mathbf1^\perp\),
\[
T_U=
\begin{pmatrix}
q&g^*\\
g&A
\end{pmatrix}.
\]

Assume
\[
\frac13<q<\frac12,qquad m\ge15,qquad m\text{ odd}.
\]
If \(\lambda_{\max}(A)\le q\), then
\[
t(C_m,W)\ge p^m-pq^{m-1}.
\]
Otherwise, \(A\) has exactly one eigenvalue \(\alpha>q\). It satisfies
\[
q<\alpha<\frac12,qquad \alpha^2+q\alpha-q\le0.
\]
Define
\[
L=\sqrt{pq-\alpha^2},\qquad
k_m(\lambda)=\frac{p^{m-1}-\lambda^{m-1}}{p+\lambda},
\]
\[
A_m=2L^{m-2}+mk_m(\alpha),\qquad
B_m=2L^{m-2}+mk_m(L),
\]
\[
R_m=\alpha^m+L^m-pq^{m-1}.
\]
Further put
\[
d=\alpha-q,\quad f=\alpha-L,\quad e=1-2\alpha,
\]
\[
C_m=\frac{B_m f\sqrt{2\alpha}\,e^2}{4\alpha^2},\qquad
\xi=\frac{4\alpha^2d}{e^2},\qquad
\rho=\frac{A_m}{B_m}\frac{\sqrt\alpha}{2\sqrt2f},
\]
and
\[
\psi(\xi,\rho)=\min_{0\le v\le1}
\left(\rho v^2+(\xi-v+v^2)_+\right).
\]
Then the operator and eigenfunction argument proves
\[
t(C_m,W)-p^m+pq^{m-1}
\ge -R_m+C_m\psi(\xi,\rho).
\]
Therefore it remains only to prove
\[
R_m\le C_m\psi(\xi,\rho)
\tag{S}
\]
for
\[
\frac13<q<\frac12,qquad q<\alpha<\frac12,qquad
\alpha^2+q\alpha-q\le0,qquad m\ge15\text{ odd}.
\]

This is the precise mathematically meaningful content of Sections 2 and 3, without any manuscript-specific vocabulary.

## 4. Detailed proof of the operator reduction

### 4.1 Hilbert--Schmidt estimate

Because \(0\le U\le1\), one has \(U^2\le U\) pointwise. Hence
\[
\lVert T_U\rVert_{\mathrm{HS}}^2
=\int U(x,y)^2\,dx\,dy
\le\int U(x,y)\,dx\,dy=q.
\]
The squared Hilbert--Schmidt norm of the block matrix is
\[
q^2+2\lVert g\rVert_2^2+\operatorname{tr}(A^2).
\]
Consequently
\[
\operatorname{tr}(A^2)+2\lVert g\rVert_2^2\le q-q^2=pq.
\tag{1}
\]

For \(h\perp\mathbf1\), write \(h=h_+-h_-\) and let
\[
r=\int h_+=\int h_-=\frac12\lVert h\rVert_1.
\]
Since \(0\le U\le1\),
\[
-2r^2\le\langle h,T_Uh\rangle\le2r^2
\le\frac12\lVert h\rVert_2^2.
\]
Thus
\[
\lVert A\rVert\le\frac12.
\tag{2}
\]

### 4.2 Trace identity

Let \(Jf=\langle f,\mathbf1\rangle\mathbf1\). Then \(T_W=J-T_U\). Conjugating by the isometry that fixes \(\mathbf1\) and negates \(\mathbf1^\perp\) shows that \(T_W\) is unitarily equivalent to
\[
M=
\begin{pmatrix}
p&g^*\\
g&-A
\end{pmatrix}.
\]
For a finite-rank step kernel, Schur complementation gives
\[
\det(I-zM)
=\det(I+zA)
\left(1-pz-z^2\langle g,(I+zA)^{-1}g\rangle\right).
\]
Define the formal power series
\[
u(z)=\frac{z^2\langle g,(I+zA)^{-1}g\rangle}{1-pz},
\qquad
F(z)=-\log(1-u(z)).
\]
Comparing the coefficient of \(z^m\) in
\(-\log\det(I-zM)\) gives
\[
t(C_m,W)=p^m-\operatorname{tr}(A^m)+m[z^m]F(z).
\tag{3}
\]

For a general graphon, approximate \(U\) by conditional expectations on finite dyadic partitions. The kernels converge in \(L^2\), hence the associated operators converge in Hilbert--Schmidt norm. For fixed \(m\):

- cycle density is continuous under this bounded \(L^2\) convergence by a telescoping expansion;
- \(\operatorname{tr}(A^m)\) is continuous by Schatten Hölder inequalities;
- \([z^m]F(z)\) is a polynomial in \(p\) and finitely many scalars \(\langle g,A^jg\rangle\), \(0\le j\le m-2\), and is therefore continuous.

This proves (3) for every graphon.

For Lean, the finite-rank proof followed by an approximation theorem is substantially easier than developing a Fredholm determinant. Only truncated formal power series up to degree \(m\) are required.

### 4.3 The case \(\lambda_{\max}(A)\le q\)

Let \(\nu\) range over the spectrum of \(A\). The coefficient of \(z^n\), \(n\ge2\), in the contribution of the \(\nu\)-eigenspace to \(u(z)\) is
\[
\frac{p^{n-1}-(-\nu)^{n-1}}{p+\nu}\,\lVert E_\nu g\rVert_2^2\ge0,
\]
because \(|\nu|\le1/2<p\). Therefore all coefficients of \(u\), and hence all coefficients of
\(-\log(1-u)=\sum_{r\ge1}u^r/r\), are nonnegative.

If \(\lambda_{\max}(A)\le q\), then, for odd \(m\),
\[
\nu^m\le q^{m-2}\nu^2
\]
for every spectral value \(\nu\): this is immediate for \(\nu\le0\), and follows from \(0\le\nu\le q\) otherwise. Using (1),
\[
\operatorname{tr}(A^m)
\le q^{m-2}\operatorname{tr}(A^2)
\le pq^{m-1}.
\]
Equation (3) now yields the desired cycle inequality.

### 4.4 Existence and bounds for the unique eigenvalue above \(q\)

Suppose \(A\) has an eigenvalue above \(q\). There cannot be two such eigenvalues, because (1) would imply
\[
2q^2<\operatorname{tr}(A^2)\le pq=q(1-q),
\]
contrary to \(q>1/3\). Denote the unique eigenvalue above \(q\) by \(\alpha\), and take a unit eigenfunction \(\phi\perp\mathbf1\).

From (1), the sum of the squares of all other eigenvalues is at most
\[
L^2:=pq-\alpha^2.
\]
Therefore every other eigenvalue lies in \([-L,L]\). Moreover,
\[
L^2<pq-q^2=q(1-2q)<q^2,
\]
so \(L<q<\alpha\).

Let
\[
a=\int|\phi|.
\]
Since \(\int\phi_+=\int\phi_-=a/2\) and \(0\le U\le1\),
\[
\alpha=\langle\phi,T_U\phi\rangle
\le \langle\phi_+,T_U\phi_+\rangle+
\langle\phi_-,T_U\phi_-\rangle
\le\frac{a^2}{2}.
\]
Hence
\[
a^2\ge2\alpha.
\tag{4}
\]

Write \(|\phi|=a\mathbf1+h\) with \(h\perp\mathbf1\). Positivity of \(U\) gives
\[
\langle|\phi|,T_U|\phi|\rangle\ge
\langle\phi,T_U\phi\rangle=\alpha.
\]
Because \(\alpha=\lambda_{\max}(A)\),
\[
\alpha
\le qa^2+2a\langle g,h\rangle+\alpha(1-a^2)
\le qa^2+2a\lVert g\rVert_2\sqrt{1-a^2}+alpha(1-a^2).
\]
Thus \(a^2<1\) and
\[
\lVert g\rVert_2^2
\ge\frac{(\alpha-q)^2a^2}{4(1-a^2)}
\ge\frac{\alpha(\alpha-q)^2}{2(1-2\alpha)},
\tag{5}
\]
where (4) and the monotonicity of \(t/(1-t)\) were used.

Combining (5) with \(\alpha^2+2\lVert g\rVert_2^2\le pq\) and multiplying by \(1-2\alpha>0\) yields
\[
(1-\alpha-q)(\alpha^2+q\alpha-q)\le0.
\]
Since \(\alpha+q<1\),
\[
\alpha^2+q\alpha-q\le0,
\qquad
\alpha\le\frac{\sqrt{q^2+4q}-q}{2}<\frac12.
\tag{6}
\]

### 4.5 Lower bound involving \(c=\langle g,\phi\rangle\)

Decompose
\[
g=c\phi+g_0,\qquad g_0\perp\phi.
\]
For odd \(m\), define \(k_m,A_m,B_m,R_m\) as in Section 3. Since \(k_m\) is decreasing on \([0,p)\), and since
\(k_m(\lambda)\ge k_m(L)\) for \(-L\le\lambda\le L\), spectral expansion of \(u\) gives
\[
m[z^m]F(z)
\ge m[z^m]u(z)
\ge mk_m(\alpha)c^2+mk_m(L)\lVert g_0\rVert_2^2.
\tag{7}
\]

The non-\(\alpha\) part of the spectrum has squared mass at most
\(L^2-2\lVert g\rVert_2^2\). Since a negative eigenvalue contributes a nonpositive number to the trace of an odd power,
\[
\operatorname{tr}(A^m)
\le\alpha^m+L^m-2L^{m-2}
\left(c^2+\lVert g_0\rVert_2^2\right).
\tag{8}
\]
Combining (3), (7), and (8) yields
\[
t(C_m,W)-p^m+pq^{m-1}
\ge -R_m+A_mc^2+B_m\lVert g_0\rVert_2^2.
\tag{9}
\]

### 4.6 Two eigenfunction inequalities

Define
\[
z=\left(\int|\phi|\right)^2,
\qquad b=\langle|\phi|,\phi\rangle,
\]
choosing the sign of \(\phi\) so that \(b\ge0\), and put
\[
k=|\phi|-\sqrt z\,\mathbf1-b\phi,
\qquad K=\lVert k\rVert_2^2.
\]
Then
\[
z+b^2+K=1,qquad z\ge2\alpha.
\]
Let
\[
h=z-2\alpha,qquad e=1-2\alpha,qquad
d=\alpha-q,qquad f=\alpha-L.
\]

First, \(T_U\phi=c\mathbf1+\alpha\phi\), while pointwise
\[
T_U\phi\le T_U\phi_+\le\int\phi_+=\frac{\sqrt z}{2}.
\]
Taking the inner product with \(\phi_+\) gives
\[
c\le\frac{h-2\alpha b}{2\sqrt z}.
\tag{10}
\]

Second, positivity of \(U\) gives
\[
\langle|\phi|,T_U|\phi|\rangle\ge\alpha.
\]
Using \(\langle k,Ak\rangle\le LK\), one obtains
\[
bc+\langle g_0,k\rangle
\ge H:=\frac{dz+fK}{2\sqrt z}.
\tag{11}
\]
For \(K>0\), Cauchy--Schwarz therefore implies
\[
\lVert g_0\rVert_2^2\ge\frac{(H-bc)_+^2}{K}.
\tag{12}
\]

### 4.7 Reduction of (9) to a one-variable convex minimisation

If the right-hand side of (10) is nonpositive, then \(c\le0\) and (11)--(12) give
\[
B_m\lVert g_0\rVert_2^2
\ge B_m\frac{H^2}{K}
\ge B_mdf.
\]
This is at least \(C_m\psi(\xi,\rho)\), because choosing \(v=0\) in the definition of \(\psi\) gives
\(\psi\le\xi\), and
\[
C_m\xi=B_mfd\sqrt{2\alpha}\le B_mfd.
\]

Suppose now that the right-hand side of (10) is positive. Replacing a negative \(c\) by zero cannot increase
\(A_mc^2+B_m(H-bc)_+^2/K\), so take \(c\ge0\). From (10), \(z\ge2\alpha\), and \(h=e-b^2-K\),
\[
b^2+2\alpha b+2c\sqrt{2\alpha}\le e.
\tag{13}
\]
Thus
\[
0\le c\le\frac{e}{2\sqrt{2\alpha}},
\qquad
b\le\sqrt{\alpha^2+e-2c\sqrt{2\alpha}}-\alpha
\le\frac{e-2c\sqrt{2\alpha}}{2\alpha}.
\tag{14}
\]
Also (11), \(z\ge2\alpha\), and \(z\le1\) imply
\[
H\ge\frac{d\sqrt{2\alpha}}2+\frac{fK}{2}.
\]
For every real \(w\) and \(K>0\),
\[
\frac{(w+fK/2)_+^2}{K}\ge2f(w)_+.
\tag{15}
\]
Indeed, if \(w\le0\) the claim is trivial; if \(w>0\), it is the arithmetic--geometric mean inequality, with equality at \(K=2w/f\).

Using (12), (14), and (15),
\[
A_mc^2+B_m\lVert g_0\rVert_2^2
\ge
A_mc^2+2B_mf
\left(\frac{d\sqrt{2\alpha}}2-c\beta(c)\right)_+,
\]
where
\[
\beta(c)=\sqrt{\alpha^2+e-2c\sqrt{2\alpha}}-\alpha.
\]
Set
\[
v=\frac{2c\sqrt{2\alpha}}e\in[0,1].
\]
Then (14) gives
\[
c\beta(c)\le\frac{e^2v(1-v)}{4\alpha\sqrt{2\alpha}},
\]
and direct substitution gives
\[
A_mc^2=C_m\rho v^2,
\]
\[
2B_mf
\left(\frac{d\sqrt{2\alpha}}2-c\beta(c)\right)_+
\ge C_m(\xi-v+v^2)_+.
\]
Minimising over \(v\in[0,1]\) proves
\[
A_mc^2+B_m\lVert g_0\rVert_2^2
\ge C_m\psi(\xi,\rho).
\tag{16}
\]

When \(K=0\), (11) gives \(bc\ge d\sqrt z/2>0\), so \(c>0\). Inequality (13) still applies. With the same substitution, it implies \(\xi\le v-v^2\), hence the positive-part term vanishes and
\(A_mc^2=C_m\rho v^2\ge C_m\psi\). Thus (16) also holds in the degenerate case.

Combining (9) and (16) proves the clean reduction stated in Section 3.

## 5. Explicit evaluation of \(\psi\)

For \(\rho>0\), \(\xi\ge0\), define
\[
\xi_c(\rho)=\frac{2\rho+1}{4(\rho+1)^2},
\qquad
v_-(\xi)=\frac{1-\sqrt{1-4\xi}}2
\quad(0\le\xi\le1/4).
\]
Splitting according to the sign of \(\xi-v+v^2\) gives
\[
\psi(\xi,\rho)=
\begin{cases}
\rho v_-(\xi)^2,&0\le\xi<\xi_c(\rho),\\[3pt]
\displaystyle \xi-\frac1{4(1+\rho)},&\xi\ge\xi_c(\rho).
\end{cases}
\tag{17}
\]
Equivalently, since \(t_+=\max_{0\le\lambda\le1}\lambda t\), convex minimax gives
\[
\psi(\xi,\rho)
=\max_{0\le\lambda\le1}
\left(\lambda\xi-\frac{\lambda^2}{4(\rho+\lambda)}\right).
\tag{18}
\]
The minimiser in \(v\) for fixed \(\lambda\) is
\(v=\lambda/[2(\rho+\lambda)]\in[0,1]\).

Two useful lower bounds follow by choosing a value of \(\lambda\):
\[
C_m\psi\ge
C_m\left(\xi-\frac1{4(1+\rho)}\right)
\qquad(\lambda=1),
\tag{19}
\]
and, when \(2\rho\xi\le1\),
\[
C_m\psi\ge
C_m\rho\xi^2\frac{1+4\xi}{1+2\xi}
\qquad(\lambda=2\rho\xi).
\tag{20}
\]

No special name for \(\psi\), (19), or (20) is required.

## 6. Status of the remaining scalar inequality

The change of variables used in the PDF is valid. Put
\[
e=1-2\alpha,qquad \kappa=\frac{\alpha-q}{e}.
\]
Then
\[
\alpha=\frac{1-e}{2},\qquad
q=\alpha-\kappa e,qquad
p=\alpha+(1+\kappa)e,
\]
and the admissible set is
\[
0<e<\frac13,qquad
0<\kappa\le\frac{1-e}{1+e},qquad
\kappa<\frac{1-3e}{6e}.
\tag{21}
\]
Moreover
\[
L^2=\alpha e-d(d+e),qquad
\xi=\frac{(1-e)^2\kappa}{e}.
\tag{22}
\]

The PDF divides (21) into the following three ordinary cases:

1. \(e\le1/60\) and \(\xi\ge1\). The PDF gives an analytic proof using (19).
2. \(e\ge1/60\) and \(\xi\ge1\). After a valid one-variable maximisation in \(m\), the proof reduces to Lemma 5.3. The finite interval certificate is absent.
3. \(\xi\le1\). The range \(e\le1/60\) is treated analytically. The range
   \(1/60\le e\le1/3-1/1000\) is delegated to the absent certificate in Lemma 6.3. The remaining range \(1/3-1/1000<e<1/3\) is treated analytically.

Hence the uncovered proof obligations are precisely:

### Obligation B

Prove the explicit two-variable inequality (34) of the PDF on
\[
\frac1{60}\le e\le\frac{2033}{10000},qquad
\frac{e}{(1-e)^2}\le\kappa\le
\min\left\{\frac{1-e}{1+e},\frac{1-3e}{6e}\right\}.
\]

### Obligation C

Prove the scalar comparison described after Lemma 6.4 on
\[
\frac1{60}\le e\le\frac13-\frac1{1000},qquad
0<\kappa\le
\min\left\{rac{e}{(1-e)^2},
\frac{1-e}{1+e},
\frac{1-3e}{6e}\right\}.
\]

The prose in Section 8 is not enough to prove either obligation: it supplies neither the rational rectangles nor their verified inequalities. In proof-assistant terms, these are two missing terms of the required proposition types.

## 7. Lean formalisation blueprint

### 7.1 Recommended separation into layers

The formalisation should be divided into four layers.

| Layer | Content | Dependence on missing data |
|---|---|---|
| I | rational and real scalar inequalities; formula for \(\psi\) | only the two finite certificates are missing |
| II | finite-dimensional symmetric matrices and truncated formal power series | none |
| III | step graphons and approximation in \(L^2\) | none in principle |
| IV | assembly with previously proved density and small-cycle cases | earlier external theorems are required |

Formalise Layer I first. It tests the central claim without the much larger measure-theoretic infrastructure.

### 7.2 Core scalar structure

The following is indicative Lean-style pseudocode, not code expected to compile without adapting names to the installed Mathlib version.

```lean
structure ScalarData where
  q α : ℝ
  m : ℕ
  hq0 : 1 / 3 < q
  hq1 : q < 1 / 2
  hαq : q < α
  hαhalf : α < 1 / 2
  hquad : α ^ 2 + q * α ≤ q
  hm : 15 ≤ m
  hmodd : Odd m

namespace ScalarData

noncomputable def p (D : ScalarData) : ℝ := 1 - D.q
noncomputable def L (D : ScalarData) : ℝ := Real.sqrt (D.p * D.q - D.α ^ 2)
noncomputable def d (D : ScalarData) : ℝ := D.α - D.q
noncomputable def e (D : ScalarData) : ℝ := 1 - 2 * D.α
noncomputable def f (D : ScalarData) : ℝ := D.α - D.L

noncomputable def k (D : ScalarData) (x : ℝ) : ℝ :=
  (D.p ^ (D.m - 1) - x ^ (D.m - 1)) / (D.p + x)

noncomputable def AA (D : ScalarData) : ℝ :=
  2 * D.L ^ (D.m - 2) + D.m * D.k D.α

noncomputable def BB (D : ScalarData) : ℝ :=
  2 * D.L ^ (D.m - 2) + D.m * D.k D.L

noncomputable def R (D : ScalarData) : ℝ :=
  D.α ^ D.m + D.L ^ D.m - D.p * D.q ^ (D.m - 1)
```

Avoid natural-number coercion ambiguity by writing `(D.m : ℝ)` in compiled code. Prove the following sign lemmas immediately:

```lean
lemma p_pos (D) : 0 < D.p := ...
lemma e_pos (D) : 0 < D.e := ...
lemma radicand_nonneg (D) : 0 ≤ D.p * D.q - D.α^2 := ...
lemma L_nonneg (D) : 0 ≤ D.L := Real.sqrt_nonneg _
lemma L_lt_q (D) : D.L < D.q := ...
lemma f_pos (D) : 0 < D.f := sub_pos.mpr (lt_trans (D.L_lt_q) D.hαq)
lemma AA_pos (D) : 0 < D.AA := ...
lemma BB_pos (D) : 0 < D.BB := ...
```

These lemmas should be used before every division or order-preserving multiplication. This eliminates many hidden side conditions present in a handwritten proof.

### 7.3 Formalising \(\psi\)

Define

```lean
noncomputable def objective (ξ ρ v : ℝ) : ℝ :=
  ρ * v^2 + max (ξ - v + v^2) 0

noncomputable def psi (ξ ρ : ℝ) : ℝ :=
  sInf (objective ξ ρ '' Set.Icc (0 : ℝ) 1)
```

Alternatively, define \(\psi\) directly by the piecewise formula (17), then prove it equals the minimum. The latter is easier if only the final inequality is needed. Required lemmas are:

```lean
lemma psi_eq_min ... :
  psi ξ ρ = min' (Set.Icc (0 : ℝ) 1) ... := ...

lemma psi_piecewise (hρ : 0 < ρ) (hξ : 0 ≤ ξ) : ... := ...

lemma psi_dual_lower
    (hρ : 0 < ρ) (hλ0 : 0 ≤ λ) (hλ1 : λ ≤ 1) :
  λ * ξ - λ^2 / (4 * (ρ + λ)) ≤ psi ξ ρ := ...
```

For the last lemma, one does not need a general minimax theorem. Complete the square pointwise:
\[
\rho v^2+(\xi-v+v^2)_+
\ge (\rho+\lambda)v^2-\lambda v+\lambda\xi
\ge\lambda\xi-\frac{\lambda^2}{4(\rho+\lambda)}.
\]
This route is shorter and more robust in Lean.

### 7.4 Finite-dimensional spectral layer

First use a finite real inner-product space. Represent the compressed operator by a self-adjoint linear map, not by an arbitrary matrix. Formalise:

1. the block operator relative to \(\mathbb R\oplus H\);
2. the trace identity for powers;
3. the eigenvalue decomposition of a self-adjoint operator;
4. inequalities (7)--(9).

The determinant/logarithm argument should use `PowerSeries` truncated at degree \(m\). A possible theorem interface is:

```lean
theorem trace_block_power
    (A : H →ₗ[ℝ] H) (hA : IsSelfAdjoint A)
    (g : H) (p : ℝ) (m : ℕ) :
  LinearMap.trace ℝ H' (M ^ m)
    = p^m - LinearMap.trace ℝ H (A ^ m)
      + m * coeff m (FormalMultilinearRemainder p A g) := ...
```

The exact Mathlib trace API may dictate a matrix formulation instead. In that event, diagonalise the symmetric matrix and prove the bounds in coordinates.

### 7.5 Passage from step graphons to graphons

For a dyadic sigma-algebra \(\mathcal F_n\), let
\[
U_n=\mathbb E[U\mid\mathcal F_n\otimes\mathcal F_n].
\]
Prove:

```lean
lemma condexp_graphon_bounds : 0 ≤ Uₙ ∧ Uₙ ≤ 1 := ...
lemma condexp_graphon_symm : Symmetric Uₙ := ...
lemma condexp_L2_tendsto : Tendsto Uₙ atTop (𝓝 U) in Lp := ...
lemma cycleDensity_continuous_fixed_m : ... := ...
lemma integralOperator_HS_tendsto : ... := ...
lemma trace_power_continuous_of_HS (hm : 2 ≤ m) : ... := ...
```

The cycle-density continuity estimate can be proved by telescoping the product over the \(m\) edges and applying Cauchy--Schwarz to each term; boundedness by one controls the remaining factors.

### 7.6 Eigenfunction geometry layer

Once the compact self-adjoint spectral theorem is available, package the data as:

```lean
structure ExceptionalEigenData where
  α : ℝ
  φ : Lp ℝ 2 μ
  norm_φ : ‖φ‖ = 1
  orth_one : inner φ 1 = 0
  eigen : A φ = α • φ
  hα : q < α
```

Then prove, in order:

1. uniqueness of \(\alpha>q\) from the sum-of-squares bound;
2. \(L<q<\alpha<1/2\);
3. (4)--(6);
4. the decomposition of \(|\phi|\) into the orthogonal components \(\mathbf1,\phi,k\);
5. (10) and (11);
6. the scalar minimisation leading to (16).

Avoid pointwise representatives wherever possible. The inequality
\(T_U\phi_+\le\int\phi_+\) is an almost-everywhere statement and should be transported into an `AEEqFun` inequality before integration.

### 7.7 Encoding the missing finite certificates

A trustworthy certificate should consist of:

```lean
structure RatBox where
  eLo eHi kLo kHi : ℚ
  he : eLo ≤ eHi
  hk : kLo ≤ kHi

structure BoxCertificate where
  box : RatBox
  tag : CertificateRule
  auxBounds : List RationalBound
```

The trusted Lean kernel should prove a theorem of the form

```lean
theorem check_box_sound
    (cert : BoxCertificate)
    (hcheck : checkBox cert = true) :
    ∀ e κ : ℝ,
      inBox cert.box e κ → admissible e κ → targetInequality e κ := ...
```

Then the externally generated data are merely a list:

```lean
def certificateB : List BoxCertificate := [...]
def certificateC : List BoxCertificate := [...]
```

and completeness is checked inside Lean:

```lean
theorem certificateB_covers :
  ∀ e κ, domainB e κ → ∃ c ∈ certificateB, inBox c.box e κ := by native_decide

theorem all_certificateB_valid :
  ∀ c ∈ certificateB, checkBox c = true := by native_decide
```

The exponential bounds must be accompanied by proved rational inequalities. For \(t\ge0\), an upper bound can use
\[
e^{-t}\le\left(\sum_{j=0}^N\frac{t^j}{j!}\right)^{-1}.
\]
Square-root bounds can use integers \(a,b,S>0\) satisfying
\[
a^2\le tS^2\le b^2,
\qquad
\frac aS\le\sqrt t\le\frac bS.
\]
All interval monotonicity rules must be theorems, not comments in the generator.

The absent Python programs alone would still not be the ideal Lean certificate. What is needed is their complete box data plus a small verified checker.

### 7.8 Final theorem dependency

After obligations B and C have been certified, the Region-II theorem has the following short logical form:

```lean
theorem regionII
    (W : Graphon) (hp0 : 1/2 < edgeDensity W)
    (hp1 : edgeDensity W < 2/3)
    (hm : 15 ≤ m) (hodd : Odd m) :
    cycleDensity m W ≥
      edgeDensity W ^ m
        - edgeDensity W * (1 - edgeDensity W) ^ (m - 1) := by
  by_cases h : spectralMax (compression W) ≤ 1 - edgeDensity W
  · exact noExceptionalEigenvalue_case W h hm hodd
  · obtain ⟨D, hD⟩ := construct_scalar_data W h
    calc
      cycleDensity m W - ...
          ≥ -D.R + D.C * psi D.ξ D.ρ := operator_reduction W D hD
      _ ≥ 0 := by linarith [scalar_inequality D]
```

The cases \(m\le13\) and \(p\ge2/3\) must be imported as separately proved theorems. They are not consequences of the supplied PDF.

## 8. Required material before the paper can be certified as correct

The following items are necessary and sufficient to continue the audit to a genuine acceptance proof:

1. `zoneB_certifier.py` exactly as executed;
2. `zoneC_certifier.py` exactly as executed;
3. the complete generated certificate data, preferably the rational box endpoints and all auxiliary rational bounds;
4. a reproducible command and the interpreter/dependency versions;
5. the “earlier consolidated note” containing the \(m\le13\) and \(p\ge2/3\) proofs;
6. ideally, hashes of all inputs and outputs.

Without items 1--3, Theorem 1.1 remains unproved in the supplied article. Without item 5, Corollaries 1.2 and 1.3 remain unproved even if Theorem 1.1 is accepted.

## 9. Bottom line

The unusual terminology can be removed completely without changing the mathematics. The central conceptual contribution is a valid-looking reduction from a graphon inequality to the scalar inequality (S). The PDF does not, however, contain a complete proof of (S), because two finite exact certificates are only described and not supplied. A Lean development should therefore formalise the operator reduction and the scalar checker separately, and it must treat the two missing certificate datasets and the earlier external theorems as explicit outstanding dependencies rather than assumptions hidden in prose.
