"""
Exact checker for the C13 inequality on the triangle-density extremal
complete tripartite graphons.

The triangle extremal graphon in the interval p in [1/2,2/3] has three
parts of sizes c, (1-c)/2, (1-c)/2 and all cross-edges present.  This
script verifies symbolically that

    t(C13,W) - (p^13 - p(1-p)^12) >= 0

for 0 <= c <= 1/3.  The final positivity check is by Bernstein
coefficients on [0,1/3].
"""
from __future__ import annotations
import sympy as sp

c, z = sp.symbols("c z")
b = (1 - c) / 2

# On the two-dimensional quotient, the complete tripartite graphon has
# matrix [[0, sqrt(2bc)], [sqrt(2bc), b]].  Its trace powers T_n satisfy
# T_0=2, T_1=b, T_n=b*T_{n-1}+2*b*c*T_{n-2}.  There is one additional
# internal eigenvalue -b.  Hence t(C_13)=T_13-b^13.
T = [sp.Integer(2), b]
for n in range(2, 14):
    T.append(sp.expand(b * T[-1] + 2 * b * c * T[-2]))

t_c13 = sp.expand(T[13] - b**13)
p = sp.expand(1 - (c**2 + 2 * b**2))
q = sp.expand(1 - p)
gap = sp.factor(t_c13 - (p**13 - p * q**12))

R = sp.factor(gap / (c * (1 - c) * (3*c - 1)**2 * (3*c + 1) / sp.Integer(2048)))
# The factor above is positive on 0<c<1/3.  R should be the degree-19 polynomial.
print("p(c)=", sp.factor(p))
print("q(c)=", sp.factor(q))
print("gap factorization=")
print(sp.factor(gap))
print("residual degree", sp.Poly(R, c).degree())

# Check R(c)>0 on [0,1/3] by Bernstein coefficients after c=z/3.
G = sp.expand(R.subs(c, z/3))
P = sp.Poly(G, z)
deg = P.degree()
coeff = {mon[0]: coef for mon, coef in P.terms()}
bernstein = []
for k in range(deg + 1):
    bk = sp.Rational(0)
    for i in range(k + 1):
        if i in coeff:
            bk += coeff[i] * sp.Rational(sp.binomial(k, i), sp.binomial(deg, i))
    bernstein.append(sp.factor(bk))

if not all(bk > 0 for bk in bernstein):
    raise AssertionError("A Bernstein coefficient is not positive")

print(f"All {deg+1} Bernstein coefficients of R(z/3) are positive.")
print("Minimum Bernstein coefficient:", min(bernstein))
print("C13 holds on the triangle-extremal complete tripartite family.")
