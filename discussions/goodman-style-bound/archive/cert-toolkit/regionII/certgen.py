# -*- coding: utf-8 -*-
"""Exact Gram -> SOS certificate generator (univariate Hankel form).

Given a symmetric Gram matrix N(q) (polynomial entries) for a moment form
  L = sum_{i,j} N[i,j] * s_{i+j}    (basis lambda^0..lambda^{n-1}, ascending)
produce an exact identity
  C(q) * L = sum_k p_k(q) * SOS(v_k)
with C, p_k polynomials having all-nonneg coefficients in y = rho - q, and v_k
integer/poly coefficient vectors, where
  SOS(v) = sum_{i,j} v_i v_j s_{i+j}.
Verify the identity exactly in sympy.
"""
import sympy as sp

q = sp.symbols("q")

def schur_sos(N, n):
    """Return list of (coeff_k (rational fn of q), intvec_k (list of polys)) with
    sum_k coeff_k * SOS(intvec_k) == sum_{i,j} N[i,j] s_{i+j}, exactly.
    Elimination order: index 0 first (so leading basis element eliminated first)."""
    R = [[sp.nsimplify(N[i][j]) for j in range(n)] for i in range(n)]
    terms = []
    for k in range(n):
        piv = sp.cancel(R[k][k])
        if piv == 0:
            continue
        # w_k vector over basis: e_k + sum_{j>k} R[k][j]/piv e_j
        w = [sp.Integer(0)] * n
        w[k] = sp.Integer(1)
        for j in range(k + 1, n):
            w[j] = sp.cancel(R[k][j] / piv)
        # clear denominators
        b = sp.Integer(1)
        for wj in w:
            d = sp.fraction(sp.cancel(wj))[1]
            b = sp.lcm(b, d)
        b = sp.expand(b)
        intvec = [sp.expand(sp.cancel(wj * b)) for wj in w]
        coeff = sp.cancel(piv / b**2)
        terms.append((coeff, intvec))
        # Schur complement update for i,j>k
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                R[i][j] = sp.cancel(R[i][j] - R[k][i] * R[k][j] / piv)
    return terms

def make_cert(N, n, rho, name):
    # L coefficients on moments
    terms = schur_sos(N, n)
    # common denominator C
    C = sp.Integer(1)
    for c, _ in terms:
        d = sp.fraction(c)[1]
        C = sp.lcm(C, d)
    C = sp.expand(C)
    pks = [sp.expand(sp.cancel(C * c)) for c, _ in terms]
    intvecs = [iv for _, iv in terms]
    # Verify: C * sum_{ij} N s_{i+j} == sum_k p_k SOS(intvec_k)
    s = sp.symbols("s0:40")
    L = sum(N[i][j] * s[i + j] for i in range(n) for j in range(n))
    lhs = sp.expand(C * L)
    rhs = 0
    for pk, iv in zip(pks, intvecs):
        sosv = sum(iv[i] * iv[j] * s[i + j] for i in range(n) for j in range(n))
        rhs += pk * sosv
    rhs = sp.expand(rhs)
    ok = sp.expand(lhs - rhs) == 0
    Cpos = bernstein_pos(C, rho)
    pkpos = [bernstein_pos(pk, rho) for pk in pks]
    print(f"[{name}] identity OK: {ok} ; C pos-on-[0,rho]: {Cpos} ; p_k pos: {pkpos}")
    print(f"   deg C = {sp.degree(C, q)}, deg p_k = {[sp.degree(pk,q) for pk in pks]}")
    return C, pks, intvecs, ok and Cpos and all(pkpos)


def bernstein_pos(poly, rho, max_elev=40):
    """True if poly>0 on [0,rho], certified by all-positive Bernstein coeffs on [0,rho]
    after enough degree elevation. Returns (ok). Also a necessary numeric check."""
    poly = sp.expand(poly)
    if poly == 0:
        return False
    # quick numeric check
    import numpy as np
    f = sp.lambdify(q, poly, "numpy")
    xs = np.linspace(0, float(rho), 500)
    if np.min(f(xs)) <= 0:
        return False
    # Bernstein on [0,rho]: write poly(q) = sum_k c_k C(n,k) (q/rho)^k (1-q/rho)^{n-k}
    d = sp.degree(poly, q)
    for n in range(d, max_elev + 1):
        # bernstein coeffs via evaluating the linear map; use the formula
        # c_k = sum_{i=0}^{k} ... easier: substitute q = rho*u, expand in u, convert mono->bernstein
        u = sp.symbols("u")
        pu = sp.expand(poly.subs(q, rho * u))
        Pu = sp.Poly(pu, u)
        # elevate to degree n: multiply by (u+(1-u))^{n-d} = 1, but represent in degree n
        # monomial u^i -> bernstein: u^i = sum_{k>=i} [C(k,i)/C(n,i)] B_{k,n}(u)
        coeffs_mono = [Pu.coeff_monomial(u**i) for i in range(d + 1)]
        bern = [sp.Integer(0)] * (n + 1)
        for i in range(d + 1):
            ci = coeffs_mono[i]
            if ci == 0:
                continue
            for k in range(i, n + 1):
                bern[k] += ci * sp.binomial(k, i) / sp.binomial(n, i)
        if all(b >= 0 for b in bern):
            return True
    return False


# ---- TEST on C9 linear Gram (known-good) ----
def test_c9():
    # From check_c9_linear_gram, basis z=(lam^3,lam^2,lam,1) i.e. descending.
    # Our convention: ascending basis lam^0..lam^3 -> reverse the matrix.
    Nd = sp.Matrix([
        [8, 8*q-sp.Rational(9,2), sp.Rational(17,250), -sp.Rational(71,500)],
        [8*q-sp.Rational(9,2), 24*q**2-27*q+9-sp.Rational(34,250),
         (32*q**3-54*q**2+36*q-9)/2+sp.Rational(71,500), -sp.Rational(3,50)],
        [sp.Rational(17,250), (32*q**3-54*q**2+36*q-9)/2+sp.Rational(71,500),
         40*q**4-90*q**3+90*q**2-45*q+9+sp.Rational(3,25),
         sp.Rational(3,2)*(16*q**5-45*q**4+60*q**3-45*q**2+18*q-3)],
        [-sp.Rational(71,500), -sp.Rational(3,50),
         sp.Rational(3,2)*(16*q**5-45*q**4+60*q**3-45*q**2+18*q-3),
         56*q**6-189*q**5+315*q**4-315*q**3+189*q**2-63*q+9]
    ])
    # descending basis (lam^3..lam^0); moment index of z_i*z_j with z ordered desc deg (3,2,1,0):
    # entry (i,j) multiplies lam^{(3-i)+(3-j)} = s_{6-i-j}. To use ascending SOS convention,
    # reverse order so basis is lam^0..lam^3.
    n = 4
    Nrev = [[Nd[n-1-i, n-1-j] for j in range(n)] for i in range(n)]
    make_cert(Nrev, n, sp.Rational(997,2000), "C9-linear")

if __name__ == "__main__":
    test_c9()
