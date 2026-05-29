"""
Exact-arithmetic checker for odd_cycle_graphon_bound_verified_note.tex.

This script verifies the polynomial identities and rational PSD certificates used in
that note. It uses SymPy and performs exact computations over QQ[q,lambda].
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import combinations
import sympy as sp


def assert_zero(expr, name: str) -> None:
    if sp.simplify(expr) != 0:
        raise AssertionError(f"{name} failed: expression is not zero: {sp.factor(expr)}")
    print(f"OK: {name}")


def assert_positive_coeffs(poly, var, name: str) -> None:
    P = sp.Poly(sp.together(poly).as_numer_denom()[0], var)
    coeffs = P.all_coeffs()
    bad = [c for c in coeffs if c <= 0]
    if bad:
        raise AssertionError(f"{name} failed: nonpositive coefficients {bad}")
    print(f"OK: {name} has {len(coeffs)} positive coefficients")


def path_components(n: int, subset) -> tuple[int, ...]:
    adj = [set() for _ in range(n)]
    for i in subset:
        u, v = i, (i + 1) % n
        adj[u].add(v)
        adj[v].add(u)
    seen = set()
    comps = []
    for v in range(n):
        if adj[v] and v not in seen:
            stack = [v]
            seen.add(v)
            edges_twice = 0
            while stack:
                a = stack.pop()
                edges_twice += len(adj[a])
                for b in adj[a]:
                    if b not in seen:
                        seen.add(b)
                        stack.append(b)
            comps.append(edges_twice // 2)
    return tuple(sorted(comps, reverse=True))


def cycle_forest_counts(n: int):
    return {r: Counter(path_components(n, s) for s in combinations(range(n), r)) for r in range(n + 1)}


def check_counts() -> None:
    expected_5 = {
        0: {(): 1},
        1: {(1,): 5},
        2: {(2,): 5, (1, 1): 5},
        3: {(3,): 5, (2, 1): 5},
        4: {(4,): 5},
        5: {(5,): 1},
    }
    expected_7 = {
        0: {(): 1},
        1: {(1,): 7},
        2: {(1, 1): 14, (2,): 7},
        3: {(2, 1): 21, (3,): 7, (1, 1, 1): 7},
        4: {(3, 1): 14, (4,): 7, (2, 2): 7, (2, 1, 1): 7},
        5: {(5,): 7, (4, 1): 7, (3, 2): 7},
        6: {(6,): 7},
        7: {(7,): 1},
    }
    for n, expected in [(5, expected_5), (7, expected_7)]:
        actual = cycle_forest_counts(n)
        for r, cnt in expected.items():
            if Counter(cnt) != actual[r]:
                raise AssertionError(f"C_{n} counts fail at r={r}: {actual[r]} vs {cnt}")
        print(f"OK: C_{n} inclusion-exclusion counts")
    # For C9 we only check total counts sum to binomial and print the count table.
    actual_9 = cycle_forest_counts(9)
    for r, cnt in actual_9.items():
        if sum(cnt.values()) != sp.binomial(9, r):
            raise AssertionError(f"C_9 count total fail at r={r}")
    print("OK: C_9 inclusion-exclusion counts sum correctly")


def path_formulae(max_n=8):
    q = sp.symbols("q")
    s = sp.symbols("s0:20")
    a = sp.Integer(1)
    h = defaultdict(lambda: sp.Integer(0))  # h = sum_p h[p] A^p g
    xs = {0: a}
    for n in range(1, max_n + 1):
        inner = sum(c * s[p] for p, c in h.items())
        a_new = sp.expand(q * a + inner)
        h_new = defaultdict(lambda: sp.Integer(0))
        h_new[0] += a
        for p, c in h.items():
            h_new[p + 1] += c
        a, h = a_new, h_new
        xs[n] = a
    return q, s, xs


def check_c7_square() -> None:
    q, lam = sp.symbols("q lam")
    P = (
        6 * lam**4
        + (12 * q - 7) * lam**3
        + (18 * q**2 - 21 * q + 7) * lam**2
        + (24 * q**3 - 42 * q**2 + 28 * q - 7) * lam
        + 30 * q**4 - 70 * q**3 + 70 * q**2 - 35 * q + 7
    )
    D = 288 * q**2 - 336 * q + 119
    C = 24 * q**3 - 42 * q**2 + 28 * q - 7
    N = 5184*q**6 - 18144*q**5 + 28602*q**4 - 25802*q**3 + 13874*q**2 - 4165*q + 539
    expr = 6 * (lam**2 + (q - sp.Rational(7, 12)) * lam) ** 2 + D / 24 * (lam + 12*C/D) ** 2 + N / D
    assert_zero(P - expr, "C7 quartic square decomposition")
    y = sp.symbols("y")
    assert_positive_coeffs(D.subs(q, sp.Rational(1, 2) - y), y, "C7 D(q)")
    assert_positive_coeffs(8 * N.subs(q, sp.Rational(1, 2) - y), y, "C7 8N(q)")


def check_c9_linear_gram() -> None:
    q, lam, y = sp.symbols("q lam y")
    P = (
        8*lam**6 + (16*q-9)*lam**5 + 3*(8*q**2-9*q+3)*lam**4
        + (32*q**3-54*q**2+36*q-9)*lam**3
        + (40*q**4-90*q**3+90*q**2-45*q+9)*lam**2
        + 3*(16*q**5-45*q**4+60*q**3-45*q**2+18*q-3)*lam
        + 56*q**6-189*q**5+315*q**4-315*q**3+189*q**2-63*q+9
    )
    N = sp.Matrix([
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
    z = sp.Matrix([lam**3, lam**2, lam, 1])
    assert_zero(P - (z.T * N * z)[0], "C9 P_q Gram identity")
    rho = sp.Rational(997, 2000)
    for i in range(1, 5):
        minor = sp.factor(N[:i, :i].det().subs(q, rho - y))
        assert_positive_coeffs(minor, y, f"C9 N_q leading minor {i}")


def check_c9_phi_decomposition() -> None:
    q, s, x = path_formulae(8)
    s0, s1, s2, s3, s4, s5, s6 = s[:7]
    Phi = (
        8*x[8] - 9*x[7] + 9*x[6] - 9*x[5] + 9*x[4] - 9*x[3] + 9*x[2]
        - 9*q*x[6] + 18*q*x[5] - 27*q*x[4] + 36*q*x[3] - 45*q*x[2]
        - 9*q**2 + 54*q**2*x[2] - 27*q**2*x[3] + 9*q**2*x[4]
        + 54*q**3 - 9*q**3*x[2] - 117*q**4 + 126*q**5 - 84*q**6 + 36*q**7 - 8*q**8
        + 3*x[2]**3 + 18*x[2]**2 - 27*q*x[2]**2
        - 27*x[2]*x[3] + 18*q*x[2]*x[3] + 18*x[2]*x[4] - 9*x[2]*x[5]
        + 9*x[3]**2 - 9*x[3]*x[4]
    )
    Phi = sp.expand(Phi)
    H = (
        8*s0**4 + 10*(8*q**2-9*q+3)*s0**3 + 6*(16*q-9)*s0**2*s1
        + 24*s0**2*s2 + 24*s0*s1**2
    )
    # Extract total degree >=3 in s variables and compare with H.
    poly = sp.Poly(Phi, *s[:7])
    high = 0
    for monom, coeff in poly.terms():
        if sum(monom) >= 3:
            high += coeff * sp.prod(var**pow_ for var, pow_ in zip(s[:7], monom))
    assert_zero(sp.expand(high - H), "C9 high-degree H extraction")
    print("OK: C9 Phi_9 decomposition high-degree part")



def expression_from_counts(n: int, q, xs, replace_cycle_by_path: bool = True):
    """Inclusion-exclusion lower expression for t(C_n,1-U) with c_n <= x_{n-1}."""
    counts = cycle_forest_counts(n)
    def term(comp):
        out = sp.Integer(1)
        for a in comp:
            out *= q if a == 1 else xs[a]
        return out
    E = sp.Integer(1)
    for r in range(1, n):
        for comp, c in counts[r].items():
            E += (-1)**r * c * term(comp)
    if replace_cycle_by_path:
        E -= xs[n-1]  # replace the final -c_n by -x_{n-1}
    return sp.expand(E)


def check_c5_c7_defects() -> None:
    q, s, xs = path_formulae(8)
    s0, s1, s2, s3, s4, s5, s6 = s[:7]
    # C5 lower expansion from counts, target, and square certificate.
    E5 = expression_from_counts(5, q, xs)
    target5 = (1-q)**5 - (1-q)*q**4
    Phi5 = sp.expand(E5 - target5)
    expected5 = 4*xs[4] - 5*xs[3] + 5*(1-q)*xs[2] - (4*q**4 - 10*q**3 + 5*q**2)
    assert_zero(Phi5 - expected5, "C5 path-defect formula from counts")
    # In A-moment notation, ||Tg||^2 = s0^2+s2 and <g,Tg>=s1.
    moment5 = 4*(s0**2+s2) + (8*q-5)*s1 + (12*q**2-15*q+5)*s0
    assert_zero(sp.expand(Phi5 - moment5), "C5 moment-defect formula")

    # C7 lower expansion from counts and target.
    E7 = expression_from_counts(7, q, xs)
    target7 = (1-q)**7 - (1-q)*q**6
    Phi7 = sp.expand(E7 - target7)
    expected7_path = (
        6*xs[6] - 7*xs[5] + 7*(1-q)*xs[4] + 7*(2*q-1)*xs[3]
        + 7*(q**2-3*q+1)*xs[2] + 7*xs[2]**2 - 7*xs[2]*xs[3]
        - 6*q**6 + 21*q**5 - 35*q**4 + 28*q**3 - 7*q**2
    )
    assert_zero(Phi7 - expected7_path, "C7 path-defect formula from counts")
    expected7_mom = (
        6*s4+(12*q-7)*s3+(18*q**2-21*q+7)*s2
        +(24*q**3-42*q**2+28*q-7)*s1
        +(30*q**4-70*q**3+70*q**2-35*q+7)*s0
        +12*s0*s2+(36*q-21)*s0*s1
        +(36*q**2-42*q+14)*s0**2+6*s0**3+6*s1**2
    )
    assert_zero(sp.expand(Phi7 - expected7_mom), "C7 moment-defect formula")


def check_c9_formulae_more() -> None:
    q, s, xs = path_formulae(8)
    s0, s1, s2, s3, s4, s5, s6 = s[:7]
    E9 = expression_from_counts(9, q, xs)
    target9 = (1-q)**9 - (1-q)*q**8
    Phi_from_counts = sp.expand(E9 - target9)
    Phi_stated = (
        8*xs[8] - 9*xs[7] + 9*xs[6] - 9*xs[5] + 9*xs[4] - 9*xs[3] + 9*xs[2]
        - 9*q*xs[6] + 18*q*xs[5] - 27*q*xs[4] + 36*q*xs[3] - 45*q*xs[2]
        - 9*q**2 + 54*q**2*xs[2] - 27*q**2*xs[3] + 9*q**2*xs[4]
        + 54*q**3 - 9*q**3*xs[2] - 117*q**4 + 126*q**5 - 84*q**6 + 36*q**7 - 8*q**8
        + 3*xs[2]**3 + 18*xs[2]**2 - 27*q*xs[2]**2
        - 27*xs[2]*xs[3] + 18*q*xs[2]*xs[3] + 18*xs[2]*xs[4] - 9*xs[2]*xs[5]
        + 9*xs[3]**2 - 9*xs[3]*xs[4]
    )
    assert_zero(Phi_from_counts - Phi_stated, "C9 Phi_9 formula from counts")
    # Quadratic extraction equals F_q.
    poly = sp.Poly(sp.expand(Phi_stated), *s[:7])
    quadratic = 0
    for monom, coeff in poly.terms():
        if sum(monom) == 2:
            quadratic += coeff * sp.prod(var**pow_ for var, pow_ in zip(s[:7], monom))
    m1, m2, m3, m4 = sp.symbols("m1 m2 m3 m4")
    F = (
        (48*q**2-54*q+18)*m1**2 + (48*q-27)*m1*m2 + 16*m1*m3 + 8*m2**2
        +(160*q**3-270*q**2+180*q-45)*m1
        +(96*q**2-108*q+36)*m2+(48*q-27)*m3+16*m4
        +120*q**4-270*q**3+270*q**2-135*q+27
    )
    F_sub = s0**2 * F.subs({m1:s1/s0, m2:s2/s0, m3:s3/s0, m4:s4/s0})
    assert_zero(sp.expand(quadratic - F_sub), "C9 quadratic F_q extraction")
    # Kernel K and diagonal Gram M.
    lam, mu, u, v, y = sp.symbols("lam mu u v y")
    K = (
        (48*q**2-54*q+18)*lam*mu
        + (48*q-27)/2*(lam*mu**2 + lam**2*mu)
        + sp.Rational(16,2)*(lam*mu**3 + lam**3*mu)
        + 8*lam**2*mu**2
        + (160*q**3-270*q**2+180*q-45)/2*(lam+mu)
        + (96*q**2-108*q+36)/2*(lam**2+mu**2)
        + (48*q-27)/2*(lam**3+mu**3)
        + sp.Rational(16,2)*(lam**4+mu**4)
        + 120*q**4-270*q**3+270*q**2-135*q+27
    )
    # Check diagonal Gram representation M.
    Kdiag = sp.expand(K.subs(mu, lam))
    M = sp.Matrix([
        [40, 48*q-27, 0],
        [48*q-27, 144*q**2-162*q+54, (160*q**3-270*q**2+180*q-45)/2],
        [0, (160*q**3-270*q**2+180*q-45)/2, 120*q**4-270*q**3+270*q**2-135*q+27]
    ])
    zz = sp.Matrix([lam**2, lam, 1])
    assert_zero(Kdiag - (zz.T*M*zz)[0], "C9 quadratic diagonal Gram identity")
    yy = sp.symbols("yy")
    for i in range(1,4):
        minor = sp.factor(M[:i,:i].det().subs(q, sp.Rational(1,2)-yy))
        assert_positive_coeffs(minor, yy, f"C9 quadratic M_q leading minor {i}")


def main() -> None:
    check_counts()
    check_c5_c7_defects()
    check_c7_square()
    check_c9_linear_gram()
    check_c9_phi_decomposition()
    check_c9_formulae_more()
    print("All checks passed.")


if __name__ == "__main__":
    main()
