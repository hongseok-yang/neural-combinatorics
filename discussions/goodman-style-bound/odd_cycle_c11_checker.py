"""
Exact-arithmetic checker for the C11 working note.

The checker verifies the algebraic identities and the finite certificates used in
odd_cycle_c11_working_note.tex:
  * inclusion-exclusion formula for the crude C11 path certificate;
  * path-density moment recurrence up to P_10;
  * decomposition of the certificate into homogeneous moment pieces;
  * positivity of the linear piece on q in [0,97/200] and lambda in [-1,1]
    by exact Bernstein subdivision;
  * positivity of the nonlinear kernels K2,K3,K4 on their full boxes by exact
    Bernstein subdivision;
  * scalar inequalities used in the near-bipartite spectral/triangle argument.

All computations are over rational numbers, except for printing optional decimal
summaries.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import combinations, permutations, product
import sympy as sp


def assert_zero(expr, name: str) -> None:
    if sp.simplify(expr) != 0:
        raise AssertionError(f"{name} failed: {sp.factor(expr)}")
    print(f"OK: {name}")


def assert_true(cond: bool, name: str) -> None:
    if not cond:
        raise AssertionError(f"{name} failed")
    print(f"OK: {name}")


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


def path_formulae(max_n: int):
    q = sp.symbols("q")
    s = sp.symbols("s0:30")
    a = sp.Integer(1)
    h = defaultdict(lambda: sp.Integer(0))  # h = sum_p h[p] A^p g
    xs = {0: a}
    for n in range(1, max_n + 1):
        inner = sum(c * s[p] for p, c in h.items())
        a_new = sp.expand(q * a + inner)
        h_new = defaultdict(lambda: sp.Integer(0))
        h_new[0] += a
        for pwr, c in h.items():
            h_new[pwr + 1] += c
        a, h = a_new, h_new
        xs[n] = a
    return q, s, xs


def expression_from_counts(n: int, q, xs):
    """Lower expression for t(C_n,1-U) obtained by replacing -t(C_n,U) by -x_{n-1}."""
    counts = cycle_forest_counts(n)

    def term(comp):
        out = sp.Integer(1)
        for a in comp:
            out *= q if a == 1 else xs[a]
        return out

    E = sp.Integer(1)
    for r in range(1, n):
        for comp, c in counts[r].items():
            E += (-1) ** r * c * term(comp)
    E -= xs[n - 1]
    return sp.expand(E)


def c11_path_expression(q, x):
    return sp.expand(
        -10*q**10 + 55*q**9 - 165*q**8 + 330*q**7 - 462*q**6 + 451*q**5
        + 11*q**4*x[2] - 275*q**4
        - 110*q**3*x[2] + 44*q**3*x[3] - 11*q**3*x[4] + 88*q**3
        + 66*q**2*x[2]**2 - 33*q**2*x[2]*x[3] + 165*q**2*x[2]
        - 110*q**2*x[3] + 66*q**2*x[4] - 33*q**2*x[5] + 11*q**2*x[6] - 11*q**2
        - 11*q*x[2]**3 - 110*q*x[2]**2 + 132*q*x[2]*x[3]
        - 66*q*x[2]*x[4] + 22*q*x[2]*x[5] - 77*q*x[2]
        - 33*q*x[3]**2 + 22*q*x[3]*x[4] + 66*q*x[3]
        - 55*q*x[4] + 44*q*x[5] - 33*q*x[6] + 22*q*x[7] - 11*q*x[8]
        + 10*x[10] + 22*x[2]**3 - 33*x[2]**2*x[3] + 11*x[2]**2*x[4]
        + 33*x[2]**2 + 11*x[2]*x[3]**2 - 55*x[2]*x[3]
        + 44*x[2]*x[4] - 33*x[2]*x[5] + 22*x[2]*x[6] - 11*x[2]*x[7]
        + 11*x[2] + 22*x[3]**2 - 33*x[3]*x[4] + 22*x[3]*x[5]
        - 11*x[3]*x[6] - 11*x[3] + 11*x[4]**2 - 11*x[4]*x[5]
        + 11*x[4] - 11*x[5] + 11*x[6] - 11*x[7] + 11*x[8] - 11*x[9]
    )


def bernstein_min(poly, vars_, degrees):
    P = sp.Poly(poly, *vars_)
    coeff = {mon: c for mon, c in P.terms()}
    mn = None
    for beta in product(*[range(d + 1) for d in degrees]):
        b = sp.Rational(0)
        for alpha in product(*[range(bi + 1) for bi in beta]):
            c = coeff.get(alpha)
            if c is None:
                continue
            factor = sp.Rational(1)
            for bi, ai, di in zip(beta, alpha, degrees):
                factor *= sp.Rational(sp.binomial(bi, ai), sp.binomial(di, ai))
            b += c * factor
        if mn is None or b < mn:
            mn = sp.factor(b)
    return mn


def certify_positive_bernstein(poly, orig_vars, bounds, name: str, max_boxes: int = 100000):
    """Certify poly>0 on a rational box by recursive exact Bernstein subdivision."""
    n = len(orig_vars)
    unit = sp.symbols(f"z0:{n}")
    boxes = [tuple(bounds)]
    done = 0
    worst = None
    while boxes:
        box = boxes.pop()
        sub = {v: lo + (hi - lo) * z for v, z, (lo, hi) in zip(orig_vars, unit, box)}
        G = sp.expand(poly.subs(sub))
        P = sp.Poly(G, *unit)
        degs = tuple(P.degree(z) for z in unit)
        mn = bernstein_min(G, unit, degs)
        if mn > 0:
            done += 1
            if worst is None or mn < worst:
                worst = mn
            continue
        if len(boxes) + done > max_boxes:
            raise AssertionError(f"{name}: too many boxes; current min {mn}; box {box}")
        lengths = [hi - lo for lo, hi in box]
        i = max(range(n), key=lambda j: lengths[j])
        lo, hi = box[i]
        mid = (lo + hi) / 2
        b1 = list(box)
        b2 = list(box)
        b1[i] = (lo, mid)
        b2[i] = (mid, hi)
        boxes.append(tuple(b1))
        boxes.append(tuple(b2))
    print(f"OK: {name} by Bernstein subdivision ({done} boxes, worst lower coefficient {worst})")


def kernel_for(Fexpr, d, m_symbols):
    lambdas = sp.symbols(f"lam0:{d}")
    K = sp.Integer(0)
    P = sp.Poly(Fexpr, *m_symbols[1:9])
    for exps, coeff in P.terms():
        js = []
        for idx, e in enumerate(exps, start=1):
            js += [idx] * e
        js += [0] * (d - len(js))
        terms = set(permutations(js, d))
        K += coeff * sum(sp.prod(lambdas[i] ** perm[i] for i in range(d)) for perm in terms) / len(terms)
    return sp.expand(K), lambdas


def check_c11_path_certificate():
    q, s, xs = path_formulae(10)
    target = (1 - q) ** 11 - (1 - q) * q ** 10
    Phi_from_counts = sp.expand(expression_from_counts(11, q, xs) - target)
    Phi_stated = c11_path_expression(q, xs)
    assert_zero(Phi_from_counts - Phi_stated, "C11 path-certificate expression from inclusion-exclusion")

    vars_s = s[:9]
    poly = sp.Poly(Phi_stated, *vars_s)
    parts = []
    for d in range(1, 6):
        part = sp.Integer(0)
        for monom, coeff in poly.terms():
            if sum(monom) == d:
                part += coeff * sp.prod(v ** e for v, e in zip(vars_s, monom))
        parts.append(sp.expand(part))
    high5 = parts[4]
    assert_zero(high5 - 10 * s[0] ** 5, "C11 degree-5 part is 10*s0^5")

    # Normalize s_j = r m_j, with m_0=1. Then degree-d part is r^d F_d.
    m = sp.symbols("m0:9")
    subs = {s[0]: 1}
    subs.update({s[j]: m[j] for j in range(1, 9)})
    F = [sp.expand(part.subs(subs)) for part in parts]

    # Linear part: F_1 = integral P_q(lambda) dnu(lambda).
    lam = sp.symbols("lam")
    Pq = sp.Integer(0)
    Ppoly = sp.Poly(F[0], *m[1:9])
    for exps, coeff in Ppoly.terms():
        # linear terms plus constant only
        deg = sum(exps)
        if deg == 0:
            Pq += coeff
        elif deg == 1:
            idx = exps.index(1) + 1
            Pq += coeff * lam ** idx
        else:
            raise AssertionError("F1 is not linear")
    # Certify P_q(lambda)>0 for q in [0,97/200], lambda in [-1,1].
    certify_positive_bernstein(
        Pq,
        (q, lam),
        ((sp.Rational(0), sp.Rational(97, 200)), (sp.Rational(-1), sp.Rational(1))),
        "C11 linear kernel P_q(lambda) on q<=97/200",
    )

    # Nonlinear pieces: F_d is the d-fold average of K_d.
    for d in [2, 3, 4]:
        K, lambdas = kernel_for(F[d - 1], d, m)
        bounds = ((sp.Rational(0), sp.Rational(1, 2)),) + tuple(
            (sp.Rational(-1), sp.Rational(1)) for _ in lambdas
        )
        certify_positive_bernstein(K, (q, *lambdas), bounds, f"C11 nonlinear kernel K_{d}")


def check_spectral_triangle_scalar_inequalities():
    e = sp.symbols("e")
    p = sp.Rational(1, 2) + e
    q = sp.Rational(1, 2) - e
    E = sp.Rational(3, 200)

    # B=p^3-A^3 <= 139/100 e, where A=(p q^10)^(1/11).
    # Since both sides are positive, this follows from
    # (p q^10)^3 >= (p^3 - 139e/100)^11.
    D1 = sp.Poly(sp.expand((p * q ** 10) ** 3 - (p ** 3 - sp.Rational(139, 100) * e) ** 11), e)
    Q1 = sp.Poly(sp.cancel(D1.as_expr() / e), e)
    assert_true(Q1.eval(0) > 0 and Q1.eval(E) > 0 and Q1.count_roots(0, E) == 0,
                "scalar inequality p^3-A^3 <= 139e/100 on 0<=e<=3/200")

    # H=pq-A^2 <= 9e/11, where A=(p q^10)^(1/11).
    # Equivalent to (p q^10)^2 >= (pq - 9e/11)^11.
    D2 = sp.Poly(sp.expand((p * q ** 10) ** 2 - (p * q - sp.Rational(9, 11) * e) ** 11), e)
    expr = D2.as_expr()
    mult = 0
    while sp.Poly(expr, e).eval(0) == 0:
        expr = sp.cancel(expr / e)
        mult += 1
    Q2 = sp.Poly(expr, e)
    assert_true(mult == 2 and Q2.eval(0) > 0 and Q2.eval(E) > 0 and Q2.count_roots(0, E) == 0,
                "scalar inequality pq-A^2 <= 9e/11 on 0<=e<=3/200")

    # c<=1/65 when e<=3/200, because e(c)=c-3c^2/2 is increasing and e(1/65)>3/200.
    assert_true(sp.Rational(1, 65) - sp.Rational(3, 2) * sp.Rational(1, 65) ** 2 > E,
                "triangle parameter bound c<=1/65")

    # Final comparison:
    # alpha*(e+3e^2/2) >= 139e/100 + (9e/11)^(3/2), 0<=e<=3/200.
    # Put t=sqrt(e).  The difference divided by e is
    # f(t) = alpha*(1+3t^2/2) - 139/100 - (9/11)^(3/2)*t,
    # a convex quadratic in t.  Two sub-checks:
    #   (a) Critical point t* = (9/11)^(3/2)/(3*alpha) lies right of sqrt(E),
    #       so f is decreasing on [0,sqrt(E)] and worst case is at t=sqrt(E).
    #       Equivalent rational comparison: 200 * (9/11)^3 > 27 * alpha^2.
    #   (b) At t=sqrt(E), both sides of f(t) >= 0 are positive; squaring,
    #       the squared margin is positive.
    alpha = sp.Rational(3, 2) * sp.Rational(64, 65) ** 2
    monotone_gap = sp.Rational(200) * sp.Rational(9, 11) ** 3 - 27 * alpha ** 2
    assert_true(monotone_gap > 0,
                "critical point of f(t) lies right of sqrt(3/200) (so f decreasing on [0, sqrt(3/200)])")
    left_endpoint = alpha * (1 + sp.Rational(3, 2) * E) - sp.Rational(139, 100)
    square_gap = sp.simplify(left_endpoint ** 2 - (sp.Rational(9, 11) ** 3) * E)
    assert_true(left_endpoint > 0 and square_gap > 0,
                "final scalar comparison for the spectral-triangle interval")


def main() -> None:
    check_c11_path_certificate()
    check_spectral_triangle_scalar_inequalities()
    print("All C11 checks passed.")


if __name__ == "__main__":
    main()
