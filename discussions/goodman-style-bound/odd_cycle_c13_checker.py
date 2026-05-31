"""
Exact-arithmetic checker for odd_cycle_c13_working_note.tex.

The checker verifies the algebraic identities and the finite certificates used
in the C_13 path-certificate range:
  * inclusion-exclusion formula for the crude C_13 path certificate;
  * path-density moment recurrence up to P_12;
  * decomposition of the certificate into homogeneous moment pieces
        Phi_13 = L_1 + L_2 + L_3 + L_4 + L_5 + 12 s_0^6;
  * closed-form formula for the linear-part polynomial P_q^(m) valid for all
    odd m >= 5, cross-checked against m = 11 and m = 13;
  * positivity of the linear piece P_q^(13)(lambda) on q in [0, 481/1000]
    and lambda in [-1, 1] by exact rational Bernstein subdivision;
  * positivity of the nonlinear kernel K_2 on q in [0, 481/1000] and of
    K_3, K_4, K_5 on q in [0, 1/2] by exact rational Bernstein subdivision.

The path-certificate cut-off rho_13 = 519/1000 follows.  This checker does
not cover the spectral-triangle near-bipartite argument or the later frontier
split; those are checked in c13_near_bipartite_checker.py and
c13_frontier_certificate_search.py.

All computations are over rational numbers, except for printing optional
decimal summaries.
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
    return {r: Counter(path_components(n, s) for s in combinations(range(n), r))
            for r in range(n + 1)}


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
    P = sp.Poly(Fexpr, *m_symbols[1:])
    for exps, coeff in P.terms():
        js = []
        for idx, e in enumerate(exps, start=1):
            js += [idx] * e
        js += [0] * (d - len(js))
        terms = set(permutations(js, d))
        K += coeff * sum(sp.prod(lambdas[i] ** perm[i] for i in range(d)) for perm in terms) / len(terms)
    return sp.expand(K), lambdas


def closed_form_Pq_coefficient(m, j, q):
    """
    Closed-form coefficient of lambda^j in P_q^(m), valid for odd m >= 5 and
    0 <= j <= m - 3:
        a_j^(m)(q) = (-1)^j m (1-q)^(m-2-j) + m q^(m-2-j) - (m-2-j) q^(m-3-j).
    The leading coefficient a_{m-3}^(m) equals m - 1.
    """
    return ((-1) ** j * m * (1 - q) ** (m - 2 - j)
            + m * q ** (m - 2 - j)
            - (m - 2 - j) * q ** (m - 3 - j))


def extract_Pq_from_Phi(Phi, n, q, s):
    """Given Phi_n in symbols q, s_0, ..., s_{n-2}, return the degree-1 polynomial
    P_q(lambda) such that L_1 = integral P_q(lambda) d-mu(lambda)."""
    vars_s = [s[j] for j in range(n - 2)]
    poly = sp.Poly(Phi, *vars_s)
    L1 = sp.Integer(0)
    for monom, coeff in poly.terms():
        if sum(monom) == 1:
            L1 += coeff * sp.prod(v ** e for v, e in zip(vars_s, monom))
    m_syms = sp.symbols(f"m0:{n - 1}")
    subs = {s[0]: 1}
    subs.update({s[j]: m_syms[j] for j in range(1, n - 2)})
    L1_norm = sp.expand(L1.subs(subs))
    lam = sp.symbols("lam")
    Pq = sp.Integer(0)
    Ppoly = sp.Poly(L1_norm, *m_syms[1:n - 2])
    for exps, coeff in Ppoly.terms():
        deg = sum(exps)
        if deg == 0:
            Pq += coeff
        elif deg == 1:
            idx = exps.index(1) + 1
            Pq += coeff * lam ** idx
        else:
            raise AssertionError("L_1 is not linear in m_1, ..., m_{n-2}")
    return sp.expand(Pq), lam


def check_closed_form_for_m(m_val):
    """Verify Proposition: P_q^(m) matches the closed-form for the given odd m."""
    q_m, s_m, xs_m = path_formulae(m_val - 1)
    target = (1 - q_m) ** m_val - (1 - q_m) * q_m ** (m_val - 1)
    Phi_m = sp.expand(expression_from_counts(m_val, q_m, xs_m) - target)
    Pq, lam = extract_Pq_from_Phi(Phi_m, m_val, q_m, s_m)
    Pq_closed = sum(closed_form_Pq_coefficient(m_val, j, q_m) * lam ** j
                    for j in range(m_val - 2))
    assert_zero(sp.expand(Pq - Pq_closed),
                f"closed-form P_q^({m_val}) matches recurrence-derived P_q for m={m_val}")


def check_c13_path_certificate():
    n = 13
    q, s, xs = path_formulae(n - 1)
    target = (1 - q) ** n - (1 - q) * q ** (n - 1)
    Phi = sp.expand(expression_from_counts(n, q, xs) - target)

    # Decompose by total degree in s_0..s_10.
    vars_s = [s[j] for j in range(n - 2)]  # s_0..s_10
    poly = sp.Poly(Phi, *vars_s)
    parts = []
    for d in range(0, 7):
        part = sp.Integer(0)
        for monom, coeff in poly.terms():
            if sum(monom) == d:
                part += coeff * sp.prod(v ** e for v, e in zip(vars_s, monom))
        parts.append(sp.expand(part))

    # The (q-only) degree-0 part should vanish (target was subtracted).
    assert_zero(parts[0], "C13 degree-0 (pure-q) part of Phi_13 is 0")
    # Degree-6 top is 12 s_0^6 (= (m-1) s_0^((m-1)/2) at m=13).
    assert_zero(parts[6] - 12 * s[0] ** 6, "C13 degree-6 (top) part is 12*s_0^6")

    # Cross-check the closed-form P_q^(m) at m = 11 and m = 13.
    check_closed_form_for_m(11)
    check_closed_form_for_m(13)

    # Extract the linear part for m = 13.
    Pq, lam = extract_Pq_from_Phi(Phi, n, q, s)
    # Sanity: degree should be m - 3 = 10.
    assert_true(sp.Poly(Pq, lam).degree() == n - 3,
                f"C13 linear polynomial P_q(lambda) has degree {n-3} in lambda")

    # Certify P_q(lambda) > 0 on q in [0, 481/1000], lambda in [-1, 1].
    certify_positive_bernstein(
        Pq, (q, lam),
        ((sp.Rational(0), sp.Rational(481, 1000)), (sp.Rational(-1), sp.Rational(1))),
        "C13 linear kernel P_q(lambda) on q<=481/1000",
    )

    # Build kernel representations for L_2..L_5 and certify positivity.
    # NOTE: K_2 must be certified on q in [0, 481/1000] (the binding constraint),
    # because K_2 dips slightly negative near q = 1/2 for C_13.
    # K_3, K_4, K_5 are positive on the full q in [0, 1/2].
    m_syms = sp.symbols(f"m0:{n - 1}")
    subs = {s[0]: 1}
    subs.update({s[j]: m_syms[j] for j in range(1, n - 2)})
    F = [sp.expand(part.subs(subs)) for part in parts]

    for d in [2, 3, 4, 5]:
        K, lambdas = kernel_for(F[d], d, m_syms)
        qmax = sp.Rational(481, 1000) if d == 2 else sp.Rational(1, 2)
        qmax_str = "481/1000" if d == 2 else "1/2"
        bounds = ((sp.Rational(0), qmax),) + tuple(
            (sp.Rational(-1), sp.Rational(1)) for _ in lambdas
        )
        certify_positive_bernstein(
            K, (q, *lambdas), bounds,
            f"C13 nonlinear kernel K_{d} on q<={qmax_str}",
        )


def main() -> None:
    check_c13_path_certificate()
    print("All C13 checks passed.")


if __name__ == "__main__":
    main()
