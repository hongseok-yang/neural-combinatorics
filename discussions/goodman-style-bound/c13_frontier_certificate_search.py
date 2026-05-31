"""
Exact Bernstein checks for the C13 frontier split.

Goal.  In the remaining q-band, split into:

  (safe)     lambda_max(A) <= q, already handled by the positive-spectrum-safe criterion;
  (frontier) lambda_max(A) = alpha > q.

In the frontier case, Tr(A^2) <= pq implies every other positive eigenvalue beta
satisfies beta^2 <= pq - alpha^2 <= q(1-2q).  On q in [481/1000, 49/100],
this gives beta <= 7/50.  Negative eigenvalues are always >= -1/2.

This script checks the pieces of the C13 path-certificate decomposition on the
restricted frontier domains:

  P_q(lambda) for safe modes lambda in [-1/2, 7/50];
  P_q(alpha) for the frontier mode alpha in [q, 1/2];
  K_2 on safe-safe pairs, frontier-safe pairs, and the frontier-frontier diagonal.

The higher kernels K_3,K_4,K_5 were already certified positive on the full
[-1,1] domain in odd_cycle_c13_checker.py.
"""

from __future__ import annotations

import sympy as sp

import odd_cycle_c13_checker as oc


def build_c13_pieces():
    n = 13
    q, s, xs = oc.path_formulae(n - 1)
    target = (1 - q) ** n - (1 - q) * q ** (n - 1)
    phi = sp.expand(oc.expression_from_counts(n, q, xs) - target)

    Pq, lam = oc.extract_Pq_from_Phi(phi, n, q, s)

    vars_s = [s[j] for j in range(n - 2)]
    poly = sp.Poly(phi, *vars_s)
    part2 = sp.Integer(0)
    for monom, coeff in poly.terms():
        if sum(monom) == 2:
            part2 += coeff * sp.prod(v ** e for v, e in zip(vars_s, monom))

    m_syms = sp.symbols(f"m0:{n - 1}")
    subs = {s[0]: 1}
    subs.update({s[j]: m_syms[j] for j in range(1, n - 2)})
    F2 = sp.expand(part2.subs(subs))
    K2, (x, y) = oc.kernel_for(F2, 2, m_syms)
    return q, lam, Pq, x, y, K2


def frontier_sub(q, t):
    return q + (sp.Rational(1, 2) - q) * t


def main():
    q, lam, Pq, x, y, K2 = build_c13_pieces()
    qlo = sp.Rational(481, 1000)
    qhi = sp.Rational(49, 100)
    safe_hi = sp.Rational(7, 50)
    t = sp.symbols("t")

    # Linear piece: safe modes.
    oc.certify_positive_bernstein(
        Pq,
        (q, lam),
        ((qlo, qhi), (sp.Rational(-1, 2), safe_hi)),
        "frontier split: P_q(lambda) for non-frontier modes",
        max_boxes=100000,
    )

    # Linear piece: frontier mode alpha in [q,1/2].
    P_front = sp.expand(Pq.subs(lam, frontier_sub(q, t)))
    oc.certify_positive_bernstein(
        P_front,
        (q, t),
        ((qlo, qhi), (sp.Rational(0), sp.Rational(1))),
        "frontier split: P_q(alpha) for alpha in [q,1/2]",
        max_boxes=100000,
    )

    # Quadratic kernel: safe-safe.
    oc.certify_positive_bernstein(
        K2,
        (q, x, y),
        ((qlo, qhi), (sp.Rational(-1, 2), safe_hi), (sp.Rational(-1, 2), safe_hi)),
        "frontier split: K2 safe-safe",
        max_boxes=100000,
    )

    # Quadratic kernel: frontier-safe.
    K2_front_safe = sp.expand(K2.subs(x, frontier_sub(q, t)))
    oc.certify_positive_bernstein(
        K2_front_safe,
        (q, t, y),
        ((qlo, qhi), (sp.Rational(0), sp.Rational(1)), (sp.Rational(-1, 2), safe_hi)),
        "frontier split: K2 frontier-safe",
        max_boxes=100000,
    )

    # Quadratic kernel: frontier-frontier diagonal (there is at most one frontier eigenvalue).
    K2_front_front = sp.expand(K2.subs({x: frontier_sub(q, t), y: frontier_sub(q, t)}))
    oc.certify_positive_bernstein(
        K2_front_front,
        (q, t),
        ((qlo, qhi), (sp.Rational(0), sp.Rational(1))),
        "frontier split: K2 frontier-frontier diagonal",
        max_boxes=100000,
    )

    print("\nAll frontier split certificate checks passed.")


if __name__ == "__main__":
    main()
