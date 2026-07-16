#!/usr/bin/env python3
"""Exact rational-arithmetic certificate for the Zone-B battle of regionII_corrected_solution.tex.

Claim certified (the reduced form of Lemma zoneB): for all
    e in [1/60, 2033/10000],  kappa in [kappa_xi(e), kappa_bar(e)],  m >= 15 odd:
    Pi_lower  >=  max_{n>=14} K(n) / x^2  +  Lambda_upper,
which implies the lambda=1 certificate payment dominates the Bernoulli defect
bound, hence R_m <= C_m psi(xi,rho) on Zone B.  Here (paper notation)
    K(n) = x^n (n-A)/(n+1),  A = x(1+kappa)/kappa,  n = m-1,
    Pi >= sqrt(1-e)(1-l)(1-y^{m-1})(1-eps)/(1+y),
    Lambda = (alpha e)^{m/2}/(m d alpha p^{m-2}) <= x^13 (2e/(1-e))^{6.5}(1-e)^2/(15e).
Facts used (proved in the paper):
    K log-concave on (A,oo); max_{n>=14} K = K(max(14,n*));
    K(14) <= x^14(14-A)_+/15;
    K(n*) <= exp(-lam A - 2w), w = (sqrt(nu^2+4nu)-nu)/2, nu = lam(A+1) >= lam A
             >= Phi := 2(1-e)(1+kappa)^2 e/(kappa(1+e+2 kappa e)^2);
    n* <= 14 on a box if A_max < 14 and 15(14-A_max) lam_min >= A_max+1;
    lam = ln(1/x) in [1-x, (1-x)/x];
    rho >= (1-exp(-17.37(1+kappa)e))/4;  eps <= min(1/4, e/(4(1-e)^2 kappa(1+rho))).
All arithmetic is fractions.Fraction; sqrt/exp are bracketed rationally
(integer isqrt; exponential series partial sums with tail bounds).  No floats.

Run: python3 zoneB_certifier.py       (exit 0 iff certified)
"""
from __future__ import annotations

from fractions import Fraction as F
from math import isqrt

E_LO = F(1, 60)
E_HI = F(2033, 10000)  # the zone is provably empty for e >= 2033/10000
MAX_DEPTH = 26
STATS = {"verified": 0, "skipped": 0, "maxdepth": 0}

SCALE = 10**40


def sqrt_lo(t: F) -> F:
    """Rational lower bound of sqrt(t), t>=0."""
    if t < 0:
        raise ValueError
    n = (t.numerator * SCALE * SCALE) // t.denominator
    return F(isqrt(n), SCALE)


def sqrt_up(t: F) -> F:
    if t < 0:
        raise ValueError
    n = (t.numerator * SCALE * SCALE) // t.denominator
    return F(isqrt(n) + 1, SCALE)


def _round_down(t: F, den: int = 10**12) -> F:
    return F((t.numerator * den) // t.denominator, den)


def _round_up(t: F, den: int = 10**12) -> F:
    return F(-((-t.numerator * den) // t.denominator), den)


def exp_neg_up(t: F) -> F:
    """Rational upper bound of exp(-t) for t >= 0."""
    assert t >= 0
    t = _round_down(t)  # smaller t => larger exp(-t): still an upper bound
    s, term = F(1), F(1)
    for k in range(1, 41):
        term = term * t / k
        s += term
    return F(1) / s  # e^t >= partial sum


def exp_neg_lo(t: F) -> F:
    """Rational lower bound of exp(-t) for t >= 0."""
    assert t >= 0
    t = _round_up(t)
    if t >= 30:
        return F(0)
    N = 80
    s, term = F(1), F(1)
    for k in range(1, N + 1):
        term = term * t / k
        s += term
    rem = term * t / (N + 1 - t)  # geometric tail bound, N+1 > t
    return F(1) / (s + rem)


def x_of(e: F, k: F) -> F:
    return (1 - e) / (1 + e + 2 * k * e)


def kappa_xi(e: F) -> F:
    return e / (1 - e) ** 2


def kappa_bar(e: F) -> F:
    return min((1 - e) / (1 + e), (1 - 3 * e) / (6 * e))


def verify_box(e1: F, e2: F, k1: F, k2: F, depth: int = 0) -> bool:
    STATS["maxdepth"] = max(STATS["maxdepth"], depth)
    # Skip boxes entirely outside the admissible strip.
    # kappa_xi is increasing in e, kappa_bar decreasing in e:
    if k2 <= kappa_xi(e1):          # whole box has kappa <= kappa_xi(e) (xi<=1): Zone C
        STATS["skipped"] += 1
        return True
    if k1 >= kappa_bar(e1):         # whole box has kappa >= kappa_bar(e): outside D
        STATS["skipped"] += 1
        return True

    # Monotone endpoint bounds (x decreasing in e and kappa).
    x_min = x_of(e2, k2)
    x_max = x_of(e1, k1)
    u_min = 1 - x_max
    lam_min = u_min
    A_min = x_min * (1 + k2) / k2
    A_max = x_max * (1 + k1) / k1

    l2_up = 2 * e2 / (1 - e2)                 # (l_bar)^2 upper
    l_up = sqrt_up(l2_up)
    if l_up >= 1:
        return subdivide(e1, e2, k1, k2, depth)
    l14_up = min(F(1), l2_up**7)

    t_rho = F(1737, 100) * (1 + k1) * e1
    rho_lo = (1 - exp_neg_up(t_rho)) / 4
    eps_up = min(F(1, 4), e2 / (4 * (1 - e2) ** 2 * k1 * (1 + rho_lo)))

    Pi_lo = sqrt_lo(1 - e2) * (1 - l_up) * (1 - l14_up) * (1 - eps_up) / (1 + l_up)
    if Pi_lo <= 0:
        return subdivide(e1, e2, k1, k2, depth)

    Lam_up = x_max**13 * (2 * e2 / (1 - e2)) ** 6 * sqrt_up(2 * e2 / (1 - e2)) \
        * (1 - e1) ** 2 / (15 * e1)

    K1_up = x_max**14 * max(F(0), 14 - A_min) / 15

    gate_only_K14 = (A_max < 14) and (15 * (14 - A_max) * lam_min >= A_max + 1)
    if gate_only_K14:
        K_up = K1_up
    else:
        Phi_min = 2 * (1 - e2) * e1 * (1 + k2) ** 2 / (k2 * (1 + e2 + 2 * k2 * e2) ** 2)
        nu = Phi_min
        w_lo = max(F(0), (sqrt_lo(nu * nu + 4 * nu) - nu) / 2)
        K2_up = exp_neg_up(Phi_min + 2 * w_lo)
        K_up = max(K1_up, K2_up)

    if Pi_lo >= K_up / (x_min * x_min) + Lam_up:
        STATS["verified"] += 1
        return True
    return subdivide(e1, e2, k1, k2, depth)


def subdivide(e1, e2, k1, k2, depth) -> bool:
    if depth >= MAX_DEPTH:
        print(f"UNRESOLVED BOX: e in [{float(e1):.6f},{float(e2):.6f}], "
              f"kappa in [{float(k1):.6f},{float(k2):.6f}]")
        return False
    em, km = (e1 + e2) / 2, (k1 + k2) / 2
    if (e2 - e1) / e1 >= (k2 - k1) / k1:
        return verify_box(e1, em, k1, k2, depth + 1) & verify_box(em, e2, k1, k2, depth + 1)
    return verify_box(e1, e2, k1, km, depth + 1) & verify_box(e1, e2, km, k2, depth + 1)


def main() -> None:
    import sys
    sys.setrecursionlimit(100000)
    ok = verify_box(E_LO, E_HI, kappa_xi(E_LO), F(1), 0)
    print(f"boxes verified: {STATS['verified']}, skipped (outside domain): "
          f"{STATS['skipped']}, max depth: {STATS['maxdepth']}")
    print("ZONE-B BATTLE CERTIFIED (exact rational arithmetic)" if ok
          else "CERTIFICATION FAILED")
    raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    main()
