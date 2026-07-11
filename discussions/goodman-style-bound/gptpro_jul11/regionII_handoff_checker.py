#!/usr/bin/env python3
"""Region-II handoff checker for the odd-cycle density project.

This script is intentionally modest.  It is not a proof certificate for the
remaining Region-II scalar inequality.  It performs three kinds of checks:

  1. exact rational algebraic diagnostics that caught previous false routes;
  2. numerical evaluation of the exact Huber target R_m <= C_m psi(xi,rho);
  3. optional coarse/random scans to help future proof attempts locate hard
     parameter regimes.

Run:
    python3 regionII_handoff_checker.py
    python3 regionII_handoff_checker.py --scan

The exact spectral-shift identities and finite high-density certificates are
in clean_two_sided_shift_checker.py, included separately in this package.
"""
from __future__ import annotations

import argparse
import math
import random
from fractions import Fraction as F


def report(name: str, ok: bool, detail: str = "") -> None:
    status = "OK" if ok else "FAIL"
    print(f"[{status}] {name}" + (f" -- {detail}" if detail else ""))
    if not ok:
        raise SystemExit(1)


# ---------------------------------------------------------------------------
# Exact rational checks


def check_correct_recurrence() -> None:
    """Verify the corrected recurrence for r_m exactly on rational samples.

    r_m = x^m + y^m - s^(m-1), s = x^2 + y^2.
    Correct recurrence:
      r_{m+2} = s r_m - x^2 y^2 (x^{m-2}+y^{m-2}) + s^m(1-s).
    The earlier recurrence omitted the last positive term.
    """
    samples = [(F(3, 5), F(1, 5)), (F(7, 10), F(2, 10)), (F(4, 5), F(1, 10))]
    for x, y in samples:
        s = x*x + y*y
        for m in [3, 5, 7, 11, 17]:
            r_m = x**m + y**m - s**(m-1)
            r_next = x**(m+2) + y**(m+2) - s**(m+1)
            rhs = s*r_m - x*x*y*y*(x**(m-2)+y**(m-2)) + s**m*(1-s)
            assert r_next == rhs
            false_rhs = s*r_m - x*x*y*y*(x**(m-2)+y**(m-2))
            assert r_next - false_rhs == s**m*(1-s)
    report("corrected r_m recurrence, exact rational", True)


def check_forced_variance_algebra() -> None:
    """Check the algebra reducing forced variance + HS budget to alpha^2+q alpha <= q."""
    for q in [F(2, 5), F(9, 20), F(7, 18)]:
        for a in [q + F(1, 100), q + F(1, 50)]:
            if a >= F(1, 2):
                continue
            lhs = a*a + a*(a-q)**2/(1-2*a) - q*(1-q)
            simplified = - (a + q - 1)*(a*a + a*q - q)/(1-2*a)
            assert lhs == simplified
    report("forced-variance algebra to frontier upper bound, exact rational", True)


def check_two_clique_ratio() -> None:
    """Exact diagnostic for the family killing a naive total-coupling bound."""
    for s in [F(1, 10), F(1, 100), F(1, 1000), F(1, 10_000)]:
        q = (1-s)**2 / 2
        p = 1 - q
        alpha = (1-s) / 2
        g2 = s*q*q + (1-s)*(alpha-q)**2
        ratio = g2*(p-alpha)**2/(p*alpha*(alpha-q)**2)
        # ratio/s tends to 9.  The loose bound below is exact and enough to
        # confirm the O(s) diagnostic on these samples.
        assert abs(ratio/s - 9) <= 40*s
    report("two-clique false naive coupling ratio = 9s + O(s^2), exact rational", True)


# ---------------------------------------------------------------------------
# Huber target evaluation


def psi_closed(xi: float, rho: float) -> float:
    """Closed form of psi(xi,rho) = min_{0<=v<=1} rho v^2 + (xi-v+v^2)_+."""
    if xi <= 0:
        return 0.0
    # In Region II xi can exceed 1/4; then only the second branch is relevant.
    if xi < 0.25:
        xi_c = (2*rho + 1)/(4*(rho + 1)**2)
        if xi < xi_c:
            vminus = (1 - math.sqrt(max(0.0, 1 - 4*xi)))/2
            return rho*vminus*vminus
    return xi - 1/(4*(1+rho))


def regionII_values(q: float, alpha: float, m: int) -> dict[str, float]:
    p = 1 - q
    L2 = p*q - alpha*alpha
    if L2 <= 0:
        raise ValueError("inadmissible L^2")
    L = math.sqrt(L2)
    e = 1 - 2*alpha
    d = alpha - q
    f = alpha - L
    if min(e, d, f) <= 0:
        raise ValueError("inadmissible parameters")

    def k(lam: float) -> float:
        return (p**(m-1) - lam**(m-1))/(p + lam)

    A = 2*L**(m-2) + m*k(alpha)
    B = 2*L**(m-2) + m*k(L)
    R = alpha**m + L**m - p*q**(m-1)
    C = B*f*math.sqrt(2*alpha)*e*e/(4*alpha*alpha)
    xi = 4*alpha*alpha*d/(e*e)
    rho = (A/B)*math.sqrt(alpha)/(2*math.sqrt(2)*f)
    payment = C*psi_closed(xi, rho)
    return dict(p=p, L=L, A=A, B=B, R=R, C=C, xi=xi, rho=rho, payment=payment)


def frontier_upper(q: float) -> float:
    return (math.sqrt(q*q + 4*q) - q)/2


def check_smooth_counterexample() -> None:
    """Check that the smooth Huber lower bound is too weak at a known point."""
    q = 0.498667598218
    alpha = 0.499255849143
    m = 13
    vals = regionII_values(q, alpha, m)
    xi, rho = vals["xi"], vals["rho"]
    smooth_psi = ((math.sqrt(1 + 4*rho*xi)-1)**2)/(4*rho)
    smooth_payment = vals["C"]*smooth_psi
    exact_payment = vals["payment"]
    R = vals["R"]
    ok = smooth_payment < R < exact_payment
    report("smooth Huber route is strictly too weak at diagnostic point", ok,
           f"R={R:.12e}, smooth={smooth_payment:.12e}, exact={exact_payment:.12e}")


def scan_huber_target() -> None:
    """Coarse deterministic scan of the exact Huber scalar target.

    This is not a proof.  It is meant to catch obvious algebraic mistakes and
    to identify near-tight regimes for future certification.
    """
    worst = (float("inf"), None)
    ms = [3, 5, 7, 9, 13, 21, 51, 101, 201]
    for m in ms:
        for iq in range(1, 80):
            q = 1/3 + (1/2 - 1/3)*iq/80
            upper = frontier_upper(q)
            if upper <= q:
                continue
            for ia in range(1, 80):
                alpha = q + (upper-q)*ia/80
                try:
                    vals = regionII_values(q, alpha, m)
                except ValueError:
                    continue
                margin = vals["payment"] - vals["R"]
                scale = max(abs(vals["payment"]), abs(vals["R"]), 1e-300)
                rel = margin/scale
                if rel < worst[0]:
                    worst = (rel, (m, q, alpha, vals["R"], vals["payment"], vals["xi"], vals["rho"]))
    rel, data = worst
    ok = rel > -1e-8
    report("coarse scan of exact Huber target (diagnostic only)", ok,
           f"worst relative margin {rel:.3e} at {data}")


def random_scan(seed: int = 20260711, trials: int = 20000) -> None:
    rng = random.Random(seed)
    worst = (float("inf"), None)
    for _ in range(trials):
        # Bias toward q near 1/2 and alpha near the frontier, where scans found
        # the tightest cases.
        u = rng.random()
        q = 0.5 - (0.5 - 1/3)*(u*u)
        upper = frontier_upper(q)
        v = rng.random()
        alpha = q + (upper-q)*(1 - v*v)
        m = rng.choice([3,5,7,9,11,13,17,21,31,51,75,101,151,201,301])
        if m % 2 == 0:
            m += 1
        try:
            vals = regionII_values(q, alpha, m)
        except ValueError:
            continue
        margin = vals["payment"] - vals["R"]
        scale = max(abs(vals["payment"]), abs(vals["R"]), 1e-300)
        rel = margin/scale
        if rel < worst[0]:
            worst = (rel, (m, q, alpha, vals["R"], vals["payment"], vals["xi"], vals["rho"]))
    rel, data = worst
    ok = rel > -1e-7
    report("random biased scan of exact Huber target (diagnostic only)", ok,
           f"worst relative margin {rel:.3e} at {data}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--scan", action="store_true", help="run deterministic grid scan")
    parser.add_argument("--random-scan", action="store_true", help="run biased random scan")
    parser.add_argument("--trials", type=int, default=20000)
    args = parser.parse_args()

    check_correct_recurrence()
    check_forced_variance_algebra()
    check_two_clique_ratio()
    check_smooth_counterexample()
    if args.scan:
        scan_huber_target()
    if args.random_scan:
        random_scan(trials=args.trials)
    print("\nCompleted Region-II handoff checks.")


if __name__ == "__main__":
    main()
