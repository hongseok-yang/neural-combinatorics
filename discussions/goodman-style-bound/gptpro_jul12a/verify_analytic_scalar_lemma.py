#!/usr/bin/env python3
"""Exact algebra and high-precision regression checks for the analytic lemma.

This program is not part of the proof.  It verifies the identities used in
`goodman_odd_cycles_claude_audit_and_analytic_completion.tex` and samples the
quadratic stop-loss transform H on the full parameter region.
"""

from __future__ import annotations

import argparse
import random
from dataclasses import dataclass

import mpmath as mp
import sympy as sp


def check_symbolic_identities() -> None:
    q, f, eps = sp.symbols("q f eps", nonnegative=True)
    p = 1 - q
    r = 1 - 2 * q
    alpha = (q + f) / (1 + f)
    L = (q - f**2) / (1 + f)
    c = (r + f**2) / (1 + f)
    a = p * (q + f) / (1 + f) ** 2
    u = f * (r - f) / (1 + f)

    assert sp.factor(alpha - L - f) == 0
    assert sp.factor(1 - alpha - L - c) == 0
    assert sp.factor(c - r - f * (f - r) / (1 + f)) == 0
    assert sp.factor(u - f * (c - f)) == 0

    x = sp.symbols("x")
    chi = x**2 - c * x - a
    assert sp.factor(chi.subs(x, p) + a * f**2) == 0
    assert sp.factor(chi.subs(x, -L) + f * (1 - alpha)) == 0
    h0_formula = c * (c**2 + 3 * a - L**2) - p * r
    assert sp.factor(h0_formula - 2 * a * f**2) == 0

    # Formulas in the transition case.
    T = 2 * c * eps - u * (q + u)
    Hq = 3 * c * eps**2 + c * (2 * q + 3 * (r + u)) * eps - u**2 * (q + u)
    D = sp.expand(c * Hq - T**2)
    relation = eps**2 + (1 + u) * eps - a * f**2
    reduced_D = sp.Poly(D, eps).rem(sp.Poly(relation, eps)).as_expr()
    target_D = 4 * p * r * c * eps - c**2 * a * f**2 - p * u**2 * (q + u)
    assert sp.factor(reduced_D - target_D) == 0

    E = 2 * p * q * r * c - c**2 * a - p * (c - f) ** 2 * (q + u)
    F = sp.factor((1 + f) ** 4 * E / p)
    P = (
        2 * r * (1 - 3 * r**2)
        + (-1 + 5 * r + 7 * r**2 - 7 * r**3) * f
        - 2 * (1 + r**3) * f**2
        + 2 * r * (1 - 3 * r) * f**3
        + 2 * r * (1 - r) * f**4
    )
    assert sp.factor(2 * F - f * P) == 0

    print("[exact] all symbolic identities passed")


@dataclass(frozen=True)
class Parameters:
    q: mp.mpf
    p: mp.mpf
    alpha: mp.mpf
    L: mp.mpf
    c: mp.mpf
    a: mp.mpf
    beta: mp.mpf
    gamma: mp.mpf
    f: mp.mpf


def make_parameters(q: mp.mpf, alpha: mp.mpf) -> Parameters:
    p = 1 - q
    L = (q - alpha**2) / (1 - alpha)
    c = 1 - alpha - L
    a = alpha * (1 - alpha)
    h = mp.sqrt(c**2 + 4 * a)
    beta = (h + c) / 2
    gamma = (h - c) / 2
    return Parameters(q, p, alpha, L, c, a, beta, gamma, alpha - L)


def H(P: Parameters, t: mp.mpf) -> mp.mpf:
    plus = lambda z: max(z, mp.mpf("0"))
    return (
        P.beta * plus(P.beta - t) ** 2
        + P.p * plus(P.q - t) ** 2
        - P.p * plus(P.p - t) ** 2
        - P.gamma * plus(P.gamma - t) ** 2
        - P.c * plus(P.L - t) ** 2
    )


def scalar_gap(P: Parameters, k: int) -> mp.mpf:
    return (
        P.beta ** (2 * k + 1)
        - P.gamma ** (2 * k + 1)
        - P.c * P.L ** (2 * k)
        - P.p ** (2 * k + 1)
        + P.p * P.q ** (2 * k)
    )


def stress_test(points: int, max_k: int, seed: int) -> None:
    mp.mp.dps = 90
    rng = random.Random(seed)
    worst_h = mp.inf
    worst_gap = mp.inf
    worst_h_data = None
    worst_gap_data = None

    # Include all important boundaries, then random interior points.
    samples: list[tuple[mp.mpf, mp.mpf]] = []
    for q0 in [mp.mpf(1) / 3, mp.mpf("0.4"), mp.mpf("0.499999")]:
        for theta in [mp.mpf("0"), mp.mpf("0.25"), mp.mpf("0.5"), mp.mpf("0.75"), mp.mpf("1")]:
            samples.append((q0, q0 + theta * (mp.sqrt(q0) - q0)))
    for _ in range(points):
        q0 = mp.mpf(1) / 3 + mp.mpf(str(rng.random())) * (mp.mpf(1) / 2 - mp.mpf(1) / 3)
        theta = mp.mpf(str(rng.random()))
        samples.append((q0, q0 + theta * (mp.sqrt(q0) - q0)))

    for q0, alpha0 in samples:
        P = make_parameters(q0, alpha0)
        supports = [mp.mpf("0"), P.L, P.q, P.gamma, P.p, P.beta]
        probes = set(supports)
        ordered = sorted(supports)
        for left, right in zip(ordered, ordered[1:]):
            probes.add((left + right) / 2)
            probes.add((2 * left + right) / 3)
            probes.add((left + 2 * right) / 3)
        for t in probes:
            value = H(P, t)
            if value < worst_h:
                worst_h = value
                worst_h_data = (q0, alpha0, t)
            if value < mp.mpf("-1e-65"):
                raise AssertionError(f"negative H={value} at q,alpha,t={worst_h_data}")

        for k in range(1, max_k + 1):
            value = scalar_gap(P, k)
            if value < worst_gap:
                worst_gap = value
                worst_gap_data = (q0, alpha0, k)
            if value < mp.mpf("-1e-65"):
                raise AssertionError(f"negative scalar gap={value} at q,alpha,k={worst_gap_data}")

    print(f"[numeric] tested {len(samples)} parameter pairs, k<= {max_k}")
    print(f"[numeric] minimum sampled H: {mp.nstr(worst_h, 20)} at {worst_h_data}")
    print(f"[numeric] minimum sampled gap: {mp.nstr(worst_gap, 20)} at {worst_gap_data}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--points", type=int, default=2000)
    parser.add_argument("--max-k", type=int, default=50)
    parser.add_argument("--seed", type=int, default=20260711)
    args = parser.parse_args()

    check_symbolic_identities()
    stress_test(args.points, args.max_k, args.seed)
    print("PASS")


if __name__ == "__main__":
    main()
