#!/usr/bin/env python3
"""Exact and numerical audit for ``complete_odd_cycle_bound.tex``.

The LaTeX manuscript contains a self-contained proof.  This script is only a
companion audit.  It runs the exact checks from the Region-II note and then
verifies the longer algebraic identities introduced in the dense-region
Dirichlet--beta--gamma proof and in the orthogonal-polynomial discussion.

All symbolic checks use exact SymPy arithmetic.  The final random step-graphon
stress test is numerical and is not used by the proof.
"""
from __future__ import annotations

import math
import runpy
from fractions import Fraction
from pathlib import Path

import numpy as np
import sympy as sp


def check(name: str, condition: bool) -> None:
    if not bool(condition):
        raise AssertionError(name)
    print(f"[OK] {name}")


def complete_homogeneous(variables: list[sp.Expr], degree: int) -> sp.Expr:
    """Complete homogeneous symmetric polynomial by truncated multiplication."""
    coeff = [sp.Integer(0)] * (degree + 1)
    coeff[0] = sp.Integer(1)
    for y in variables:
        nxt = [sp.Integer(0)] * (degree + 1)
        for d in range(degree + 1):
            for k in range(d + 1):
                nxt[d] += coeff[d - k] * y**k
        coeff = nxt
    return sp.expand(coeff[degree])


def gamma_raw_moment(r: int, k: int) -> sp.Integer:
    return sp.rf(r, k)


def shifted_gamma_moment(r: int, z: sp.Rational, k: int) -> sp.Expr:
    return sp.expand(
        sum(
            sp.binomial(k, a) * z**a * (-1) ** (k - a) * gamma_raw_moment(r, a)
            for a in range(k + 1)
        )
    )


def dense_checks() -> None:
    print("\n=== Dense-region exact checks ===")

    # Complete-homogeneous / Dirichlet polarization for representative ranks.
    for r in range(1, 5):
        lambdas = sp.symbols(f"l0:{r}")
        for j in range(0, 7):
            # E(Theta.lambda)^j from the exact Dirichlet monomial formula.
            expectation = sp.Integer(0)
            # Enumerate weak compositions recursively.
            def comps(total: int, parts: int):
                if parts == 1:
                    yield (total,)
                else:
                    for a in range(total + 1):
                        for tail in comps(total - a, parts - 1):
                            yield (a,) + tail
            for alpha in comps(j, r):
                multinomial = sp.factorial(j)
                for a in alpha:
                    multinomial /= sp.factorial(a)
                dmoment = sp.factorial(r - 1)
                for a in alpha:
                    dmoment *= sp.factorial(a)
                dmoment /= sp.factorial(j + r - 1)
                monomial = sp.prod(lambdas[i] ** alpha[i] for i in range(r))
                expectation += multinomial * dmoment * monomial
            rhs = complete_homogeneous(list(lambdas), j) / sp.binomial(j + r - 1, r - 1)
            check(f"Dirichlet moment r={r}, j={j}", sp.expand(expectation - rhs) == 0)

    # Beta representation of h_n(a^r,b^r) and its differentiated version.
    a, b = sp.symbols("a b")
    for r in range(1, 5):
        for n in range(1, 8):
            lhs = complete_homogeneous([a] * r + [b] * r, n)
            # E Xi^k (1-Xi)^(n-k) for Xi~Beta(r,r).
            rhs_expect = sp.Integer(0)
            for k in range(n + 1):
                beta_moment = sp.rf(r, k) * sp.rf(r, n - k) / sp.rf(2 * r, n)
                rhs_expect += sp.binomial(n, k) * a**k * b ** (n - k) * beta_moment
            rhs = sp.binomial(n + 2 * r - 1, 2 * r - 1) * rhs_expect
            check(f"Beta h identity r={r}, n={n}", sp.expand(lhs - rhs) == 0)

            lhs_deriv = complete_homogeneous([a] * (r + 1) + [b] * r, n - 1)
            rhs_deriv_expect = sp.Integer(0)
            if n >= 1:
                # E Xi (aXi+b(1-Xi))^(n-1)
                for k in range(n):
                    beta_moment = sp.rf(r, k + 1) * sp.rf(r, n - 1 - k) / sp.rf(2 * r, n)
                    rhs_deriv_expect += (
                        sp.binomial(n - 1, k) * a**k * b ** (n - 1 - k) * beta_moment
                    )
            rhs_deriv = (
                sp.binomial(n + 2 * r - 1, 2 * r - 1)
                * sp.Rational(n, r)
                * rhs_deriv_expect
            )
            check(
                f"Differentiated beta h identity r={r}, n={n}",
                sp.expand(lhs_deriv - rhs_deriv) == 0,
            )

    # rho identity and the centered even expansion, checked for all small odd n.
    u, v = sp.symbols("u v")
    for n in range(1, 16, 2):
        for r in range(1, 6):
            m = n + 2 * r
            rho = sp.Rational(m, n) * (u**n + (1 - u) ** n) - u ** (n - 1)
            rho_alt = (
                sp.Rational(m, n)
                * (1 - u)
                * ((1 - u) ** (n - 1) - u ** (n - 1))
                + (sp.Rational(m, n) - 1) * u ** (n - 1)
            )
            check(f"rho pointwise identity n={n}, r={r}", sp.expand(rho - rho_alt) == 0)

            A = u**n + (1 - u) ** n
            derivative_form = 2 * r * A - (1 - u) * sp.diff(A, u)
            check(
                f"rho derivative identity n={n}, r={r}",
                sp.expand(n * rho - derivative_form) == 0,
            )

            centered = sp.expand((n * rho).subs(u, sp.Rational(1, 2) + v))
            expected = sp.Integer(0)
            for j in range((n - 1) // 2 + 1):
                aj = 2 ** (2 * j + 1 - n) * sp.binomial(n, 2 * j)
                if j == 0:
                    expected += 2 * r * aj
                else:
                    expected += aj * (2 * (r + j) * v ** (2 * j) - j * v ** (2 * j - 1))
            check(f"centered rho expansion n={n}, r={r}", sp.expand(centered - expected) == 0)

    # Gamma recurrence, ODE, zero-crossing formula, and critical-point factorization.
    r, j, bvar = sp.symbols("r j b", positive=True)
    F, Fp = sp.symbols("F Fp", nonzero=True)
    Fpp = (2 * j * F - (bvar - r - 2 * j + 1) * Fp) / bvar
    Hprime = (r + j) * Fp + sp.Rational(3, 2) * Fp + sp.Rational(3, 2) * bvar * Fpp
    Fp_at_zero = -2 * (r + j) * F / (3 * bvar)
    crossing = sp.factor((Hprime.subs(Fp, Fp_at_zero)) / F)
    crossing_target = (
        3 * (r + 4 * j) * bvar - (r + j) * (5 * r + 8 * j)
    ) / (3 * bvar)
    check("H zero-crossing formula", sp.simplify(crossing - crossing_target) == 0)

    bstar = (r + j) * (5 * r + 8 * j) / (3 * (r + 4 * j))
    d = 2 * (r + j) / 3
    c = 3 * j * bstar / (r + j)
    check("b*-d identity", sp.factor(bstar - d - r * (r + j) / (r + 4 * j)) == 0)
    check("cd identity", sp.factor(c * d - 2 * j * bstar) == 0)
    check("c-d identity", sp.factor(c - d - (r + 2 * j - bstar)) == 0)

    x = sp.symbols("x", real=True)
    # Verify logarithmic derivative factorization instead of differentiating symbolic powers fully.
    log_derivative = 2 * j / x + r / (x + bstar) - 1
    factored = (c - x) * (x + d) / (x * (x + bstar))
    check("G derivative factorization", sp.factor(log_derivative - factored) == 0)

    # L(t) derivative formulas and rational tangent upper bound.
    t = sp.symbols("t", positive=True)
    A_t = 3 * t * (5 + 8 * t) / (2 * (1 + t) * (1 + 4 * t))
    B_t = (1 + 4 * t) * (5 + 8 * t) / (3 * (1 + t))
    R_t = (32 * t**2 + 25 * t + 2) / (3 * (1 + 4 * t))
    L = 2 * t * sp.log(A_t) + sp.log(B_t) - R_t
    Lprime_target = 2 * sp.log(A_t) - (
        (32 * t**2 + 16 * t - 7) * (32 * t**2 + 25 * t + 2)
    ) / (3 * (t + 1) * (4 * t + 1) ** 2 * (8 * t + 5))
    check("L'(t) identity", sp.simplify(sp.diff(L, t) - Lprime_target) == 0)

    Lsecond_target = -(
        (32 * t**2 + 25 * t + 2)
        * (128 * t**4 + 224 * t**3 + 120 * t**2 - 28 * t - 25)
    ) / (t * (t + 1) ** 2 * (4 * t + 1) ** 3 * (8 * t + 5) ** 2)
    check("L''(t) identity", sp.simplify(sp.diff(Lprime_target, t) - Lsecond_target) == 0)

    tangent_upper = (
        2 * t * (sp.Rational(7, 10) + (A_t - 2) / 2)
        + sp.Rational(13, 5)
        + (B_t - 13) / 13
        - R_t
    )
    rational_target = 3 * (96 * t**3 - 191 * t**2 - 16 * t + 46) / (
        130 * (t + 1) * (4 * t + 1)
    )
    check("rational upper bound simplification", sp.factor(tangent_upper - rational_target) == 0)

    cubic = 96 * t**3 - 191 * t**2 - 16 * t + 46
    check("cubic endpoint at 1", cubic.subs(t, 1) == -65)
    check("cubic endpoint at 3/2", cubic.subs(t, sp.Rational(3, 2)) == -sp.Rational(335, 4))

    # Generalized Laguerre representation of shifted gamma moments.
    bb = sp.symbols("bb")
    for rv in range(1, 7):
        for k in range(0, 13):
            moment = sp.expand(
                sum(
                    sp.binomial(k, a) * (-bb) ** (k - a) * sp.rf(rv, a)
                    for a in range(k + 1)
                )
            )
            laguerre = sp.expand((-1) ** k * sp.factorial(k) * sp.assoc_laguerre(k, -rv - k, -bb))
            check(f"Laguerre shifted-moment identity r={rv}, k={k}", moment == laguerre)

    # Exact stress test of the gamma moment inequality over a rational grid.
    z_grid = [
        sp.Rational(0), sp.Rational(1, 20), sp.Rational(1, 10),
        sp.Rational(1, 4), sp.Rational(1, 2), sp.Rational(1),
        sp.Rational(2), sp.Rational(5), sp.Rational(10),
    ]
    for rv in range(1, 16):
        for jj in range(1, 13):
            for z in z_grid:
                odd = shifted_gamma_moment(rv, z, 2 * jj - 1)
                even = shifted_gamma_moment(rv, z, 2 * jj)
                gap = sp.expand((rv + jj) * even - 3 * jj * odd)
                if gap < 0:
                    raise AssertionError(("gamma moment grid", rv, jj, z, gap))
    print("[OK] exact gamma moment grid r<=15, j<=12")

    # Exact stress test of shifted-gamma positivity at q=0,1/6,1/3.
    q_grid = [sp.Rational(0), sp.Rational(1, 12), sp.Rational(1, 6), sp.Rational(1, 4), sp.Rational(1, 3)]
    x_grid = [sp.Rational(0), sp.Rational(1, 10), sp.Rational(1, 2), sp.Rational(1), sp.Rational(3)]
    for nn in range(1, 14, 2):
        for rr in range(1, 8):
            mm = nn + 2 * rr
            Y = sp.symbols("Y")
            for qq in q_grid:
                for xx in x_grid:
                    poly = sp.Poly(
                        sp.expand(
                            sp.Rational(mm, nn)
                            * ((qq + xx * Y) ** nn + (1 - qq - xx * Y) ** nn)
                            - (qq + xx * Y) ** (nn - 1)
                        ),
                        Y,
                    )
                    expectation = sum(
                        coeff * gamma_raw_moment(rr, monom[0])
                        for monom, coeff in poly.terms()
                    )
                    if sp.simplify(expectation) < 0:
                        raise AssertionError(("shifted gamma positivity grid", nn, rr, qq, xx, expectation))
    print("[OK] exact shifted-gamma positivity grid")


def random_step_graphon_checks() -> None:
    print("\n=== Numerical random step-graphon stress test ===")
    rng = np.random.default_rng(20260718)
    min_gap = math.inf
    worst = None
    for n in range(2, 13):
        weights = rng.dirichlet(np.ones(n))
        s = np.sqrt(weights)
        for trial in range(250):
            mat = rng.random((n, n))
            mat = (mat + mat.T) / 2
            # Include structured near-extreme samples as well.
            if trial % 10 == 0:
                mat = (mat > 0.5).astype(float)
                mat = np.triu(mat) + np.triu(mat, 1).T
            p = float(weights @ mat @ weights)
            op = (s[:, None] * mat) * s[None, :]
            eig = np.linalg.eigvalsh(op)
            for m in range(3, 24, 2):
                density = float(np.sum(eig**m))
                target = p**m - p * (1 - p) ** (m - 1)
                gap = density - target
                if gap < min_gap:
                    min_gap = gap
                    worst = (n, trial, m, p, density, target)
                if gap < -2e-11:
                    raise AssertionError(("random graphon gap", gap, worst))
    print(f"[OK] random step graphons; minimum numerical gap {min_gap:.3e}")
    print(f"     worst tuple (n,trial,m,p,density,target)={worst}")


def main() -> None:
    print("=== Region-II exact audit ===")
    region_script = Path(__file__).with_name("regionII_exact_checks.py")
    if not region_script.exists():
        raise FileNotFoundError(region_script)
    runpy.run_path(str(region_script), run_name="__main__")
    dense_checks()
    random_step_graphon_checks()
    print("\nAll complete-proof checks passed.")


if __name__ == "__main__":
    main()
