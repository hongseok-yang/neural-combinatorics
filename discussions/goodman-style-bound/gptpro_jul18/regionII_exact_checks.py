#!/usr/bin/env python3
"""Exact symbolic audit for ``regionII_self_contained_proof.tex``.

This script is a companion check, not an additional hypothesis of the proof.
It verifies, over the rationals with SymPy, the longer algebraic identities and
both Bernstein-coefficient lists used in the note:

* the C5 inclusion--exclusion reduction and square completion;
* the C7 inclusion--exclusion reduction and univariate SOS identity;
* the forced-variance factorization and chart identities;
* derivative identities used in the one-variable estimates;
* the small-v squared polynomial identity for m=9;
* the degree-9 and degree-10 Bernstein certificates.

Run with Python 3 and SymPy installed:

    python3 regionII_exact_checks.py
"""

from __future__ import annotations

import sympy as sp


def check(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(name)
    print(f"[OK] {name}")


def bernstein_coefficients(
    polynomial: sp.Expr,
    variable: sp.Symbol,
    left: sp.Rational,
    right: sp.Rational,
    degree: int,
) -> list[sp.Expr]:
    """Return Bernstein coefficients on [left,right] in exact arithmetic."""
    t = sp.symbols("_t")
    transformed = sp.Poly(
        sp.expand(polynomial.subs(variable, left + (right - left) * t)), t
    )
    power = [transformed.coeff_monomial(t**j) for j in range(degree + 1)]
    return [
        sp.simplify(
            sum(
                power[j]
                * sp.binomial(i, j)
                / sp.binomial(degree, j)
                for j in range(i + 1)
            )
        )
        for i in range(degree + 1)
    ]


def main() -> None:
    q, lam = sp.symbols("q lam")
    s0, s1, s2, s3, s4 = sp.symbols("s0 s1 s2 s3 s4")

    # C5 identity and completion of the square.
    tg2, gtg, g2 = sp.symbols("tg2 gtg g2")
    x2 = q**2 + g2
    x3 = q**3 + 2 * q * g2 + gtg
    x4 = q**4 + 3 * q**2 * g2 + 2 * q * gtg + tg2
    c5_lower = 1 - 5 * q + 5 * q**2 + 5 * (1 - q) * x2 - 5 * x3 + 4 * x4
    target5 = (1 - q) ** 5 - (1 - q) * q**4
    phi5 = sp.expand(c5_lower - target5)
    expected5 = (
        4 * tg2 + (8 * q - 5) * gtg + (12 * q**2 - 15 * q + 5) * g2
    )
    check("C5 reduction", sp.expand(phi5 - expected5) == 0)
    check(
        "C5 square completion",
        sp.expand(
            (12 * q**2 - 15 * q + 5)
            - (8 * q - 5) ** 2 / 16
            - (8 * q**2 - 10 * q + sp.Rational(55, 16))
        )
        == 0,
    )

    # C7 path formulas and inclusion--exclusion reduction.
    x2 = q**2 + s0
    x3 = q**3 + 2 * q * s0 + s1
    x4 = q**4 + 3 * q**2 * s0 + 2 * q * s1 + s0**2 + s2
    x5 = (
        q**5
        + 4 * q**3 * s0
        + 3 * q**2 * s1
        + 3 * q * s0**2
        + 2 * q * s2
        + 2 * s0 * s1
        + s3
    )
    x6 = (
        q**6
        + 5 * q**4 * s0
        + 4 * q**3 * s1
        + 6 * q**2 * s0**2
        + 3 * q**2 * s2
        + 6 * q * s0 * s1
        + 2 * q * s3
        + s0**3
        + 2 * s0 * s2
        + s1**2
        + s4
    )
    c7_lower = (
        6 * x6
        - 7 * x5
        + 7 * (1 - q) * x4
        + 7 * (2 * q - 1) * x3
        + 7 * (q**2 - 3 * q + 1) * x2
        + 7 * x2**2
        - 7 * x2 * x3
        + 1
        - 7 * q
        + 14 * q**2
        - 7 * q**3
    )
    target7 = (1 - q) ** 7 - (1 - q) * q**6
    phi7 = sp.expand(c7_lower - target7)
    expected7 = (
        6 * s4
        + (12 * q - 7) * s3
        + (18 * q**2 - 21 * q + 7) * s2
        + (24 * q**3 - 42 * q**2 + 28 * q - 7) * s1
        + (30 * q**4 - 70 * q**3 + 70 * q**2 - 35 * q + 7) * s0
        + 12 * s0 * s2
        + (36 * q - 21) * s0 * s1
        + (36 * q**2 - 42 * q + 14) * s0**2
        + 6 * s0**3
        + 6 * s1**2
    )
    check("C7 reduction", sp.expand(phi7 - expected7) == 0)

    p_poly = (
        6 * lam**4
        + (12 * q - 7) * lam**3
        + (18 * q**2 - 21 * q + 7) * lam**2
        + (24 * q**3 - 42 * q**2 + 28 * q - 7) * lam
        + 30 * q**4
        - 70 * q**3
        + 70 * q**2
        - 35 * q
        + 7
    )
    d_poly = 288 * q**2 - 336 * q + 119
    c_poly = 24 * q**3 - 42 * q**2 + 28 * q - 7
    n_poly = (
        5184 * q**6
        - 18144 * q**5
        + 28602 * q**4
        - 25802 * q**3
        + 13874 * q**2
        - 4165 * q
        + 539
    )
    sos = (
        6 * (lam**2 + (q - sp.Rational(7, 12)) * lam) ** 2
        + d_poly / 24 * (lam + 12 * c_poly / d_poly) ** 2
        + n_poly / d_poly
    )
    check("C7 univariate SOS identity", sp.factor(p_poly - sos) == 0)

    y = sp.symbols("y")
    check(
        "C7 positivity form for D(q)",
        sp.expand(d_poly.subs(q, sp.Rational(1, 2) - y) - (288 * y**2 + 48 * y + 23))
        == 0,
    )
    check(
        "C7 positivity form for N(q)",
        sp.expand(
            8 * n_poly.subs(q, sp.Rational(1, 2) - y)
            - (
                41472 * y**6
                + 20736 * y**5
                + 21456 * y**4
                + 7984 * y**3
                + 2032 * y**2
                + 316 * y
                + 11
            )
        )
        == 0,
    )

    # Forced variance and chart algebra.
    alpha = sp.symbols("alpha")
    forced = alpha**2 * (1 - 2 * alpha) + alpha * (alpha - q) ** 2 - q * (1 - q) * (1 - 2 * alpha)
    check(
        "forced-variance factorization",
        sp.expand(forced - (1 - alpha - q) * (alpha**2 + q * alpha - q)) == 0,
    )

    zeta, v = sp.symbols("zeta v", positive=True)
    h_chart = zeta + 1 + v
    u_expr = v / h_chart
    a_expr = (zeta + 1) / h_chart
    ell2_expr = zeta * v / h_chart
    q_expr = v**2 + v * zeta + 2 * v + 2 * zeta + 2
    d_expr = 1 + a_expr**2 + ell2_expr
    check(
        "chart D-Q identity",
        sp.factor(d_expr - (zeta + 1) * q_expr / h_chart**2) == 0,
    )
    check(
        "chart H identity",
        sp.expand(
            zeta * h_chart**2
            - (zeta + 1) * (zeta + v) ** 2
            - (zeta**2 + zeta - v**2)
        )
        == 0,
    )

    # Derivative identities in the linear branch.
    x = sp.symbols("x")
    h_fun = (1 - x) * (1 - x + x**2) * (1 + x**2) ** 5 / x**2
    s_poly = 11 * x**5 - 20 * x**4 + 19 * x**3 - 8 * x**2 - 2 * x + 2
    check(
        "high-zeta derivative identity",
        sp.factor(sp.diff(h_fun, x) + (1 + x**2) ** 4 * s_poly / x**3) == 0,
    )

    n = sp.symbols("N", positive=True)
    k_fun = (n + 2) / n * (1 - x) ** 2 * (1 + x**3) * (1 + x**2) ** (sp.Rational(3, 4) * n - 1)
    p_n = (
        3 * n * x**5
        - 3 * n * x**4
        + 3 * n * x**2
        - 3 * n * x
        + 6 * x**5
        - 2 * x**4
        + 10 * x**3
        - 6 * x**2
        + 4 * x
        + 4
    )
    check(
        "growth-lemma logarithmic derivative",
        sp.simplify(
            sp.diff(sp.log(k_fun), x)
            + p_n / (2 * (1 - x) * (1 + x**2) * (1 + x**3))
        )
        == 0,
    )

    # Small-v squared identity for N=7.
    vv = sp.symbols("v", nonnegative=True)
    left = (1 + vv) ** 7 / ((1 + 2 * vv) * sp.sqrt(1 + vv / 2))
    right = (1 - sp.Rational(7, 8) * vv) * (1 + 5 * vv + 11 * vv**2)
    positive_poly = (
        128 * vv**13
        + 1792 * vv**12
        + 11648 * vv**11
        + 46592 * vv**10
        + 128128 * vv**9
        + 232540 * vv**8
        + 345884 * vv**7
        + 492971 * vv**6
        + 464196 * vv**5
        + 258097 * vv**4
        + 86924 * vv**3
        + 18035 * vv**2
        + 2254 * vv
        + 160
    )
    check(
        "m=9 small-v squared identity",
        sp.factor(
            left**2
            - right**2
            - vv * positive_poly / (128 * (1 + 2 * vv) ** 2 * (1 + vv / 2))
        )
        == 0,
    )

    # Degree-nine Bernstein certificate on [0,1/2].
    s = sp.symbols("s")
    p9 = (
        sp.Rational(10395, 128) * s**9
        - sp.Rational(333333, 2048) * s**8
        + sp.Rational(13635, 128) * s**7
        + sp.Rational(51005, 2048) * s**6
        - sp.Rational(18765, 128) * s**5
        + sp.Rational(264969, 2048) * s**4
        - sp.Rational(4995, 64) * s**3
        + sp.Rational(11913, 256) * s**2
        - sp.Rational(135, 8) * s
        + 3
    )
    p9_expected = [
        sp.Rational(3),
        sp.Rational(33, 16),
        sp.Rational(17795, 12288),
        sp.Rational(29843, 28672),
        sp.Rational(361761, 458752),
        sp.Rational(918263, 1376256),
        sp.Rational(7142309, 11010048),
        sp.Rational(1096445, 1572864),
        sp.Rational(390495, 524288),
        sp.Rational(361511, 524288),
    ]
    p9_actual = bernstein_coefficients(p9, s, sp.Rational(0), sp.Rational(1, 2), 9)
    check("degree-9 Bernstein coefficients", p9_actual == p9_expected)
    check("degree-9 Bernstein positivity", all(coefficient > 0 for coefficient in p9_actual))

    # Degree-ten derivative polynomial and Bernstein certificate on [9/20,5/7].
    yy = sp.symbols("Y")
    q10 = (
        58 * yy**10
        + 319 * yy**9
        - 1793 * yy**8
        - 11280 * yy**7
        + 9788 * yy**6
        - 11354 * yy**5
        + 350 * yy**4
        + 5880 * yy**3
        - 6174 * yy**2
        + 5635 * yy
        - 1029
    )
    v_of_y = 8 * yy**2 / (7 - yy**2)
    ratio = (
        (1 - yy**2)
        * (1 - yy)
        * (1 + v_of_y - yy)
        * (1 + v_of_y) ** 6
        / (6 + 8 * v_of_y)
    )
    denominator = (
        (yy - 1)
        * (yy + 1)
        * (yy**2 - 7)
        * (yy**2 + 1)
        * (29 * yy**2 + 21)
        * (yy**3 + 7 * yy**2 - 7 * yy + 7)
    )
    check(
        "degree-10 logarithmic derivative identity",
        sp.factor(sp.diff(sp.log(ratio), yy) - 2 * q10 / denominator) == 0,
    )
    q10_expected = [
        sp.Rational(3243737479716939, 5120000000000),
        sp.Rational(24439395309190297, 35840000000000),
        sp.Rational(2256629681468091, 3136000000000),
        sp.Rational(653354162075429, 878080000000),
        sp.Rational(3033296182962901, 4033680000000),
        sp.Rational(625950152734243, 847072800000),
        sp.Rational(1151767076423, 1647086000),
        sp.Rational(6182915802683, 9882516000),
        sp.Rational(7481469276, 14706125),
        sp.Rational(67938971678, 201768035),
        sp.Rational(26748047904, 282475249),
    ]
    q10_actual = bernstein_coefficients(
        q10, yy, sp.Rational(9, 20), sp.Rational(5, 7), 10
    )
    check("degree-10 Bernstein coefficients", q10_actual == q10_expected)
    check("degree-10 Bernstein positivity", all(coefficient > 0 for coefficient in q10_actual))

    print("\nAll exact symbolic checks passed.")


if __name__ == "__main__":
    main()
