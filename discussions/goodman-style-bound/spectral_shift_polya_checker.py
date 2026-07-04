#!/usr/bin/env python3
"""
Fast exact Polya-coefficient checker for the rank-one frontier certificate.

This script accompanies spectral_shift_baton_note.tex.  It verifies the
coefficient-polynomial target

    P_{m,r}(q,lambda) >= 0 on 0 <= q <= lambda <= 1/2

for the listed odd m.  The variables are transformed to barycentric
coordinates

    x = 2q,  y = 2(lambda-q),  z = 1-2lambda,

so x,y,z >= 0 and x+y+z = 1.  For each pair (m,r), the script constructs a
homogeneous integer multiple of the barycentric form H_{m,r}(x,y,z).  A Polya
certificate is found by checking that all coefficients of

    (x+y+z)^N H_{m,r}(x,y,z)

are nonnegative.  The arithmetic is exact over the integers.  The integer
multiple used is positive, so it does not affect nonnegativity.

The default table verifies all odd m <= 43.  Use --max-m to stop earlier.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from math import comb
from typing import Dict, Tuple

Monomial = Tuple[int, int, int]
Poly = Dict[Monomial, int]


def mul_poly(a: Poly, b: Poly) -> Poly:
    out: defaultdict[Monomial, int] = defaultdict(int)
    for (i, j, k), c in a.items():
        for (i2, j2, k2), d in b.items():
            out[(i + i2, j + j2, k + k2)] += c * d
    return {mon: coeff for mon, coeff in out.items() if coeff}


def pow_sum(n: int) -> Poly:
    """Return (x+y+z)^n."""
    out: Poly = {}
    for i in range(n + 1):
        for j in range(n - i + 1):
            k = n - i - j
            out[(i, j, k)] = comb(n, i) * comb(n - i, j)
    return out


SUM_POW = [pow_sum(n) for n in range(128)]


def linear_power(coeffs: Tuple[int, int, int], n: int) -> Poly:
    """Return (a*x+b*y+c*z)^n for integer coefficients a,b,c."""
    a, b, c = coeffs
    out: Poly = {}
    for i in range(n + 1):
        for j in range(n - i + 1):
            k = n - i - j
            coeff = comb(n, i) * comb(n - i, j) * (a**i) * (b**j) * (c**k)
            if coeff:
                out[(i, j, k)] = coeff
    return out


def monomial_scaled_q_lambda_p(i: int, j: int, k: int) -> Poly:
    """Return 2^(i+j+k) q^i lambda^j p^k in barycentric variables.

    On the simplex,
        q = x/2,
        lambda = (x+y)/2,
        p = 1-q = (x+2y+2z)/2.
    Therefore the scaled monomial is
        x^i (x+y)^j (x+2y+2z)^k.
    """
    poly: Poly = {(0, 0, 0): 1}
    if i:
        poly = mul_poly(poly, {(i, 0, 0): 1})
    if j:
        poly = mul_poly(poly, linear_power((1, 1, 0), j))
    if k:
        poly = mul_poly(poly, linear_power((1, 2, 2), k))
    return poly


def add_scaled(out: defaultdict[Monomial, int], poly: Poly, scale: int) -> None:
    if scale == 0:
        return
    for mon, coeff in poly.items():
        out[mon] += scale * coeff


def coefficient_polynomial_scaled(m: int, r: int) -> Poly:
    """Return a positive integer multiple of H_{m,r}.

    More precisely, if n=m-2r, this returns r*2^n*H_{m,r}, where H_{m,r}
    is the homogeneous barycentric form of P_{m,r}.  This clears all
    denominators and the factor m/r in the definition of P_{m,r}.
    """
    if not (m % 2 == 1 and m >= 5 and 1 <= r <= m // 2):
        raise ValueError("expected odd m>=5 and 1<=r<=floor(m/2)")
    n = m - 2 * r
    out: defaultdict[Monomial, int] = defaultdict(int)

    # A = [z^n] (1-pz)^(-r) (1+lambda z)^(-r).
    for i in range(n + 1):
        j = n - i
        coeff = comb(r + i - 1, i) * comb(r + j - 1, j) * ((-1) ** j)
        add_scaled(out, monomial_scaled_q_lambda_p(0, j, i), m * coeff)

    # B = [z^n] (1-qz)^(-r) (1-lambda z)^(-r).
    for i in range(n + 1):
        j = n - i
        coeff = comb(r + i - 1, i) * comb(r + j - 1, j)
        add_scaled(out, monomial_scaled_q_lambda_p(i, j, 0), m * coeff)

    # C = [z^{n-1}] (1-qz)^(-(r+1)) (1-lambda z)^(-r), homogenised
    # by multiplying by x+y+z.  Since C has degree n-1, r*2^n*C_h
    # equals 2r times the degree-(n-1) scaled polynomial times (x+y+z).
    if n - 1 >= 0:
        temp: defaultdict[Monomial, int] = defaultdict(int)
        for i in range(n):
            j = n - 1 - i
            coeff = comb(r + i, i) * comb(r + j - 1, j)
            add_scaled(temp, monomial_scaled_q_lambda_p(i, j, 0), coeff)
        temp_homogeneous = mul_poly(dict(temp), SUM_POW[1])
        add_scaled(out, temp_homogeneous, -2 * r)

    return {mon: coeff for mon, coeff in out.items() if coeff}


def polya_certificate_nonnegative(poly: Poly, exponent: int) -> bool:
    certified = mul_poly(poly, SUM_POW[exponent]) if exponent else poly
    return all(coeff >= 0 for coeff in certified.values())


# Sufficient exponents found by exact search.  They need not be minimal.
POLYA_EXPONENT = {
    5: 0,
    7: 0,
    9: 1,
    11: 1,
    13: 2,
    15: 2,
    17: 3,
    19: 4,
    21: 5,
    23: 6,
    25: 7,
    27: 8,
    29: 9,
    31: 11,
    33: 13,
    35: 14,
    37: 16,
    39: 17,
    41: 19,
    43: 20,
}


def main() -> None:
    parser = argparse.ArgumentParser(description="Exact Polya checker for rank-one frontier coefficient positivity.")
    parser.add_argument("--max-m", type=int, default=max(POLYA_EXPONENT), help="largest odd m to verify, default 43")
    args = parser.parse_args()

    selected = [(m, n) for m, n in POLYA_EXPONENT.items() if m <= args.max_m]
    if not selected:
        raise SystemExit("No stored Polya exponents at or below --max-m")

    for m, exponent in selected:
        for r in range(1, m // 2 + 1):
            poly = coefficient_polynomial_scaled(m, r)
            if not polya_certificate_nonnegative(poly, exponent):
                raise AssertionError(f"Polya certificate failed for m={m}, r={r}, N={exponent}")
        print(f"m={m}: verified with N={exponent}", flush=True)
    print("All selected rank-one frontier coefficient certificates verified exactly.")


if __name__ == "__main__":
    main()
