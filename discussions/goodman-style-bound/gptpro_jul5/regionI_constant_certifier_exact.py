#!/usr/bin/env python3
"""Exact rational constant certificate for odd_cycle_high_density_baton.tex.

This script supports the analytic proof of the residual scalar strip in the
high-density region p >= 2/3.  It checks only finite rational inequalities;
there is no floating point arithmetic in the certification path.

Checks:
  (1) The finite integer part of the left-surplus constants for all odd
      63 <= m <= 499 and all residual r.
  (2) The tail inequalities used for m >= 500 in Case A and for all m >= 63
      in Case B after applying the uniform base bounds.
  (3) The twelve-subinterval rational-power proof of the uniform lower bound
      B_1(theta) >= 126/125 on theta in [1/6, 1/4].
"""
from __future__ import annotations
from fractions import Fraction as F
from math import gcd


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def pref(theta: F) -> F:
    return (F(2, 3) - 2 * theta) / (theta * (F(1, 2) - 2 * theta) ** 2)


def ratio_case_a(m: int, r: int) -> F:
    theta = F(r, m)
    Bpow = (F(7, 6) ** (m - 2 * r))
    Bpow *= (F(8) - 24 * theta) ** (-r)
    Bpow *= ((F(1, 2) + theta) / (F(5, 12) + theta)) ** m
    return F(99, 100 * m) * pref(theta) * Bpow


def ratio_case_b(m: int, r: int) -> F:
    theta = F(r, m)
    Bpow = (F(7, 6) ** (m - 2 * r))
    Bpow *= (F(8) - 24 * theta) ** (-r)
    Bpow *= F(34, 29) ** m
    return F(99, 100 * m) * pref(theta) * Bpow


def check_finite_integer_range() -> None:
    worst_a = None
    worst_b = None
    for m in range(63, 500, 2):
        for r in range(2, (m - 1) // 4 + 1):
            if m - 2 * r <= 2 * r:
                continue
            theta = F(r, m)
            if theta <= F(1, 6):
                val = ratio_case_a(m, r)
                assert val >= 1, ("case A", m, r, val)
                if worst_a is None or val < worst_a[0]:
                    worst_a = (val, m, r)
            else:
                val = ratio_case_b(m, r)
                assert val >= 1, ("case B", m, r, val)
                if worst_b is None or val < worst_b[0]:
                    worst_b = (val, m, r)
    print("[OK] finite integer constants, odd 63 <= m <= 499")
    print(f"     worst case A = {float(worst_a[0]):.12g} at m={worst_a[1]}, r={worst_a[2]}")
    print(f"     worst case B = {float(worst_b[0]):.12g} at m={worst_b[1]}, r={worst_b[2]}")


def check_tail_bounds() -> None:
    # Case A tail: pref >= 51, B0 >= 201/200, and b^m/m increases for m >= 200.
    val_a = F(99, 100) * F(51, 500) * (F(201, 200) ** 500)
    assert val_a > 1, val_a
    # Case B: pref >= 72, B1 >= 126/125, and b^m/m has its minimum for m >= 63
    # at m=125 or m=126; checking m=125 is enough.
    val_b = F(99, 100) * F(72, 125) * (F(126, 125) ** 125)
    assert val_b > 1, val_b
    print("[OK] exact tail constants")
    print(f"     case A tail lower ratio at m=500: {float(val_a):.12g}")
    print(f"     case B tail lower ratio at m=125: {float(val_b):.12g}")


def check_B1_uniform_bound() -> None:
    # On interval [a,b], for theta in [a,b],
    # B1(theta) = (7/6)^(1-2theta) (8-24theta)^(-theta) (34/29)
    # is bounded below by
    # (7/6)^(1-2b) (8-24a)^(-b) (34/29).
    # Split [1/6,1/4] into twelve intervals of length 1/144 and prove that
    # each lower bound is at least 126/125.  Since exponents are rational, we
    # raise to a common denominator and compare exact rationals.
    worst = None
    for i in range(12):
        a = F(1, 6) + F(i, 144)
        b = F(1, 6) + F(i + 1, 144)
        e1 = 1 - 2 * b
        e2 = b
        D = lcm(e1.denominator, e2.denominator)
        lhs = F(7, 6) ** (e1.numerator * (D // e1.denominator))
        lhs *= F(34, 29) ** D
        rhs = F(126, 125) ** D
        rhs *= (F(8) - 24 * a) ** (e2.numerator * (D // e2.denominator))
        assert lhs >= rhs, (i, a, b, lhs, rhs)
        ratio = lhs / rhs
        if worst is None or ratio < worst[0]:
            worst = (ratio, i, a, b)
    print("[OK] uniform bound B1(theta) >= 126/125 on [1/6,1/4]")
    print(f"     worst powered ratio = {float(worst[0]):.12g} on interval {worst[1]} [{worst[2]}, {worst[3]}]")


def main() -> None:
    check_finite_integer_range()
    check_tail_bounds()
    check_B1_uniform_bound()
    print("\nAll exact constant certificates passed.")


if __name__ == "__main__":
    main()
