#!/usr/bin/env python3
"""Exact-rational finite-sweep certifier for `app:constants` (eq:constant-A / -B).

Companion to the Lean formalization in `OddCycleBound/HighDensity/`:

  * `AppConstantsTail.constA_m500`  closes eq:constant-A for m >= 500 uniformly;
  * `AppConstantsTail.constB_m63`   closes eq:constant-B for ALL m >= 63 uniformly;
  * this script closes the remaining eq:constant-A FINITE RANGE 63 <= m <= 499,
    which has no clean uniform bound (P(theta) is non-monotone on (0,1/6], dipping
    to ~51 near theta ~ 0.106 while B0 only exceeds 201/200), so it must be checked
    pair-by-pair.

WHAT IS CERTIFIED.  For each admissible integer pair (m, r) the paper needs
    g(m,r) := 99/(100 m) * P(theta) * B0(theta)^m  >= 1,   theta = r/m,
    P(theta) = (2/3 - 2 theta) / (theta (1/2 - 2 theta)^2),
    B0(theta) = (7/6)^(1-2 theta) * (8 - 24 theta)^(-theta) * (1/2+theta)/(5/12+theta).

CERTIFICATE FORM.  A single SCALAR EXACT-RATIONAL inequality per pair (no SOS, no
LP).  Although B0(theta) is transcendental (fractional powers), B0(r/m)^m is exactly
RATIONAL, because raising to the m-th power turns every fractional exponent into an
integer one:
    ((7/6)^(1-2 theta))^m      = (7/6)^(m-2r)              [m-2r = n, a positive int]
    ((8-24 theta)^(-theta))^m  = (8 - 24 r/m)^(-r) = (m/(8m-24r))^r
    ((1/2+theta)/(5/12+theta))^m rational base ^ integer m.
Hence
    B0(r/m)^m = (7/6)^(m-2r) * (m/(8m-24r))^r * (6(m+2r)/(5m+12r))^m
is an exact rational, and g(m,r) is one explicit (large) rational number to compare
with 1.  All arithmetic below uses `fractions.Fraction`; there is no floating point
in the certification path.  In Lean each pair is discharged by collapsing B0^m via
the integer-power identities (`M6TailRatio.rpow_npow_eq`) and a single `norm_num`
(with `set_option exponentiation.threshold` raised past 500).

ADMISSIBLE PAIRS (residual strip-left, eq:constant-A / case A, theta <= 1/6):
    m odd, 63 <= m <= 499,  r >= 2,  n = m - 2r > 2r  (i.e. 4r < m),  theta = r/m <= 1/6.
For completeness the script also re-verifies case B (theta in (1/6, 1/4)), which the
Lean side already closes uniformly via `constB_m63`.

Run:  python app_constants_finite_sweep.py            # certify + summary
      python app_constants_finite_sweep.py --emit 3   # + sample Lean lemma stubs
"""
from __future__ import annotations

import sys
from fractions import Fraction as F


def P(theta: F) -> F:
    """P(theta) = (2/3 - 2 theta) / (theta (1/2 - 2 theta)^2)  (exact)."""
    return (F(2, 3) - 2 * theta) / (theta * (F(1, 2) - 2 * theta) ** 2)


def B0_pow(m: int, r: int) -> F:
    """B0(r/m)^m as an exact rational via the integer-exponent collapse."""
    theta = F(r, m)
    return (
        F(7, 6) ** (m - 2 * r)
        * (F(8) - 24 * theta) ** (-r)
        * ((F(1, 2) + theta) / (F(5, 12) + theta)) ** m
    )


def B1_pow(m: int, r: int) -> F:
    """B1(r/m)^m as an exact rational (case B; third factor is 34/29)."""
    theta = F(r, m)
    return (
        F(7, 6) ** (m - 2 * r)
        * (F(8) - 24 * theta) ** (-r)
        * F(34, 29) ** m
    )


def ratio_a(m: int, r: int) -> F:
    """g(m,r) = 99/(100 m) * P(theta) * B0(theta)^m  (eq:constant-A, exact)."""
    return F(99, 100 * m) * P(F(r, m)) * B0_pow(m, r)


def ratio_b(m: int, r: int) -> F:
    """eq:constant-B analogue with B1 (exact)."""
    return F(99, 100 * m) * P(F(r, m)) * B1_pow(m, r)


def admissible_r(m: int):
    """Residual strip-left r for a given m:  r >= 2 and 4r < m (so n = m-2r > 2r)."""
    r = 2
    while 4 * r < m:
        yield r
        r += 1


def run_sweep(m_lo: int = 63, m_hi: int = 499):
    """Certify every admissible (m, r); return per-case worst margins and counts."""
    worst_a = worst_b = None
    count_a = count_b = 0
    for m in range(m_lo, m_hi + 1, 2):  # odd m only (step 2 from odd m_lo)
        for r in admissible_r(m):
            theta = F(r, m)
            if theta <= F(1, 6):
                val = ratio_a(m, r)
                assert val >= 1, ("FAIL case A", m, r, float(val))
                count_a += 1
                if worst_a is None or val < worst_a[0]:
                    worst_a = (val, m, r)
            else:  # 1/6 < theta < 1/4
                val = ratio_b(m, r)
                assert val >= 1, ("FAIL case B", m, r, float(val))
                count_b += 1
                if worst_b is None or val < worst_b[0]:
                    worst_b = (val, m, r)
    return worst_a, worst_b, count_a, count_b


def lean_stub(m: int, r: int) -> str:
    """Emit the exact-rational check for pair (m,r) as a Lean `example`.

    This is the scalar the per-pair Lean proof reduces to after collapsing
    B0(r/m)^m via `M6TailRatio.rpow_npow_eq`; here it is stated directly on the
    exact rational value so it is a pure `norm_num` fact.
    """
    val = ratio_a(m, r)
    num, den = val.numerator, val.denominator
    return (
        f"-- eq:constant-A pair (m,r)=({m},{r}), theta={r}/{m}; "
        f"margin g = {float(val):.6f}\n"
        f"example : (1 : ℚ) ≤ {num} / {den} := by norm_num"
    )


def main() -> int:
    try:  # keep Lean unicode (ℚ) printable on Windows consoles
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass
    worst_a, worst_b, count_a, count_b = run_sweep()
    print("[OK] eq:constant-A finite sweep, odd 63 <= m <= 499 (exact rational)")
    print(f"     case A pairs certified : {count_a}")
    print(f"     case B pairs certified : {count_b}")
    print(f"     total admissible pairs : {count_a + count_b}")
    va, ma, ra = worst_a
    vb, mb, rb = worst_b
    print(f"     worst case A margin g  = {float(va):.10f}  at m={ma}, r={ra}")
    print(f"     worst case B margin g  = {float(vb):.10f}  at m={mb}, r={rb}")
    print("     (all g >= 1 verified with exact fractions.Fraction; no floats)")

    if "--emit" in sys.argv:
        i = sys.argv.index("--emit")
        n = int(sys.argv[i + 1]) if i + 1 < len(sys.argv) else 3
        # emit stubs for the n tightest case-A pairs
        pairs = []
        for m in range(63, 500, 2):
            for r in admissible_r(m):
                if F(r, m) <= F(1, 6):
                    pairs.append((ratio_a(m, r), m, r))
        pairs.sort(key=lambda t: t[0])
        print(f"\n-- {n} tightest case-A pairs as Lean `norm_num` stubs:")
        for _, m, r in pairs[:n]:
            print(lean_stub(m, r))

    print("\nAll exact eq:constant-A finite-sweep certificates passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
