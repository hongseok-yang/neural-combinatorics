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


# --------------------------------------------------------------------------- #
#  Lean code generation for the per-m sweep tree                              #
#                                                                             #
#  Layout (all under OddCycleBound/HighDensity/Sweep/):                        #
#    Core.lean       -- hand-written (gRatA + constA_B0pow_eq + constA_of_gRatA)
#    M<mmm>.lean      -- GENERATED, one lemma `constA_m<m>` per odd m in 63..499 #
#    Aggregate.lean   -- GENERATED, `interval_cases m` dispatch -> constA_finite #
#                                                                             #
#  Per-m admissible case-A r-range: 2 <= r <= m//6  (theta = r/m <= 1/6; for   #
#  odd m this is exactly 6r < m and, since 4r < 6r < m, also n = m-2r > 2r).   #
# --------------------------------------------------------------------------- #

M_LO, M_HI = 63, 499


def sweep_odd_ms():
    return range(M_LO, M_HI + 1, 2)


def r_max(m: int) -> int:
    """Largest admissible case-A r for m: r <= m//6 (theta = r/m <= 1/6)."""
    return m // 6


def module_name(m: int) -> str:
    return f"M{m:03d}"


def emit_module(m: int) -> str:
    """The GENERATED per-m file `M<mmm>.lean` proving `constA_m<m>`."""
    rmax = r_max(m)
    return f"""/-
# `eq:constant-A` finite sweep — m = {m}  (GENERATED by app_constants_finite_sweep.py; do not hand-edit)

One lemma `constA_m{m}` covering every admissible case-A pair `({m}, r)` (`2 <= r`, `6r < {m}`,
i.e. `theta = r/{m} <= 1/6`), each discharged by `norm_num` on the exact-rational collapsed value
`gRatA {m} r`.
-/

import OddCycleBound.HighDensity.Sweep.Core

namespace OddCycleBound.HighDensity

set_option exponentiation.threshold 600 in
/-- `eq:constant-A` for every admissible case-A pair `({m}, r)`. -/
theorem constA_m{m} {{r : ℕ}} (hr2 : 2 ≤ r) (h6r : 6 * r < {m}) : 1 ≤ gRatA {m} r := by
  have hub : r ≤ {rmax} := by omega
  interval_cases r <;> norm_num [gRatA]

end OddCycleBound.HighDensity
"""


def emit_aggregate(m_lo: int = M_LO, m_hi: int = M_HI) -> str:
    """The GENERATED `Aggregate.lean`: dispatch `constA_finite` over the whole band."""
    imports = "\n".join(
        f"import OddCycleBound.HighDensity.Sweep.{module_name(m)}"
        for m in range(m_lo, m_hi + 1, 2)
    )
    # one bullet per m in [m_lo, m_hi]; odd -> per-m lemma, even -> impossible by hodd
    bullets = []
    for m in range(m_lo, m_hi + 1):
        if m % 2 == 1:
            bullets.append(f"  · exact constA_m{m} hr2 h6r")
        else:
            bullets.append("  · exact absurd hodd (by decide)")
    bullet_block = "\n".join(bullets)
    return f"""/-
# `eq:constant-A` finite sweep — aggregate dispatch  (GENERATED; do not hand-edit)

Bundles every per-m lemma `constA_m<m>` into the single `constA_finite`: for odd `m` in
`[{m_lo}, {m_hi}]` and every admissible case-A pair, `1 <= gRatA m r`.  `constA_finite_B0` then
lifts it to `eq:constant-A` in `B0` form (matching `constA_m500`) via `constA_of_gRatA`.
-/

{imports}

namespace OddCycleBound.HighDensity

/-- **`eq:constant-A` finite sweep, rational form.**  For odd `m` in `[{m_lo}, {m_hi}]`, `2 ≤ r`,
`6r < m` (`θ = r/m ≤ 1/6`), the collapsed rational target satisfies `1 ≤ gRatA m r`. -/
theorem constA_finite {{m r : ℕ}} (hodd : m % 2 = 1) (hm63 : {m_lo} ≤ m) (hm499 : m ≤ {m_hi})
    (hr2 : 2 ≤ r) (h6r : 6 * r < m) : 1 ≤ gRatA m r := by
  interval_cases m
{bullet_block}

/-- **`eq:constant-A` finite sweep, `B₀` form** (matches `constA_m500`).  For odd `m` in
`[{m_lo}, {m_hi}]` and every admissible case-A pair, `(99/(100m))·P(θ)·B₀(θ)^m ≥ 1`. -/
theorem constA_finite_B0 {{m r : ℕ}} (hodd : m % 2 = 1) (hm63 : {m_lo} ≤ m) (hm499 : m ≤ {m_hi})
    (hr2 : 2 ≤ r) (h6r : 6 * r < m) :
    1 ≤ 99 / (100 * (m : ℝ))
        * ((2 / 3 - 2 * ((r : ℝ) / m)) / (((r : ℝ) / m) * (1 / 2 - 2 * ((r : ℝ) / m)) ^ 2))
        * (B0 ((r : ℝ) / m)) ^ m :=
  constA_of_gRatA (by omega) h6r (constA_finite hodd hm63 hm499 hr2 h6r)

end OddCycleBound.HighDensity
"""


def generate(outdir: str, m_lo: int = M_LO, m_hi: int = M_HI) -> None:
    import os

    os.makedirs(outdir, exist_ok=True)
    for m in range(m_lo, m_hi + 1, 2):
        with open(os.path.join(outdir, f"{module_name(m)}.lean"), "w",
                  encoding="utf-8", newline="\n") as fh:
            fh.write(emit_module(m))
    with open(os.path.join(outdir, "Aggregate.lean"), "w",
              encoding="utf-8", newline="\n") as fh:
        fh.write(emit_aggregate(m_lo, m_hi))
    n_files = len(range(m_lo, m_hi + 1, 2))
    print(f"[gen] wrote {n_files} per-m modules + Aggregate.lean to {outdir}")


def main() -> int:
    try:  # keep Lean unicode (ℚ) printable on Windows consoles
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass
    if "--gen" in sys.argv:
        i = sys.argv.index("--gen")
        outdir = sys.argv[i + 1]
        lo = int(sys.argv[i + 2]) if i + 2 < len(sys.argv) and sys.argv[i + 2].isdigit() else M_LO
        hi = int(sys.argv[i + 3]) if i + 3 < len(sys.argv) and sys.argv[i + 3].isdigit() else M_HI
        # certify the exact range being generated before emitting
        run_sweep(lo, hi)
        generate(outdir, lo, hi)
        return 0
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
