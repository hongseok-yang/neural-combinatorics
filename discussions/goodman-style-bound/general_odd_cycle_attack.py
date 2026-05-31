"""
Two general attacks on the odd-cycle Goodman bound.

This is an exploratory checker, not a paper certificate.  It deliberately keeps
the two most promising general approaches separate:

1. Uniform frontier split.  Generalise the C13 proof: in the frontier case
   lambda_max(A)=alpha>q, all other positive modes satisfy
       beta <= sqrt(q(1-2q)).
   The script tests whether the path-certificate quadratic kernel K_2 stays
   positive on that restricted one-frontier domain over the actual
   triangle-spectral gap q <= 1/2-delta_m.

2. Near-bipartite input.  Quantify what the natural two-block near-bipartite
   C5 input can buy.  This tests the conditional spectral closure obtained from
   a hypothetical sharp lower bound
       t(C5,W) >= t(C5,T_2(eps)),
   where T_2(eps) is the equal-halves graphon with cross density 1, one internal
   density 4 eps, and the other internal density 0.

The output is meant to guide the next theorem, not to certify final positivity.
"""

from __future__ import annotations

from functools import lru_cache
import math

import mpmath as mp
import sympy as sp

import odd_cycle_c13_checker as oc


def triangle_density_lower(p: float) -> float:
    eps = p - 0.5
    if eps <= 0:
        return 0.0
    c = (1 - math.sqrt(max(0.0, 1 - 6 * eps))) / 3
    b = (1 - c) / 2
    return 6 * c * b * b


def spectral_delta(m: int, r: int, lower_bound) -> float:
    """First interval [1/2, 1/2+delta] closed by an r-cycle lower input."""

    def margin(eps: float) -> float:
        p = 0.5 + eps
        q = 0.5 - eps
        alpha = (p * q ** (m - 1)) ** (1 / m)
        delta = max(0.0, p * q - alpha * alpha)
        return lower_bound(p) - (p**r - alpha**r + delta ** (r / 2))

    hi = 1 / 6 - 1e-12
    # Use a cubic mesh to avoid missing tiny first roots for large m.  The
    # triangle window is O(m^-2), so a uniform mesh can jump over it.
    mesh = [hi * (i / 30000) ** 3 for i in range(1, 30001)]
    prev_eps = mesh[0]
    prev = margin(prev_eps)
    for eps in mesh[1:]:
        cur = margin(eps)
        if prev >= 0 and cur < 0:
            lo, right = prev_eps, eps
            for _ in range(70):
                mid = (lo + right) / 2
                if margin(mid) >= 0:
                    lo = mid
                else:
                    right = mid
            return lo
        prev_eps, prev = eps, cur
    return hi


def p_linear_value(m: int, q: float, lam: float) -> float:
    total = 0.0
    p = 1 - q
    for j in range(m - 2):
        coeff = (
            ((-1) ** j) * m * p ** (m - 2 - j)
            + m * q ** (m - 2 - j)
            - (m - 2 - j) * q ** (m - 3 - j)
        )
        total += coeff * lam**j
    return total


@lru_cache(maxsize=None)
def k2_kernel(m: int):
    q, s, xs = oc.path_formulae(m - 1)
    target = (1 - q) ** m - (1 - q) * q ** (m - 1)
    phi = sp.expand(oc.expression_from_counts(m, q, xs) - target)
    vars_s = [s[j] for j in range(m - 2)]
    poly = sp.Poly(phi, *vars_s)
    part2 = sp.Integer(0)
    for monom, coeff in poly.terms():
        if sum(monom) == 2:
            part2 += coeff * sp.prod(v ** e for v, e in zip(vars_s, monom))

    moment_syms = sp.symbols(f"m0:{m - 1}")
    subs = {s[0]: 1}
    subs.update({s[j]: moment_syms[j] for j in range(1, m - 2)})
    F2 = sp.expand(part2.subs(subs))
    K2, (x, y) = oc.kernel_for(F2, 2, moment_syms)
    return q, x, y, sp.lambdify((q, x, y), K2, "math")


def scan_frontier_split(m: int, qlo: float = 0.45):
    """Coarse restricted-domain scan for P and K2 in the true triangle gap."""
    delta = spectral_delta(m, 3, triangle_density_lower)
    qhi = 0.5 - delta
    min_p_safe = (float("inf"), None)
    min_p_front = (float("inf"), None)
    min_k2 = (float("inf"), None)

    _, _, _, K2 = k2_kernel(m)
    for iq in range(61):
        q = qlo + (qhi - qlo) * iq / 60
        tau = math.sqrt(max(0.0, q * (1 - 2 * q)))

        for il in range(81):
            lam = -0.5 + (tau + 0.5) * il / 80
            val = p_linear_value(m, q, lam)
            if val < min_p_safe[0]:
                min_p_safe = (val, (q, lam))

        for ia in range(81):
            alpha = q + (0.5 - q) * ia / 80
            val = p_linear_value(m, q, alpha)
            if val < min_p_front[0]:
                min_p_front = (val, (q, alpha))

        for ix in range(41):
            x = -0.5 + (tau + 0.5) * ix / 40
            for iy in range(41):
                y = -0.5 + (tau + 0.5) * iy / 40
                val = K2(q, x, y)
                if val < min_k2[0]:
                    min_k2 = (val, (q, x, y, "safe-safe"))

        for ia in range(41):
            alpha = q + (0.5 - q) * ia / 40
            for iy in range(41):
                y = -0.5 + (tau + 0.5) * iy / 40
                val = K2(q, alpha, y)
                if val < min_k2[0]:
                    min_k2 = (val, (q, alpha, y, "frontier-safe"))
            val = K2(q, alpha, alpha)
            if val < min_k2[0]:
                min_k2 = (val, (q, alpha, alpha, "frontier-frontier diagonal"))

    return {
        "m": m,
        "triangle_delta": delta,
        "qhi": qhi,
        "min_P_safe": min_p_safe,
        "min_P_frontier": min_p_front,
        "min_K2": min_k2,
    }


def two_block_density(p: float, m: int) -> float:
    eps = p - 0.5
    fill = 4 * eps
    M = [[fill / 2, 0.5], [0.5, 0.0]]
    P = [[1.0, 0.0], [0.0, 1.0]]
    for _ in range(m):
        P = [
            [P[0][0] * M[0][0] + P[0][1] * M[1][0], P[0][0] * M[0][1] + P[0][1] * M[1][1]],
            [P[1][0] * M[0][0] + P[1][1] * M[1][0], P[1][0] * M[0][1] + P[1][1] * M[1][1]],
        ]
    return P[0][0] + P[1][1]


def goodman_target(p: float, m: int) -> float:
    q = 1 - p
    return p**m - p * q ** (m - 1)


def scan_near_bipartite_input():
    rows = []
    for m in [13, 15, 17, 19, 21, 23, 31, 51, 101]:
        delta3 = spectral_delta(m, 3, triangle_density_lower)
        delta5 = c5_two_block_delta(m)
        rows.append((m, delta3, delta5))

    large_rows = []
    for m in [501, 1001, 1501, 2001, 5001, 10001, 20001]:
        delta5 = c5_two_block_delta(m)
        large_rows.append((m, delta5, delta5 * (m ** (2 / 3))))

    # Sanity: the two-block family itself satisfies the Goodman target.
    worst = (float("inf"), None)
    for m in [5, 7, 9, 13, 21, 51, 101]:
        for i in range(1, 5001):
            p = 0.5 + (1 / 6) * i / 5000
            val = two_block_density(p, m) - goodman_target(p, m)
            if val < worst[0]:
                worst = (val, (m, p))
    return rows, large_rows, worst


def c5_two_block_density_mp(eps: mp.mpf) -> mp.mpf:
    return eps * (256 * eps**4 + 80 * eps**2 + 5) / 8


def c5_two_block_margin(m: int, eps: mp.mpf) -> mp.mpf:
    """High-precision conditional C5 closure margin."""
    p = mp.mpf("0.5") + eps
    q = mp.mpf("0.5") - eps
    alpha = mp.exp((mp.log(p) + (m - 1) * mp.log(q)) / m)
    delta = p * q - alpha**2
    return c5_two_block_density_mp(eps) - (
        p**5 - alpha**5 + delta ** (mp.mpf(5) / 2)
    )


def c5_two_block_delta(m: int) -> float:
    """First near-bipartite interval closed by the conditional C5 input."""
    mp.mp.dps = 80
    hi = mp.mpf(1) / 6 - mp.mpf("1e-40")
    prev_eps = None
    prev = None
    for i in range(1, 20001):
        eps = hi * (mp.mpf(i) / 20000) ** 3
        cur = c5_two_block_margin(m, eps)
        if prev is not None and prev >= 0 and cur < 0:
            lo, right = prev_eps, eps
            for _ in range(120):
                mid = (lo + right) / 2
                if c5_two_block_margin(m, mid) >= 0:
                    lo = mid
                else:
                    right = mid
            return float(lo)
        prev_eps, prev = eps, cur
    return float(hi)


def symbolic_c5_obstruction():
    eps = sp.symbols("eps", nonnegative=True)
    p = sp.Rational(1, 2) + eps
    q = sp.Rational(1, 2) - eps
    B5 = eps * (256 * eps**4 + 80 * eps**2 + 5) / 8
    limiting_rhs_without_delta = p**5 - q**5
    slack = sp.factor(B5 - limiting_rhs_without_delta)
    return slack


def main() -> None:
    print("Approach 1: uniform frontier split (restricted K2 scan)")
    for m in [13, 15, 17, 19, 21, 23]:
        row = scan_frontier_split(m)
        print(
            f"m={m:2d} q<= {row['qhi']:.6f} "
            f"min P_safe={row['min_P_safe'][0]:+.3e} "
            f"min P_front={row['min_P_frontier'][0]:+.3e} "
            f"min K2={row['min_K2'][0]:+.3e} at {row['min_K2'][1]}"
        )

    print("\nApproach 2: conditional near-bipartite C5 input")
    rows, large_rows, worst = scan_near_bipartite_input()
    for m, delta3, delta5 in rows:
        print(f"m={m:4d} triangle_delta={delta3:.6e}  C5-two-block_delta={delta5:.6e}")
    print("large-m C5-two-block first-window scaling:")
    for m, delta5, scaled in large_rows:
        print(f"m={m:5d} C5-two-block_delta={delta5:.6e}  m^(2/3)delta={scaled:.6f}")
    print(f"two-block family Goodman margin worst={worst[0]:+.3e} at m,p={worst[1]}")
    print("symbolic C5 slack over the m=infinity first part:")
    print(f"  B5(eps) - ((1/2+eps)^5-(1/2-eps)^5) = {symbolic_c5_obstruction()}")


if __name__ == "__main__":
    main()
