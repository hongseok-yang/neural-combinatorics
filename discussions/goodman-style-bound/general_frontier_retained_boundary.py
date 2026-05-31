"""
Diagnostics for the sharpened retained-deletion frontier target.

This script records the useful lesson from the first attempt to prove the
stronger two-mode theorem.  The assertion Phi_m >= 0 is false in the long-cycle
regime, but the retained defect

    D_m = t(C_m, 1-U) - (p^m - p q^(m-1))

still appears positive whenever the deletion gap x_{m-1}-c_m is nonnegative.
The rigorous reduction below is that D_m is coordinatewise nondecreasing in the
coupling weights u_i=b_i^2.  Hence a minimiser of D_m subject to the deletion
constraint must either have zero coupling, or lie on the deletion frontier
x_{m-1}=c_m.  This is the boundary target that replaces the false global
Phi_m >= 0 target.
"""

from __future__ import annotations

import math
import random

from general_frontier_deletion_retaining import evaluate_model, fmt_result, matmul


def mp_witness_values() -> None:
    """Print long-cycle witnesses showing that Phi_m >= 0 is too strong."""
    try:
        import mpmath as mp
    except ImportError:  # pragma: no cover - mpmath is available in our env.
        print("mpmath unavailable; skipping high-precision witnesses")
        return

    mp.mp.dps = 90
    witnesses = [
        (
            301,
            "0.49337514699401697",
            "0.4938347275143707",
            "0.03277517666171813",
            "0.0005512898175625025",
            "0.0018527645404796014",
        ),
        (
            501,
            "0.49077788110738013",
            "0.490783159585619",
            "0.035704861869290345",
            "0.0012677685829113093",
            "0.002483635292065542",
        ),
    ]

    def mat_mul(A, B):
        return [
            [sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))]
            for i in range(len(A))
        ]

    def mat_pow(A, n):
        out = [[mp.mpf(i == j) for j in range(len(A))] for i in range(len(A))]
        base = A
        while n:
            if n & 1:
                out = mat_mul(out, base)
            base = mat_mul(base, base)
            n //= 2
        return out

    print("High-precision witnesses: Phi_m can be negative while the retained defect is positive")
    for m, q_s, alpha_s, beta_s, u_s, v_s in witnesses:
        q, alpha, beta, u, v = map(mp.mpf, (q_s, alpha_s, beta_s, u_s, v_s))
        p = 1 - q
        U = [
            [q, mp.sqrt(u), mp.sqrt(v)],
            [mp.sqrt(u), alpha, 0],
            [mp.sqrt(v), 0, beta],
        ]
        W = [
            [p, -mp.sqrt(u), -mp.sqrt(v)],
            [-mp.sqrt(u), -alpha, 0],
            [-mp.sqrt(v), 0, -beta],
        ]
        c_u = sum(mat_pow(U, m)[i][i] for i in range(3))
        x_path = mat_pow(U, m - 1)[0][0]
        c_w = sum(mat_pow(W, m)[i][i] for i in range(3))
        target = p**m - p * q ** (m - 1)
        gap = x_path - c_u
        defect = c_w - target
        phi = defect - gap
        slack = p * q - alpha**2 - beta**2 - 2 * u - 2 * v
        print(
            f"  m={m}: slack={mp.nstr(slack, 8)}, "
            f"Phi={mp.nstr(phi, 12)}, gap={mp.nstr(gap, 12)}, "
            f"defect={mp.nstr(defect, 12)}"
        )


def sign_flipped_complement(q: float, lambdas: list[float], b2s: list[float]) -> list[list[float]]:
    """Return the complement matrix after flipping leaf signs."""
    p = 1.0 - q
    b = [math.sqrt(max(0.0, b2)) for b2 in b2s]
    M = [[p, *b]]
    for i, lam in enumerate(lambdas):
        row = [b[i]] + [0.0] * len(lambdas)
        row[i + 1] = -lam
        M.append(row)
    return M


def matpow(A: list[list[float]], n: int) -> list[list[float]]:
    out = [[float(i == j) for j in range(len(A))] for i in range(len(A))]
    for _ in range(n):
        out = matmul(out, A)
    return out


def defect_derivative(m: int, q: float, lambdas: list[float], b2s: list[float], i: int) -> float:
    """Derivative of the retained defect with respect to b_i^2."""
    if b2s[i] <= 0:
        raise ValueError("use a positive coupling for the derivative formula")
    N = sign_flipped_complement(q, lambdas, b2s)
    return m * matpow(N, m - 1)[0][i + 1] / math.sqrt(b2s[i])


def derivative_sanity_scan() -> None:
    """Numerically confirm the monotonicity derivative is nonnegative."""
    rng = random.Random(20260531)
    worst = (float("inf"), None)
    for m in [21, 101, 301]:
        for _ in range(2000):
            q = 0.47 + 0.03 * rng.random()
            p = 1 - q
            alpha_hi = min(0.5, math.sqrt(p * q))
            if alpha_hi <= q:
                continue
            alpha = q + (alpha_hi - q) * rng.random()
            rem = p * q - alpha * alpha
            beta = math.sqrt(max(0.0, rem)) * rng.random()
            s0 = 0.5 * max(0.0, rem - beta * beta) * rng.random()
            theta = rng.random()
            b2s = [max(1e-14, theta * s0), max(1e-14, (1 - theta) * s0)]
            for i in range(2):
                val = defect_derivative(m, q, [alpha, beta], b2s, i)
                if val < worst[0]:
                    worst = (val, (m, q, alpha, beta, b2s, i))
    print(f"worst sampled derivative = {worst[0]:+.3e} at {worst[1]}")


def deletion_frontier_scan(samples: int = 2500) -> None:
    """Search Phi_m on the first deletion-gap crossing along random coupling rays."""
    rng = random.Random(20260531)
    for m in [21, 101, 301]:
        best = None
        crossings = 0
        for _ in range(samples):
            q = 0.47 + 0.03 * rng.random()
            p = 1 - q
            alpha_hi = min(0.5, math.sqrt(p * q))
            if alpha_hi <= q:
                continue
            alpha = q + (alpha_hi - q) * rng.random()
            rem = p * q - alpha * alpha
            beta = math.sqrt(max(0.0, rem)) * rng.random()
            s0 = 0.5 * max(0.0, rem - beta * beta) * rng.random()
            theta = rng.random()
            u, v = theta * s0, (1 - theta) * s0
            g0 = evaluate_model(m, q, alpha, beta, 0.0, 0.0).gap
            g1 = evaluate_model(m, q, alpha, beta, u, v).gap
            if not (g0 < 0 <= g1):
                continue
            crossings += 1
            lo, hi = 0.0, 1.0
            for _ in range(35):
                mid = 0.5 * (lo + hi)
                if evaluate_model(m, q, alpha, beta, mid * u, mid * v).gap >= 0:
                    hi = mid
                else:
                    lo = mid
            r = evaluate_model(m, q, alpha, beta, hi * u, hi * v)
            if best is None or r.phi < best.phi:
                best = r
        print(f"m={m}, deletion-frontier crossings={crossings}")
        if best is not None:
            print(f"  best boundary point: {fmt_result(best)}")


def main() -> None:
    mp_witness_values()
    print("\nDerivative sanity scan for the retained defect")
    derivative_sanity_scan()
    print("\nDeletion-frontier scan")
    deletion_frontier_scan()


if __name__ == "__main__":
    main()
