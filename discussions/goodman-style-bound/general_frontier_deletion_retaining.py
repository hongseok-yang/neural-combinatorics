"""
Deletion-retaining one-frontier diagnostics for general odd cycles.

This is an exploratory script.  It starts from the first obstruction found by
general_odd_cycle_attack.py: for m=21 and m=23 the deletion-free quadratic
kernel K_2 is negative on the one-frontier spectral domain.

The new point here is to keep two pieces of information that the rectangular
K_2 scan discards:

  * the sharp trace-square/coupling budget
        alpha^2 + beta^2 + 2 ||g||^2 <= p q,
    for a two-mode model A = diag(alpha, beta);

  * the exact deletion gap
        x_{m-1} - c_m = t(P_{m-1}, U) - t(C_m, U).

For a finite spectral arrowhead

        T_U = [[q, b_1, b_2],
               [b_1, alpha, 0],
               [b_2, 0, beta]],

the true Goodman defect for W=1-U satisfies

        defect = Phi_m + (x_{m-1} - c_m),

where Phi_m is the deletion-free path certificate.  The script scans feasible
two-mode one-frontier models and reports whether Phi_m or the true defect can
become negative once the coupling budget and deletion term are retained.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
import math

from general_odd_cycle_attack import k2_kernel, spectral_delta, triangle_density_lower


@dataclass
class ModelResult:
    m: int
    q: float
    alpha: float
    beta: float
    b_front2: float
    b_safe2: float
    phi: float
    gap: float
    defect: float
    k2: float | None = None

    @property
    def s0(self) -> float:
        return self.b_front2 + self.b_safe2

    @property
    def budget_slack(self) -> float:
        p = 1 - self.q
        return p * self.q - self.alpha**2 - self.beta**2 - 2 * self.s0


def matmul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    out = [[0.0] * p for _ in range(n)]
    for i in range(n):
        for k in range(m):
            aik = A[i][k]
            if aik:
                for j in range(p):
                    out[i][j] += aik * B[k][j]
    return out


def trace_power(A, power: int) -> float:
    n = len(A)
    P = [[float(i == j) for j in range(n)] for i in range(n)]
    for _ in range(power):
        P = matmul(P, A)
    return sum(P[i][i] for i in range(n))


def path_density(q: float, lambdas: list[float], b2s: list[float], n: int) -> float:
    b = [math.sqrt(max(0.0, b2)) for b2 in b2s]
    a = 1.0
    h = [0.0] * len(lambdas)
    for _ in range(n):
        a_new = q * a + sum(bi * hi for bi, hi in zip(b, h))
        h = [bi * a + lam * hi for bi, lam, hi in zip(b, lambdas, h)]
        a = a_new
    return a


def arrowhead(q: float, lambdas: list[float], b2s: list[float], complement: bool):
    b = [math.sqrt(max(0.0, b2)) for b2 in b2s]
    if complement:
        top = 1 - q
        signs = [-bi for bi in b]
        diag = [-lam for lam in lambdas]
    else:
        top = q
        signs = b
        diag = lambdas

    M = [[top, *signs]]
    for i, lam in enumerate(diag):
        row = [signs[i]] + [0.0] * len(lambdas)
        row[i + 1] = lam
        M.append(row)
    return M


def evaluate_model(
    m: int,
    q: float,
    alpha: float,
    beta: float,
    b_front2: float,
    b_safe2: float,
    k2_func=None,
) -> ModelResult:
    lambdas = [alpha, beta]
    b2s = [b_front2, b_safe2]
    p = 1 - q
    target = p**m - p * q ** (m - 1)

    x_path = path_density(q, lambdas, b2s, m - 1)
    c_u = trace_power(arrowhead(q, lambdas, b2s, complement=False), m)
    gap = x_path - c_u
    defect = trace_power(arrowhead(q, lambdas, b2s, complement=True), m) - target
    phi = defect - gap
    k2 = None if k2_func is None else k2_func(q, alpha, beta)
    return ModelResult(m, q, alpha, beta, b_front2, b_safe2, phi, gap, defect, k2)


def fmt_result(r: ModelResult) -> str:
    k2 = "" if r.k2 is None else f", K2={r.k2:+.3e}"
    return (
        f"q={r.q:.9f}, alpha={r.alpha:.9f}, beta={r.beta:.9f}, "
        f"b_front^2={r.b_front2:.3e}, b_safe^2={r.b_safe2:.3e}, "
        f"s0={r.s0:.3e}, slack={r.budget_slack:.3e}, "
        f"Phi={r.phi:+.3e}, gap={r.gap:+.3e}, defect={r.defect:+.3e}{k2}"
    )


@lru_cache(maxsize=None)
def q_window_top(m: int) -> float:
    return 0.5 - spectral_delta(m, 3, triangle_density_lower)


def scan_two_mode_budget(m: int) -> dict[str, ModelResult]:
    """Coarse scan of feasible two-mode one-frontier arrowheads."""
    qhi = q_window_top(m)
    qlo = max(0.47, qhi - 0.018)
    k2_func = k2_kernel(m)[3]

    best_phi = None
    best_defect = None
    best_negative_k2 = None
    best_gap_rescue = None
    best_phi_gap_nonnegative = None
    best_defect_gap_nonnegative = None
    best_negative_k2_gap_nonnegative = None
    best_active_negative_k2_gap_nonnegative = None
    tol = 1e-12
    active_tol = 1e-9

    for iq in range(9):
        q = qlo + (qhi - qlo) * iq / 8
        p = 1 - q
        alpha_hi = min(0.5, math.sqrt(p * q))
        if alpha_hi <= q:
            continue
        for ia in range(1, 17):
            alpha = q + (alpha_hi - q) * ia / 16
            beta_hi2 = p * q - alpha * alpha
            if beta_hi2 <= 0:
                continue
            beta_hi = math.sqrt(beta_hi2)
            for ib in range(0, 17):
                beta = beta_hi * ib / 16
                residual = p * q - alpha * alpha - beta * beta
                if residual < -1e-15:
                    continue
                s0_max = max(0.0, residual / 2)
                for scale in [0.0, 0.05, 0.15, 0.35, 0.65, 1.0]:
                    s0 = scale * s0_max
                    for theta in [0.0, 0.25, 0.5, 0.75, 1.0]:
                        r = evaluate_model(
                            m,
                            q,
                            alpha,
                            beta,
                            theta * s0,
                            (1 - theta) * s0,
                            k2_func,
                        )
                        if best_phi is None or r.phi < best_phi.phi:
                            best_phi = r
                        if best_defect is None or r.defect < best_defect.defect:
                            best_defect = r
                        if r.k2 is not None and r.k2 < 0:
                            if best_negative_k2 is None or r.k2 < best_negative_k2.k2:
                                best_negative_k2 = r
                            if r.phi < -tol and r.defect >= -tol:
                                if best_gap_rescue is None or r.phi < best_gap_rescue.phi:
                                    best_gap_rescue = r
                        if r.gap >= -tol:
                            if best_phi_gap_nonnegative is None or r.phi < best_phi_gap_nonnegative.phi:
                                best_phi_gap_nonnegative = r
                            if (
                                best_defect_gap_nonnegative is None
                                or r.defect < best_defect_gap_nonnegative.defect
                            ):
                                best_defect_gap_nonnegative = r
                            if r.k2 is not None and r.k2 < 0:
                                if (
                                    best_negative_k2_gap_nonnegative is None
                                    or r.k2 < best_negative_k2_gap_nonnegative.k2
                                ):
                                    best_negative_k2_gap_nonnegative = r
                                if r.b_front2 > active_tol and r.b_safe2 > active_tol:
                                    if (
                                        best_active_negative_k2_gap_nonnegative is None
                                        or r.k2 < best_active_negative_k2_gap_nonnegative.k2
                                    ):
                                        best_active_negative_k2_gap_nonnegative = r

    return {
        "best_phi": best_phi,
        "best_defect": best_defect,
        "best_negative_k2": best_negative_k2,
        "best_gap_rescue": best_gap_rescue,
        "best_phi_gap_nonnegative": best_phi_gap_nonnegative,
        "best_defect_gap_nonnegative": best_defect_gap_nonnegative,
        "best_negative_k2_gap_nonnegative": best_negative_k2_gap_nonnegative,
        "best_active_negative_k2_gap_nonnegative": best_active_negative_k2_gap_nonnegative,
    }


def feasible_boundary_probe(m: int) -> None:
    """Print K2 on the sharp beta^2=pq-alpha^2 boundary near the old obstruction."""
    q = q_window_top(m)
    k2_func = k2_kernel(m)[3]
    print(f"\nSharp square-budget K2 boundary, m={m}, q={q:.9f}")
    for da in [0.0, 1e-6, 1e-5, 1e-4, 1e-3, 2e-3, 4e-3]:
        alpha = q + da
        beta2 = q * (1 - q) - alpha * alpha
        if beta2 < 0:
            continue
        beta = math.sqrt(beta2)
        print(
            f"  alpha-q={da:.1e}, beta={beta:.9f}, "
            f"K2={k2_func(q, alpha, beta):+.6e}"
        )


def coupling_profile(m: int) -> None:
    """Follow Phi + deletion gap along a negative-K2 feasible ray."""
    q = q_window_top(m)
    alpha = q + 1e-3
    beta_max = math.sqrt(max(0.0, q * (1 - q) - alpha * alpha))
    beta = 0.8 * beta_max
    residual = q * (1 - q) - alpha * alpha - beta * beta
    s0_max = max(0.0, residual / 2)
    theta = 0.5
    k2_func = k2_kernel(m)[3]
    print(f"\nCoupling profile on a negative-K2 feasible ray, m={m}")
    print(
        f"  q={q:.9f}, alpha={alpha:.9f}, beta={beta:.9f}, "
        f"s0_max={s0_max:.3e}, K2={k2_func(q, alpha, beta):+.6e}"
    )
    for scale in [0.0, 0.05, 0.15, 0.35, 0.65, 1.0]:
        s0 = scale * s0_max
        r = evaluate_model(m, q, alpha, beta, theta * s0, (1 - theta) * s0)
        print(f"  scale={scale:>4.2f}: {fmt_result(r)}")


def main() -> None:
    print("Deletion-retaining one-frontier diagnostics")
    for m in [21, 23]:
        feasible_boundary_probe(m)
        coupling_profile(m)
        scan = scan_two_mode_budget(m)
        print(f"\nCoarse feasible two-mode scan, m={m}")
        for name, result in scan.items():
            if result is None:
                print(f"  {name}: none")
            else:
                print(f"  {name}: {fmt_result(result)}")


if __name__ == "__main__":
    main()
