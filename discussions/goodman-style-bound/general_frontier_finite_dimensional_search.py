"""
Search the finite-dimensional deletion-retaining frontier target.

Target, for one frontier atom alpha and one safe positive atom beta:

    alpha > q,
    beta^2 + alpha^2 + 2(u+v) <= p q,
    x_{m-1} - c_m >= 0
        ==>  t(C_m,1-U) - (p^m - p q^{m-1}) >= 0.

The previous script general_frontier_deletion_retaining.py found that the raw
K_2 kernel is negative for m=21,23, but coarse graphon-like scans with the
deletion gap retained stayed positive.  This script pushes that test harder via
a normalized five-variable search and coordinate refinement.

This is still exploratory: it searches for counter-diagnostics and tight
points, not a formal certificate.
"""

from __future__ import annotations

from dataclasses import dataclass
import math
import random

from general_frontier_deletion_retaining import ModelResult, evaluate_model, fmt_result, q_window_top


@dataclass
class SearchResult:
    z: list[float]
    result: ModelResult


def clamp01(x: float) -> float:
    return 0.0 if x < 0.0 else 1.0 if x > 1.0 else x


def window(m: int) -> tuple[float, float]:
    qhi = q_window_top(m)
    qlo = max(0.47, qhi - 0.018)
    return qlo, qhi


def decode(m: int, z: list[float], qlo: float | None = None, qhi: float | None = None) -> ModelResult:
    """Map [0,1]^5 to the sharp square-budget feasible arrowhead box."""
    if qlo is None or qhi is None:
        qlo, qhi = window(m)
    # Bias is handled by the sampler; decode itself is affine in z[0].
    q = qlo + (qhi - qlo) * z[0]
    p = 1 - q
    alpha_hi = min(0.5, math.sqrt(max(0.0, p * q)))
    alpha = q + (alpha_hi - q) * z[1]
    beta_budget = max(0.0, p * q - alpha * alpha)
    beta = math.sqrt(beta_budget) * z[2]
    residual = max(0.0, beta_budget - beta * beta)
    s0 = 0.5 * residual * z[3]
    u = z[4] * s0
    v = (1 - z[4]) * s0
    return evaluate_model(m, q, alpha, beta, u, v)


def penalty_score(r: ModelResult, gap_penalty: float = 1e4) -> float:
    """A soft score for boundary hunting; feasible points use true defect."""
    return r.defect + gap_penalty * max(0.0, -r.gap)


def is_feasible(r: ModelResult, tol: float = 0.0) -> bool:
    return r.gap >= -tol and r.budget_slack >= -1e-12


def is_active(r: ModelResult, tol: float = 1e-9) -> bool:
    return r.b_front2 > tol and r.b_safe2 > tol


def random_z(rng: random.Random) -> list[float]:
    """Bias samples toward the near-bipartite frontier where margins are small."""
    roll = rng.random()
    if roll < 0.55:
        # Near the top q-window, alpha close to q, beta close to its budget.
        return [
            1 - rng.random() ** 3,
            rng.random() ** 2,
            1 - rng.random() ** 2,
            rng.random(),
            rng.random(),
        ]
    if roll < 0.80:
        # Near alpha close to 1/2, where abstract non-graphon spectra misbehave.
        return [
            rng.random(),
            1 - rng.random() ** 3,
            rng.random() ** 2,
            rng.random(),
            rng.random(),
        ]
    return [rng.random() for _ in range(5)]


def coordinate_refine(
    m: int,
    start: list[float],
    objective,
    require_feasible: bool,
    min_active: bool = False,
    rounds: int = 18,
) -> SearchResult:
    qlo, qhi = window(m)
    z = [clamp01(x) for x in start]
    r = decode(m, z, qlo, qhi)
    if require_feasible and (not is_feasible(r) or (min_active and not is_active(r))):
        # Keep the point but make its score unusable until a feasible neighbor appears.
        best_score = float("inf")
    else:
        best_score = objective(r)
    best = SearchResult(z[:], r)

    step = 0.25
    for _ in range(rounds):
        improved = False
        for i in range(5):
            for sign in (-1, 1):
                cand = z[:]
                cand[i] = clamp01(cand[i] + sign * step)
                cr = decode(m, cand, qlo, qhi)
                if require_feasible and (not is_feasible(cr) or (min_active and not is_active(cr))):
                    continue
                score = objective(cr)
                if score < best_score:
                    z = cand
                    best_score = score
                    best = SearchResult(cand[:], cr)
                    improved = True
        if not improved:
            step *= 0.55
    return best


def search_m(m: int, samples: int = 12000, seed: int = 20260531) -> dict[str, SearchResult]:
    rng = random.Random(seed + m)
    qlo, qhi = window(m)
    best_feasible = None
    best_feasible_phi = None
    best_active = None
    best_penalty = None
    best_infeasible_defect = None

    starts: list[list[float]] = []
    for z in (
        [1.0, 0.01, 0.8, 0.0, 0.5],
        [1.0, 0.01, 0.8, 0.35, 0.5],
        [1.0, 0.05, 0.8, 0.65, 0.5],
        [1.0, 0.15, 0.8, 1.0, 0.5],
        [0.5, 0.95, 0.0, 0.0, 0.5],
    ):
        starts.append(z)

    for _ in range(samples):
        starts.append(random_z(rng))

    for z in starts:
        r = decode(m, z, qlo, qhi)
        if best_penalty is None or penalty_score(r) < penalty_score(best_penalty.result):
            best_penalty = SearchResult(z[:], r)
        if r.gap < 0 and (best_infeasible_defect is None or r.defect < best_infeasible_defect.result.defect):
            best_infeasible_defect = SearchResult(z[:], r)
        if is_feasible(r):
            if best_feasible is None or r.defect < best_feasible.result.defect:
                best_feasible = SearchResult(z[:], r)
            if best_feasible_phi is None or r.phi < best_feasible_phi.result.phi:
                best_feasible_phi = SearchResult(z[:], r)
            if is_active(r) and (best_active is None or r.defect < best_active.result.defect):
                best_active = SearchResult(z[:], r)

    refined = {}
    if best_feasible is not None:
        refined["min_defect_feasible"] = coordinate_refine(
            m, best_feasible.z, lambda r: r.defect, require_feasible=True
        )
    if best_feasible_phi is not None:
        refined["min_phi_feasible"] = coordinate_refine(
            m, best_feasible_phi.z, lambda r: r.phi, require_feasible=True
        )
    if best_active is not None:
        refined["min_defect_active"] = coordinate_refine(
            m, best_active.z, lambda r: r.defect, require_feasible=True, min_active=True
        )
    if best_penalty is not None:
        refined["penalty_boundary"] = coordinate_refine(
            m, best_penalty.z, penalty_score, require_feasible=False
        )
    if best_infeasible_defect is not None:
        refined["most_negative_infeasible"] = coordinate_refine(
            m, best_infeasible_defect.z, lambda r: r.defect, require_feasible=False
        )
    return refined


def main() -> None:
    print("Finite-dimensional deletion-retaining frontier search")
    for m in [21, 23, 25, 31]:
        print(f"\n=== m={m} ===")
        out = search_m(m)
        for name, item in out.items():
            print(f"{name}:")
            print(f"  z={[round(x, 8) for x in item.z]}")
            print(f"  {fmt_result(item.result)}")


if __name__ == "__main__":
    main()
