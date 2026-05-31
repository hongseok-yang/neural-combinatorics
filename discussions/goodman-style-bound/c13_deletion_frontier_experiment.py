"""
Numerical diagnostics for a deletion-retaining C13 attack.

This script deliberately avoids numpy so it can run in the lightweight project
environment.  It evaluates

    defect = t(C13,W) - (p^13 - p(1-p)^12)
           = Phi_13 + (x_12 - c_13)

on finite block graphons, and records the spectrum of the mean-zero compression
A = P_{1^\perp} T_U P_{1^\perp}.  The goal is to separate two phenomena:

  * Phi_13 can be negative even when lambda_max(A) <= q, hence the graphon is
    already covered by the positive-spectrum-safe criterion.
  * The only case not handled by the positive-spectrum-safe criterion has a
    unique frontier eigenvalue alpha > q.
"""

from __future__ import annotations

from collections import Counter
from itertools import combinations
from math import cos, hypot, sin, sqrt
import random


M = 13
Q_LO = 481 / 1000
Q_HI = 0.5 - 0.015592935


def path_components(n: int, subset) -> tuple[int, ...]:
    adj = [set() for _ in range(n)]
    for i in subset:
        u, v = i, (i + 1) % n
        adj[u].add(v)
        adj[v].add(u)
    seen = set()
    comps = []
    for v in range(n):
        if adj[v] and v not in seen:
            stack = [v]
            seen.add(v)
            edges_twice = 0
            while stack:
                a = stack.pop()
                edges_twice += len(adj[a])
                for b in adj[a]:
                    if b not in seen:
                        seen.add(b)
                        stack.append(b)
            comps.append(edges_twice // 2)
    return tuple(sorted(comps, reverse=True))


COUNTS = {
    r: Counter(path_components(M, s) for s in combinations(range(M), r))
    for r in range(M + 1)
}


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


def matvec(A, v):
    return [sum(aij * vj for aij, vj in zip(row, v)) for row in A]


def trace_power(A, power: int) -> float:
    n = len(A)
    P = [[float(i == j) for j in range(n)] for i in range(n)]
    for _ in range(power):
        P = matmul(P, A)
    return sum(P[i][i] for i in range(n))


def jacobi_eigh(A, max_iter=200, tol=1e-13):
    n = len(A)
    A = [row[:] for row in A]
    V = [[float(i == j) for j in range(n)] for i in range(n)]
    for _ in range(max_iter):
        p, q = 0, 1
        best = 0.0
        for i in range(n):
            for j in range(i + 1, n):
                val = abs(A[i][j])
                if val > best:
                    best = val
                    p, q = i, j
        if best < tol:
            break
        app, aqq, apq = A[p][p], A[q][q], A[p][q]
        tau = (aqq - app) / (2 * apq)
        t = (1 if tau >= 0 else -1) / (abs(tau) + sqrt(1 + tau * tau))
        c = 1 / sqrt(1 + t * t)
        s = t * c
        for k in range(n):
            if k != p and k != q:
                akp, akq = A[k][p], A[k][q]
                A[k][p] = A[p][k] = c * akp - s * akq
                A[k][q] = A[q][k] = s * akp + c * akq
        A[p][p] = c * c * app - 2 * s * c * apq + s * s * aqq
        A[q][q] = s * s * app + 2 * s * c * apq + c * c * aqq
        A[p][q] = A[q][p] = 0.0
        for k in range(n):
            vkp, vkq = V[k][p], V[k][q]
            V[k][p] = c * vkp - s * vkq
            V[k][q] = s * vkp + c * vkq
    vals = [A[i][i] for i in range(n)]
    order = sorted(range(n), key=lambda i: vals[i], reverse=True)
    return [vals[i] for i in order], [[V[row][i] for row in range(n)] for i in order]


def lower_expression(q: float, xs: list[float]) -> float:
    def term(comp):
        out = 1.0
        for a in comp:
            out *= q if a == 1 else xs[a]
        return out

    E = 1.0
    for r in range(1, M):
        sign = -1.0 if r % 2 else 1.0
        for comp, count in COUNTS[r].items():
            E += sign * count * term(comp)
    E -= xs[M - 1]
    return E


def eval_block(w, U):
    k = len(w)
    T = [[U[i][j] * w[j] for j in range(k)] for i in range(k)]
    TW = [[(1 - U[i][j]) * w[j] for j in range(k)] for i in range(k)]
    q = sum(w[i] * U[i][j] * w[j] for i in range(k) for j in range(k))
    p = 1 - q

    v = [1.0] * k
    xs = [1.0]
    for _ in range(1, M):
        v = matvec(T, v)
        xs.append(sum(w[i] * v[i] for i in range(k)))

    c13 = trace_power(T, M)
    tW13 = trace_power(TW, M)
    target = p**M - p * q ** (M - 1)
    phi = lower_expression(q, xs) - target
    gap = xs[M - 1] - c13
    defect = tW13 - target

    d = [sum(U[i][j] * w[j] for j in range(k)) for i in range(k)]
    g = [di - q for di in d]
    # P0 = I - 1 w^T, A = P0 T P0.
    P0 = [[(1.0 if i == j else 0.0) - w[j] for j in range(k)] for i in range(k)]
    A = matmul(matmul(P0, T), P0)
    # Symmetric representative D^{1/2} A D^{-1/2}.
    As = [[sqrt(w[i]) * A[i][j] / sqrt(w[j]) for j in range(k)] for i in range(k)]
    As = [[0.5 * (As[i][j] + As[j][i]) for j in range(k)] for i in range(k)]
    vals, vecs = jacobi_eigh(As)
    gs = [sqrt(w[i]) * g[i] for i in range(k)]
    modes = []
    for val, vec in zip(vals, vecs):
        b = sum(gs[i] * vec[i] for i in range(k))
        if abs(val) > 1e-9 or b * b > 1e-12:
            modes.append((val, b * b))
    front = [(val, b2) for val, b2 in modes if val > q + 1e-9]
    trA13 = sum(val**M for val, _ in modes)
    psi = tW13 - (p**M - trA13)
    frontier_excess = sum(val**M - q ** (M - 2) * val * val for val, _ in front)
    return {
        "q": q,
        "p": p,
        "phi": phi,
        "gap": gap,
        "defect": defect,
        "psi": psi,
        "trA13": trA13,
        "frontier_excess": frontier_excess,
        "front": front,
        "modes": modes,
        "lambda_max_A": max(val for val, _ in modes),
        "safe": len(front) == 0,
    }


def closure_witness():
    w = [39 / 100, 61 / 100]
    U = [[43 / 50, 1 / 10], [1 / 10, 41 / 50]]
    return w, U


def tripartite_complement_from_p(p: float):
    eps = p - 0.5
    c = (1 - sqrt(1 - 6 * eps)) / 3
    b = (1 - c) / 2
    w = [c, b, b]
    U = [[1.0 if i == j else 0.0 for j in range(3)] for i in range(3)]
    return w, U


def random_graphon(k: int):
    raw = [random.random() for _ in range(k)]
    s = sum(raw)
    w = [x / s for x in raw]
    U = [[0.0] * k for _ in range(k)]
    for i in range(k):
        for j in range(i, k):
            # Bias toward the residual band while keeping broad structure.
            x = min(1.0, max(0.0, random.gauss(0.48, 0.28)))
            U[i][j] = U[j][i] = x
    return w, U


def tripartite_like_graphon():
    p0 = random.uniform(0.5156, 0.5190)
    w, U = tripartite_complement_from_p(p0)
    # Preserve the two-large-parts geometry but perturb both weights and values.
    w = [max(0.001, wi + random.gauss(0.0, 0.012)) for wi in w]
    s = sum(w)
    w = [wi / s for wi in w]
    for i in range(3):
        for j in range(i, 3):
            base = 1.0 if i == j else 0.0
            val = min(1.0, max(0.0, base + random.gauss(0.0, 0.06)))
            U[i][j] = U[j][i] = val
    return w, U


def main():
    print(f"Transition q-window approximately [{Q_LO:.6f}, {Q_HI:.6f}]")
    w, U = closure_witness()
    res = eval_block(w, U)
    print("\nUnequal two-block path-failure witness:")
    print(
        f"  q={res['q']:.6f}, lambda_max(A)={res['lambda_max_A']:.6f}, "
        f"safe={res['safe']}"
    )
    print(
        f"  Phi_13={res['phi']:+.6e}, x12-c13={res['gap']:+.6e}, "
        f"defect={res['defect']:+.6e}"
    )

    print("\nTriangle-extremal complement examples (frontier mode decoupled):")
    for p0 in [0.5157, 0.5170, 0.5185]:
        w, U = tripartite_complement_from_p(p0)
        res = eval_block(w, U)
        alpha, b2 = res["front"][0] if res["front"] else (float("nan"), float("nan"))
        print(
            f"  p={p0:.4f}, q={res['q']:.6f}, alpha={alpha:.6f}, "
            f"b_front^2={b2:.1e}, Phi={res['phi']:+.3e}, "
            f"gap={res['gap']:+.3e}, defect={res['defect']:+.3e}, "
            f"Psi={res['psi']:+.3e}, frontier_excess={res['frontier_excess']:+.3e}"
        )

    best_phi = None
    best_defect = None
    best_front_phi = None
    frontier_examples = []
    accepted = 0
    random.seed(20260531)
    for t in range(12000):
        if t % 2:
            k = random.randint(2, 6)
            w, U = random_graphon(k)
        else:
            w, U = tripartite_like_graphon()
        res = eval_block(w, U)
        if not (Q_LO <= res["q"] <= Q_HI):
            continue
        accepted += 1
        if best_phi is None or res["phi"] < best_phi["phi"]:
            best_phi = res
        if best_defect is None or res["defect"] < best_defect["defect"]:
            best_defect = res
        if res["front"] and (best_front_phi is None or res["phi"] < best_front_phi["phi"]):
            best_front_phi = res
        if res["front"] and len(frontier_examples) < 5:
            frontier_examples.append(res)

    print(f"\nRandom transition-band sample: accepted {accepted} graphons")
    if best_phi:
        print(
            f"  most negative Phi: q={best_phi['q']:.6f}, "
            f"lambda_max(A)={best_phi['lambda_max_A']:.6f}, safe={best_phi['safe']}, "
            f"Phi={best_phi['phi']:+.3e}, gap={best_phi['gap']:+.3e}, "
            f"defect={best_phi['defect']:+.3e}"
        )
    if best_defect:
        print(
            f"  smallest defect: q={best_defect['q']:.6f}, "
            f"lambda_max(A)={best_defect['lambda_max_A']:.6f}, safe={best_defect['safe']}, "
            f"Phi={best_defect['phi']:+.3e}, gap={best_defect['gap']:+.3e}, "
            f"defect={best_defect['defect']:+.3e}"
        )
    if best_front_phi:
        alpha, b2 = best_front_phi["front"][0]
        print(
            f"  most negative frontier Phi: q={best_front_phi['q']:.6f}, "
            f"alpha={alpha:.6f}, b^2={b2:.3e}, "
            f"Phi={best_front_phi['phi']:+.3e}, gap={best_front_phi['gap']:+.3e}, "
            f"defect={best_front_phi['defect']:+.3e}"
        )
    print("\nFirst frontier examples (if any):")
    for res in frontier_examples:
        alpha, b2 = res["front"][0]
        print(
            f"  q={res['q']:.6f}, alpha={alpha:.6f}, b^2={b2:.3e}, "
            f"Phi={res['phi']:+.3e}, gap={res['gap']:+.3e}, "
            f"defect={res['defect']:+.3e}, Psi={res['psi']:+.3e}, "
            f"frontier_excess={res['frontier_excess']:+.3e}"
        )


if __name__ == "__main__":
    main()
