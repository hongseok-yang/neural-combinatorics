"""
Bipodal checker for the smoothed Goodman target

For a two-block graphon with masses s,1-s and matrix [[a,b],[b,c]], this script
computes
    Delta_2 = int W T_W^2 T_W^4 - (2p-1) int W T_W^4.
It also runs a Bernstein-subdivision search over the full cube [0,1]^4.
The subdivision routine is a numerical certificate finder: it is useful for
exploration, but it is not a formal proof unless the accepted lower bounds are
rechecked with outward-rounded interval or exact rational arithmetic.
"""

from __future__ import annotations

from math import comb
import itertools
import numpy as np
import sympy as sp


def symbolic_delta():
    s, a, b, c = sp.symbols("s a b c", real=True)
    t = 1 - s
    D = sp.diag(s, t)
    M = sp.Matrix([[a, b], [b, c]])
    K2 = M * D * M
    K4 = M * D * M * D * M * D * M
    p = s*s*a + 2*s*t*b + t*t*c
    alpha = 2*p - 1
    weights = [[s*s, s*t], [s*t, t*t]]
    Delta = sp.Integer(0)
    for i in range(2):
        for j in range(2):
            Delta += weights[i][j] * M[i, j] * (K2[i, j] - alpha) * K4[i, j]
    return sp.expand(Delta), (s, a, b, c)


def numeric_delta(s: float, a: float, b: float, c: float) -> tuple[float, float]:
    t = 1.0 - s
    M = np.array([[a, b], [b, c]], dtype=float)
    w = np.array([s, t], dtype=float)
    D = np.diag(w)
    K2 = M @ D @ M
    K4 = M @ D @ M @ D @ M @ D @ M
    p = s*s*a + 2*s*t*b + t*t*c
    alpha = 2*p - 1
    Delta = 0.0
    for i in range(2):
        for j in range(2):
            Delta += w[i]*w[j]*M[i, j]*(K2[i, j]-alpha)*K4[i, j]
    return Delta, p


def power_to_bernstein(poly, vars_, degs):
    P = sp.Poly(sp.expand(poly), *vars_)
    coeff_dict = P.as_dict()
    shape = tuple(d+1 for d in degs)
    beta = np.zeros(shape, dtype=float)
    for I in itertools.product(*[range(d+1) for d in degs]):
        val = 0.0
        for J, coeff in coeff_dict.items():
            if all(J[k] <= I[k] for k in range(len(vars_))):
                term = float(coeff)
                for k, d in enumerate(degs):
                    term *= comb(I[k], J[k]) / comb(d, J[k])
                val += term
        beta[I] = val
    return beta


def subdivide_axis(ctrl: np.ndarray, axis: int):
    arr = np.moveaxis(ctrl, axis, 0)
    n = arr.shape[0] - 1
    cur = arr.copy()
    left = [cur[0].copy()]
    right = [cur[-1].copy()]
    for _ in range(n):
        cur = 0.5 * cur[:-1] + 0.5 * cur[1:]
        left.append(cur[0].copy())
        right.append(cur[-1].copy())
    L = np.moveaxis(np.stack(left, axis=0), 0, axis)
    R = np.moveaxis(np.stack(right[::-1], axis=0), 0, axis)
    return L, R


def bernstein_subdivision(ctrl: np.ndarray, tol: float = 1e-12, max_nodes: int = 1_000_000):
    stack = [(ctrl, 0)]
    nodes = 0
    worst = (0, float(ctrl.min()), float(ctrl.max()))
    while stack:
        C, depth = stack.pop()
        nodes += 1
        mn = float(C.min())
        mx = float(C.max())
        if mn < worst[1]:
            worst = (depth, mn, mx)
        if mn >= -tol:
            continue
        if mx < -tol:
            return False, nodes, worst
        if nodes > max_nodes:
            return None, nodes, worst
        variations = [float(np.max(np.abs(np.diff(C, axis=ax)))) for ax in range(C.ndim)]
        ax = int(np.argmax(variations))
        L, R = subdivide_axis(C, ax)
        stack.append((R, depth+1))
        stack.append((L, depth+1))
    return True, nodes, worst


if __name__ == "__main__":
    Delta, vars_ = symbolic_delta()
    degs = [sp.Poly(Delta, *vars_).degree(v) for v in vars_]
    print("individual degrees", degs)
    ctrl = power_to_bernstein(Delta, vars_, degs)
    print("initial Bernstein min/max", ctrl.min(), ctrl.max())
    print("subdivision result", bernstein_subdivision(ctrl))
    # A few sanity checks
    for point in [(0.5,0,1,0), (0.5,1,0,1), (0.3,0.4,0.9,0.7), (0.9,0.2,1,1)]:
        print(point, numeric_delta(*point))
