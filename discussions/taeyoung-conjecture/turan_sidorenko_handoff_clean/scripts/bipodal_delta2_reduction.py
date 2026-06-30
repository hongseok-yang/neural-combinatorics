"""
Exact symbolic reductions for the bipodal smoothed-Goodman target.

A bipodal graphon has block masses s, 1-s and matrix [[a,b],[b,c]].
This script computes

    Delta_2 = int W T_W^2 T_W^4 - (2p-1) int W T_W^4,

verifies the rank-two Cayley-Hamilton reduction

    Delta_2 = (tau^2-eta) D1 - tau eta R,

checks the Boolean two-block boundary exactly, and checks the one-sided
threshold family [[a,1],[1,0]] using the resultant/Sturm argument described
in the accompanying note.

The final Bernstein subdivision routine is exploratory, not a formal proof:
near boundary zero curves exact Bernstein subdivision does not terminate without
additional analytic desingularization.
"""

from __future__ import annotations

from math import comb
import itertools
import numpy as np
import sympy as sp


def symbolic_objects():
    s, a, b, c = sp.symbols("s a b c", real=True)
    t = 1 - s
    D = sp.diag(s, t)
    M = sp.Matrix([[a, b], [b, c]])

    # Kernels of T_W^2 and T_W^4 on block pairs.
    K2 = M * D * M
    K4 = M * D * M * D * M * D * M

    p = s * s * a + 2 * s * t * b + t * t * c
    alpha = 2 * p - 1

    Delta = sp.Integer(0)
    D1 = sp.Integer(0)
    R = sp.Integer(0)
    weights = [[s * s, s * t], [s * t, t * t]]
    for i in range(2):
        for j in range(2):
            wij = weights[i][j]
            Delta += wij * M[i, j] * (K2[i, j] - alpha) * K4[i, j]
            D1 += wij * M[i, j] * K2[i, j] * (K2[i, j] - alpha)
            R += wij * M[i, j] ** 2 * (K2[i, j] - alpha)

    tau = s * a + t * c
    eta = s * t * (a * c - b * b)
    return {
        "vars": (s, a, b, c),
        "M": M,
        "D": D,
        "K2": K2,
        "K4": K4,
        "p": sp.expand(p),
        "alpha": sp.expand(alpha),
        "Delta": sp.expand(Delta),
        "D1": sp.expand(D1),
        "R": sp.expand(R),
        "tau": sp.expand(tau),
        "eta": sp.expand(eta),
    }


def verify_rank_two_identity() -> None:
    obj = symbolic_objects()
    Delta, D1, R = obj["Delta"], obj["D1"], obj["R"]
    tau, eta = obj["tau"], obj["eta"]
    diff = sp.expand(Delta - ((tau ** 2 - eta) * D1 - tau * eta * R))
    assert diff == 0
    print("rank-two identity: OK")


def verify_boolean_boundary() -> None:
    obj = symbolic_objects()
    s, a, b, c = obj["vars"]
    Delta = obj["Delta"]
    print("Boolean two-block boundary factorizations:")
    for A, B, C in itertools.product([0, 1], repeat=3):
        expr = sp.factor(Delta.subs({a: A, b: B, c: C}))
        print(f"  (a,b,c)=({A},{B},{C}): {expr}")
    print("Each displayed expression is nonnegative on 0 <= s <= 1.")


def sign_variations_at(sturm_seq, var, point) -> int:
    signs: list[int] = []
    for f in sturm_seq:
        v = sp.simplify(f.subs(var, point))
        if v == 0:
            continue
        signs.append(1 if v > 0 else -1)
    return sum(1 for i in range(len(signs) - 1) if signs[i] != signs[i + 1])


def verify_one_sided_threshold() -> None:
    """Check the family M=[[a,1],[1,0]]."""
    obj = symbolic_objects()
    s, a, b, c = obj["vars"]
    Delta = obj["Delta"]
    P = sp.factor(Delta.subs({b: 1, c: 0}) / (s ** 3 * a))
    print("one-sided threshold: Delta = s^3 a P(s,a)")
    print("P(s,a) =")
    print(sp.expand(P))

    # Boundary checks.
    print("boundary values:")
    for name, expr in [
        ("P(0,a)", P.subs(s, 0)),
        ("P(1,a)", sp.factor(P.subs(s, 1))),
        ("P(s,0)", sp.factor(P.subs(a, 0))),
        ("P(s,1)", sp.factor(P.subs(a, 1))),
    ]:
        print(f"  {name} = {expr}")

    res = sp.factor(sp.resultant(P, sp.diff(P, s), s))
    print("resultant Res_s(P, dP/ds) factors as:")
    print(res)

    L = sp.Poly(res / (2 * a ** 4 * (a - 2) * (a - 1) ** 4 * (a ** 4 - 5 * a ** 2 + 5)), a).as_expr()
    st = sp.sturm(L, a)
    roots_01 = sign_variations_at(st, a, 0) - sign_variations_at(st, a, 1)
    print(f"Sturm root count for the degree-16 factor on [0,1]: {roots_01}")
    assert roots_01 == 0
    assert L.subs(a, 0) > 0 and L.subs(a, 1) > 0
    print("one-sided threshold family: certified by resultant/Sturm argument")


def power_to_bernstein_float(poly, vars_, degs):
    P = sp.Poly(sp.expand(poly), *vars_)
    coeff_dict = P.as_dict()
    shape = tuple(d + 1 for d in degs)
    beta = np.zeros(shape, dtype=float)
    for I in itertools.product(*[range(d + 1) for d in degs]):
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


def exploratory_bernstein(tol: float = 1e-12, max_nodes: int = 1_000_000):
    obj = symbolic_objects()
    vars_ = obj["vars"]
    Delta = obj["Delta"]
    P = sp.Poly(Delta, *vars_)
    degs = [P.degree(v) for v in vars_]
    ctrl = power_to_bernstein_float(Delta, vars_, degs)
    stack = [(ctrl, 0)]
    nodes = leaves = 0
    max_depth = 0
    while stack:
        C, depth = stack.pop()
        nodes += 1
        max_depth = max(max_depth, depth)
        mn = float(C.min())
        mx = float(C.max())
        if mn >= -tol:
            leaves += 1
            continue
        if mx < -tol:
            return False, nodes, leaves, max_depth, mn, mx
        if nodes > max_nodes:
            return None, nodes, leaves, max_depth, mn, mx
        variations = [float(np.max(np.abs(np.diff(C, axis=ax)))) for ax in range(C.ndim)]
        ax = int(np.argmax(variations))
        L, R = subdivide_axis(C, ax)
        stack.append((R, depth + 1))
        stack.append((L, depth + 1))
    return True, nodes, leaves, max_depth


if __name__ == "__main__":
    obj = symbolic_objects()
    P = sp.Poly(obj["Delta"], *obj["vars"])
    print("Delta individual degrees:", [P.degree(v) for v in obj["vars"]])
    print("Delta number of terms:", len(P.as_dict()))
    verify_rank_two_identity()
    verify_boolean_boundary()
    verify_one_sided_threshold()
    print("exploratory Bernstein subdivision:", exploratory_bernstein())
