"""
Formalization aid for the bipodal smoothed-Goodman target.

Target.  For a bipodal graphon with block masses s, 1-s and matrix

    [[a,b], [b,c]],       0 <= s,a,b,c <= 1,

let p be the edge density and T the graphon operator.  The quantity studied is

    Delta_2 = int W T^2 T^4 - (2p-1) int W T^4.

The conjectured bipodal theorem is Delta_2 >= 0 on the cube [0,1]^4.

This script does three things:
  1. symbolically derives Delta_2 and verifies the rank-two Cayley-Hamilton
     identity Delta_2 = (tau^2-eta) D1 - tau eta R;
  2. runs the floating-point Bernstein subdivision search used for exploration;
  3. rechecks the resulting subdivision tree using exact integer/rational
     Bernstein arithmetic.  This proves all accepted boxes whose exact
     Bernstein coefficients are nonnegative and reports the remaining boundary
     boxes.  At present those remaining boxes are tiny neighborhoods of the
     lower-dimensional complete-graphon boundary; they are the remaining gap in
     a fully formal bipodal proof.

The exact verification is not a proof of the unresolved boxes.  It is meant to
make precise what has and has not been certified.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import comb, gcd
import itertools
import time
from typing import Optional

import numpy as np
import sympy as sp


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def symbolic_objects():
    s, a, b, c = sp.symbols("s a b c", real=True)
    t = 1 - s
    D = sp.diag(s, t)
    M = sp.Matrix([[a, b], [b, c]])
    K2 = M * D * M
    K4 = M * D * M * D * M * D * M
    p = s * s * a + 2 * s * t * b + t * t * c
    alpha = 2 * p - 1
    weights = [[s * s, s * t], [s * t, t * t]]

    Delta = sp.Integer(0)
    D1 = sp.Integer(0)
    R = sp.Integer(0)
    for i in range(2):
        for j in range(2):
            Delta += weights[i][j] * M[i, j] * (K2[i, j] - alpha) * K4[i, j]
            D1 += weights[i][j] * M[i, j] * K2[i, j] * (K2[i, j] - alpha)
            R += weights[i][j] * M[i, j] ** 2 * (K2[i, j] - alpha)

    tau = s * a + t * c
    eta = s * t * (a * c - b * b)
    return {
        "vars": (s, a, b, c),
        "M": M,
        "D": D,
        "K2": K2,
        "K4": K4,
        "p": sp.expand(p),
        "Delta": sp.expand(Delta),
        "D1": sp.expand(D1),
        "R": sp.expand(R),
        "tau": sp.expand(tau),
        "eta": sp.expand(eta),
    }


def power_to_bernstein_float(poly, vars_, degs):
    """Convert a power-basis polynomial on [0,1]^d to Bernstein coefficients.

    Floating-point version, used only to select a subdivision tree.
    """
    P = sp.Poly(sp.expand(poly), *vars_)
    coeff_dict = P.as_dict()
    shape = tuple(d + 1 for d in degs)
    beta = np.zeros(shape, dtype=float)
    ranges = [range(d + 1) for d in degs]
    for I in itertools.product(*ranges):
        val = 0.0
        for J, coeff in coeff_dict.items():
            if all(J[k] <= I[k] for k in range(len(vars_))):
                term = float(coeff)
                for k, d in enumerate(degs):
                    term *= comb(I[k], J[k]) / comb(d, J[k])
                val += term
        beta[I] = val
    return beta


def subdivide_axis_float(ctrl: np.ndarray, axis: int):
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


@dataclass
class Tree:
    axis: Optional[int] = None
    left: Optional["Tree"] = None
    right: Optional["Tree"] = None

    @property
    def is_leaf(self) -> bool:
        return self.axis is None


def build_numeric_tree(ctrl: np.ndarray, tol: float = 1e-12) -> Tree:
    mn = float(ctrl.min())
    mx = float(ctrl.max())
    if mn >= -tol:
        return Tree()
    if mx < -tol:
        raise RuntimeError("floating-point search found a negative Bernstein box")
    variations = [float(np.max(np.abs(np.diff(ctrl, axis=ax)))) for ax in range(ctrl.ndim)]
    ax = int(np.argmax(variations))
    left, right = subdivide_axis_float(ctrl, ax)
    return Tree(ax, build_numeric_tree(left, tol), build_numeric_tree(right, tol))


def tree_stats(tree: Tree):
    if tree.is_leaf:
        return 1, 1, 0
    n_l, leaves_l, internal_l = tree_stats(tree.left)
    n_r, leaves_r, internal_r = tree_stats(tree.right)
    return 1 + n_l + n_r, leaves_l + leaves_r, 1 + internal_l + internal_r


def exact_initial_bernstein(poly, vars_, degs):
    """Exact Bernstein coefficients on [0,1]^d.

    Returns integer coefficients with a common positive denominator.  Since only
    signs matter for certification, the denominator is not used by the verifier.
    """
    P = sp.Poly(sp.expand(poly), *vars_)
    coeff_dict = {mon: int(coeff) for mon, coeff in P.as_dict().items()}
    values: list[Fraction] = []
    common_den = 1
    for I in itertools.product(*[range(d + 1) for d in degs]):
        val = Fraction(0, 1)
        for J, coeff in coeff_dict.items():
            ok = True
            num = coeff
            den = 1
            for k, d in enumerate(degs):
                if J[k] > I[k]:
                    ok = False
                    break
                num *= comb(I[k], J[k])
                den *= comb(d, J[k])
            if ok and num:
                val += Fraction(num, den)
        values.append(val)
        common_den = lcm(common_den, val.denominator)
    ints = [v.numerator * (common_den // v.denominator) for v in values]
    ctrl = np.array(ints, dtype=object).reshape(tuple(d + 1 for d in degs))
    return ctrl, common_den


def split_axis_int(ctrl: np.ndarray, axis: int, degs):
    """Exact de Casteljau subdivision at midpoint.

    Input coefficients are integers with a common denominator.  Output child
    coefficients are integers with a new common denominator obtained by
    multiplying by 2^degree_along_axis.  Signs are therefore exact.
    """
    arr = np.moveaxis(ctrl, axis, 0)
    n = arr.shape[0] - 1
    cur = arr.copy()
    left = []
    right = []
    for k in range(n + 1):
        # At de Casteljau level k, the true average has denominator 2^k.
        # To put all coefficients over denominator 2^n, multiply by 2^(n-k).
        fac = 1 << (n - k)
        left.append(cur[0] * fac)
        right.append(cur[-1] * fac)
        if k < n:
            cur = cur[:-1] + cur[1:]
    L = np.moveaxis(np.stack(left, axis=0), 0, axis)
    R = np.moveaxis(np.stack(right[::-1], axis=0), 0, axis)
    return L, R


def min_int(ctrl: np.ndarray) -> int:
    flat = ctrl.ravel()
    mn = flat[0]
    for x in flat[1:]:
        if x < mn:
            mn = x
    return int(mn)


def verify_tree_exact(ctrl: np.ndarray, tree: Tree, degs):
    certified = 0
    unresolved = []

    def rec(C: np.ndarray, node: Tree, box, depth: int):
        nonlocal certified, unresolved
        if node.is_leaf:
            mn = min_int(C)
            if mn >= 0:
                certified += 1
            else:
                unresolved.append((box, depth, mn))
            return
        L, R = split_axis_int(C, node.axis, degs)
        lo, hi = box[node.axis]
        mid = (lo + hi) / 2
        box_l = list(box)
        box_r = list(box)
        box_l[node.axis] = (lo, mid)
        box_r[node.axis] = (mid, hi)
        rec(L, node.left, box_l, depth + 1)
        rec(R, node.right, box_r, depth + 1)

    unit = [(Fraction(0), Fraction(1)) for _ in range(4)]
    rec(ctrl, tree, unit, 0)
    return certified, unresolved


def fmt_box(box):
    names = ["s", "a", "b", "c"]
    pieces = []
    for name, (lo, hi) in zip(names, box):
        pieces.append(f"{name} in [{lo}, {hi}]")
    return "; ".join(pieces)


def main():
    t0 = time.time()
    obj = symbolic_objects()
    vars_ = obj["vars"]
    Delta = obj["Delta"]
    D1 = obj["D1"]
    R = obj["R"]
    tau = obj["tau"]
    eta = obj["eta"]
    degs = [sp.Poly(Delta, *vars_).degree(v) for v in vars_]
    print("Individual degrees:", degs)
    print("Number of power-basis terms:", len(sp.Poly(Delta, *vars_).terms()))

    identity = sp.expand(Delta - ((tau * tau - eta) * D1 - tau * eta * R))
    print("Rank-two identity verified:", identity == 0)

    ctrl_float = power_to_bernstein_float(Delta, vars_, degs)
    print("Initial floating Bernstein min/max:", ctrl_float.min(), ctrl_float.max())
    tree = build_numeric_tree(ctrl_float, tol=1e-12)
    nodes, leaves, internal = tree_stats(tree)
    print(f"Floating subdivision tree: nodes={nodes}, leaves={leaves}, internal={internal}")

    ctrl_exact, den = exact_initial_bernstein(Delta, vars_, degs)
    print("Exact initial common denominator:", den)
    print("Exact initial min coefficient:", min_int(ctrl_exact))

    certified, unresolved = verify_tree_exact(ctrl_exact, tree, degs)
    print(f"Exact leaf verification: certified={certified}, unresolved={len(unresolved)}")
    if unresolved:
        print("\nUnresolved exact Bernstein leaves:")
        for box, depth, mn in unresolved:
            print(f"  depth={depth:2d}, min_coeff<0, {fmt_box(box)}")
    print(f"\nElapsed seconds: {time.time() - t0:.2f}")


if __name__ == "__main__":
    main()
