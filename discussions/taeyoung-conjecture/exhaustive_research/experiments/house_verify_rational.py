"""Independent exact checker for ``house_atlas43_rational.json``."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path

import networkx as nx
import numpy as np
import sympy as sp
from networkx.algorithms.polynomials import chromatic_polynomial

from house_rationalize_full import scaled_equations


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", nargs="?", default="experiments/house_atlas43_rational.json")
    args = parser.parse_args()
    certificate = json.loads(Path(args.certificate).read_text(encoding="utf-8"))
    if certificate["atlas"] != 43 or certificate["interval"] != ["1/2", "1"]:
        raise AssertionError("wrong target or interval")

    # Independently check the target polynomial used by the coefficient builder.
    p = sp.symbols("p")
    graph = nx.graph_atlas(43)
    chromatic = chromatic_polynomial(graph)
    x = next(iter(chromatic.free_symbols))
    target = sp.factor((1 - p) ** 5 * chromatic.subs(x, 1 / (1 - p)))
    if sp.expand(target) != 6 * p**4 - 9 * p**3 + 5 * p**2 - p:
        raise AssertionError(target)

    denominator = int(certificate["factor_denominator"])
    factors = [np.asarray(certificate[f"F{index}"], dtype=np.int64) for index in range(2)]
    orders = [int(value) for value in certificate["orders"]]
    if [factor.shape for factor in factors] != [(128, orders[0]), (64, orders[1])]:
        raise AssertionError([factor.shape for factor in factors])

    corrections = [dict(), dict()]
    diagonals = [[Fraction(1) for _ in range(order)] for order in orders]
    radii = [[Fraction(0) for _ in range(order)] for order in orders]
    for block, i, j, numerator, correction_denominator in certificate["corrections"]:
        block, i, j = int(block), int(i), int(j)
        if not (0 <= block < 2 and 0 <= i <= j < orders[block]):
            raise AssertionError((block, i, j))
        value = Fraction(int(numerator), int(correction_denominator))
        if (i, j) in corrections[block]:
            raise AssertionError("duplicate correction")
        corrections[block][(i, j)] = value
        if i == j:
            diagonals[block][i] += value
        else:
            radii[block][i] += abs(value)
            radii[block][j] += abs(value)
    margins = [
        min(diagonal - radius for diagonal, radius in zip(block_diagonal, block_radius))
        for block_diagonal, block_radius in zip(diagonals, radii)
    ]
    claimed_margins = [Fraction(*map(int, pair)) for pair in certificate["dd_margins"]]
    if margins != claimed_margins or min(margins) <= 0:
        raise AssertionError((margins, claimed_margins))

    equations = scaled_equations(sp.Rational(1, 2), sp.Rational(1))
    for equation_index, (m0, m1, rhs, core, power, scale) in enumerate(equations):
        total = Fraction(0)
        for matrix, factor, block_corrections in zip((m0, m1), factors, corrections):
            pulled = factor.T @ matrix @ factor
            total += sum(Fraction(int(pulled[i, i])) for i in range(pulled.shape[0]))
            for (i, j), value in block_corrections.items():
                coefficient = int(pulled[i, j]) if i == j else 2 * int(pulled[i, j])
                total += coefficient * value
        if total != rhs * denominator**2:
            raise AssertionError(
                f"equation {equation_index} (core={core}, power={power}, scale={scale}) failed"
            )
    print(
        f"verified Atlas 43 exact interval SOS: equations={len(equations)} "
        f"orders={orders} DD_margins={[str(item) for item in margins]}"
    )


if __name__ == "__main__":
    main()
