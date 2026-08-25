"""Independent exact checker for S4 rooted interval-SOS JSON certificates."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path

import networkx as nx
import numpy as np
import sympy as sp
from flint import fmpq, fmpq_mat, fmpz_mat
from networkx.algorithms.polynomials import chromatic_polynomial

from s4_interval_rationalize import NAMES, coefficient_rows, exact_equations


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate")
    args = parser.parse_args()
    certificate = json.loads(Path(args.certificate).read_text(encoding="utf-8"))
    atlas = int(certificate["atlas"])
    left, right = map(sp.Rational, certificate["interval"])
    label_degree = int(certificate["label_degree"])
    degree_three_kind = certificate.get("degree_three_kind", "all")
    polynomial_degree = int(certificate.get("polynomial_degree", 2))
    denominator = int(certificate["factor_denominator"])

    # Recompute the target from the Atlas graph, independently of the string
    # stored in the certificate.
    p = sp.symbols("p")
    graph = nx.graph_atlas(atlas)
    chromatic = chromatic_polynomial(graph)
    x = next(iter(chromatic.free_symbols))
    target = sp.factor((1 - p) ** graph.number_of_nodes() *
                       chromatic.subs(x, 1 / (1 - p)))

    equations, transforms, basis_indices, _ = exact_equations(
        atlas, left, right, label_degree, degree_three_kind, polynomial_degree
    )
    if list(map(int, certificate["basis_indices"])) != basis_indices:
        raise AssertionError("wrong rooted basis")
    if certificate["names"] != NAMES:
        raise AssertionError("wrong S4 block order")
    for name, transform in zip(NAMES, transforms):
        claimed = np.asarray(certificate["young_bases"][name], dtype=np.int64)
        if not np.array_equal(claimed, transform):
            raise AssertionError(f"wrong Young basis {name}")

    factors = [np.asarray(value, dtype=np.int64) for value in certificate["factors"]]
    orders = list(map(int, certificate["orders"]))
    original_sizes = [transform.shape[1] for transform in transforms]
    order0 = polynomial_degree // 2 + 1
    order1 = polynomial_degree // 2
    expected_rows = [order0 * size for size in original_sizes] + [
        order1 * size for size in original_sizes
    ]
    if [factor.shape for factor in factors] != [
        (rows, order) for rows, order in zip(expected_rows, orders)
    ]:
        raise AssertionError("factor dimensions do not match the rooted slices")

    coordinates = [
        [(i, j) for i in range(order) for j in range(i, order)]
        for order in orders
    ]
    offsets = np.cumsum([0] + [len(item) for item in coordinates])
    coordinate_lookup = [
        {coordinate: index for index, coordinate in enumerate(items)}
        for items in coordinates
    ]
    vector = [fmpq(0) for _ in range(int(offsets[-1]))]
    diagonals = [[Fraction(1) for _ in range(order)] for order in orders]
    radii = [[Fraction(0) for _ in range(order)] for order in orders]
    for block, coords in enumerate(coordinates):
        for local, (i, j) in enumerate(coords):
            if i == j:
                vector[int(offsets[block]) + local] = fmpq(1)
    seen = set()
    for block, i, j, numerator, correction_denominator in certificate["corrections"]:
        block, i, j = int(block), int(i), int(j)
        if not (0 <= block < len(factors) and 0 <= i <= j < orders[block]):
            raise AssertionError((block, i, j))
        if (block, i, j) in seen:
            raise AssertionError("duplicate correction")
        seen.add((block, i, j))
        local = coordinate_lookup[block][(i, j)]
        value = Fraction(int(numerator), int(correction_denominator))
        vector[int(offsets[block]) + local] += fmpq(value.numerator, value.denominator)
        if i == j:
            diagonals[block][i] += value
        else:
            radii[block][i] += abs(value)
            radii[block][j] += abs(value)
    margins = [
        min(diagonal - radius for diagonal, radius in zip(block_diagonal, block_radius))
        for block_diagonal, block_radius in zip(diagonals, radii)
    ]
    claimed_margins = [Fraction(int(a), int(b)) for a, b in certificate["dd_margins"]]
    if margins != claimed_margins or min(margins) <= 0:
        raise AssertionError("diagonal-dominance audit failed")

    rows, rhs, rebuilt_coordinates = coefficient_rows(equations, factors)
    if rebuilt_coordinates != coordinates:
        raise AssertionError("coordinate order mismatch")
    integer_matrix = fmpz_mat([[int(value) for value in row] for row in rows])
    rational_vector = fmpq_mat(len(vector), 1, vector)
    actual = integer_matrix * rational_vector
    for index, target_integer in enumerate(rhs):
        expected = int(target_integer) * denominator**2
        if actual[index, 0] != expected:
            matrices, _, core, power, scale = equations[index]
            raise AssertionError(
                f"equation {index} core={core} power={power} scale={scale} failed"
            )
    print(
        f"verified Atlas {atlas} exact S4 interval SOS: interval=[{left},{right}] "
        f"target={target} equations={len(equations)} orders={orders} "
        f"min_DD_margin={min(margins)}"
    )


if __name__ == "__main__":
    main()
