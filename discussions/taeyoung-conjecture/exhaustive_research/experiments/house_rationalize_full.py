"""Turn a full-basis floating Atlas-43 interval SOS into an exact certificate.

The numerical Gram matrices are factored as L L^T.  We round L to a rational
matrix B/D and solve only 91 exact linear equations for a sparse correction
Y-I.  If Y is strictly diagonally dominant, then

    (B/D) Y (B/D)^T

is positive semidefinite in exact rational arithmetic.  The emitted JSON is
checked independently by ``house_verify_rational.py``.
"""

from __future__ import annotations

import argparse
import json
import math
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

import networkx as nx
import numpy as np
import sympy as sp
from scipy.linalg import qr

from house_certificate_faces import permutation_matrices, reconstruct
from rooted_sos_search import fixed_density_key, rooted_basis, rooted_product
from rooted_sos_search import label_s3_irrep_transforms


def scaled_equations(a: sp.Rational, b: sp.Rational):
    """Return exact integer (M0, M1, rhs) coefficient equations."""
    p, t = sp.symbols("p t")
    basis = rooted_basis(3, 1)
    size = len(basis)
    raw = defaultdict(lambda: np.zeros((size, size), dtype=np.int64))
    for i, left in enumerate(basis):
        for j in range(i, size):
            core, isolated = fixed_density_key(rooted_product(left, basis[j], 3, 1))
            raw[(core, isolated)][i, j] += 1
            if i != j:
                raw[(core, isolated)][j, i] += 1

    max_isolated = max(isolated for _, isolated in raw)

    def coefficients(expression):
        polynomial = sp.Poly(sp.expand(expression.subs(p, a + (b - a) * t)), t, domain=sp.QQ)
        return [sp.Rational(polynomial.nth(power)) for power in range(5)]

    density = {isolated: coefficients(p**isolated) for isolated in range(max_isolated + 1)}
    phi = 6 * p**4 - 9 * p**3 + 5 * p**2 - p
    target = {0: coefficients(-phi), 43: coefficients(sp.Integer(1))}
    cores = sorted(set(core for core, _ in raw) | {0, 43})
    zero = np.zeros((size, size), dtype=np.int64)
    result = []
    for core in cores:
        for total_power in range(5):
            m0_terms = []
            m1_terms = []
            used = False
            for isolated in range(max_isolated + 1):
                source = raw.get((core, isolated), zero)
                if not np.any(source):
                    continue
                for u in range(2):
                    for v in range(2):
                        index = total_power - u - v
                        if 0 <= index < 5 and density[isolated][index]:
                            m0_terms.append((density[isolated][index], u, v, source))
                            used = True
                index1, index2 = total_power - 1, total_power - 2
                if 0 <= index1 < 5 and density[isolated][index1]:
                    m1_terms.append((density[isolated][index1], source))
                    used = True
                if 0 <= index2 < 5 and density[isolated][index2]:
                    m1_terms.append((-density[isolated][index2], source))
                    used = True
            rhs = target.get(core, [sp.Rational(0)] * 5)[total_power]
            if not used and not rhs:
                continue
            denominators = [int(rhs.q)]
            denominators.extend(int(coefficient.q) for coefficient, *_ in m0_terms)
            denominators.extend(int(coefficient.q) for coefficient, *_ in m1_terms)
            scale = math.lcm(*denominators)
            m0 = np.zeros((2 * size, 2 * size), dtype=np.int64)
            m1 = np.zeros((size, size), dtype=np.int64)
            for coefficient, u, v, source in m0_terms:
                m0[u * size : (u + 1) * size, v * size : (v + 1) * size] += (
                    int(coefficient * scale) * source
                )
            for coefficient, source in m1_terms:
                m1 += int(coefficient * scale) * source
            result.append((m0, m1, int(rhs * scale), core, total_power, scale))
    return result


def numerical_factor(matrix: np.ndarray, cutoff: float):
    matrix = (matrix + matrix.T) / 2
    values, vectors = np.linalg.eigh(matrix)
    keep = values > cutoff
    return vectors[:, keep] * np.sqrt(values[keep]), values


def symmetric_coordinates(size):
    return [(i, j) for i in range(size) for j in range(i, size)]


def coefficient_rows(equations, factors):
    coordinates = [symmetric_coordinates(factor.shape[1]) for factor in factors]
    rows = []
    rhs = []
    for m0, m1, target, *_ in equations:
        blocks = []
        for matrix, factor, coords in zip((m0, m1), factors, coordinates):
            pulled = factor.T @ matrix @ factor
            blocks.extend(
                int(pulled[i, j]) if i == j else 2 * int(pulled[i, j])
                for i, j in coords
            )
        rows.append(blocks)
        rhs.append(target)
    return np.asarray(rows, dtype=object), np.asarray(rhs, dtype=object), coordinates


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("floating_certificate")
    parser.add_argument("output")
    parser.add_argument("--denominator", type=int, default=1_000_000)
    parser.add_argument("--correction-denominator", type=int, default=100_000_000)
    parser.add_argument("--cutoff", type=float, default=1e-7)
    args = parser.parse_args()

    data = np.load(args.floating_certificate)
    a, b = sp.Rational(str(data["left"])), sp.Rational(str(data["right"]))
    if (a, b) != (sp.Rational(1, 2), sp.Rational(1)):
        raise ValueError(f"expected [1/2,1], got [{a},{b}]")
    equations = scaled_equations(a, b)
    if "G0_1" in data.files:
        basis = rooted_basis(3, 1)
        transforms, _ = label_s3_irrep_transforms(basis)
        permutations = permutation_matrices(basis)
        floating_matrices = [
            reconstruct([data[f"G0_{index}"] for index in range(3)], transforms, permutations, 2),
            reconstruct([data[f"G1_{index}"] for index in range(3)], transforms, permutations, 1),
        ]
    else:
        floating_matrices = [data["G0_0"], data["G1_0"]]
    floating_factors = []
    for key, matrix in zip(("G0", "G1"), floating_matrices):
        factor, values = numerical_factor(matrix, args.cutoff)
        print(
            f"{key}: dimension={len(values)} rank={factor.shape[1]} "
            f"min={values[0]:.3e} first_kept={values[values > args.cutoff][0]:.3e}"
        )
        floating_factors.append(factor)
    denominator = args.denominator
    factors = [np.rint(factor * denominator).astype(np.int64) for factor in floating_factors]
    rows, rhs, coordinates = coefficient_rows(equations, factors)
    rhs = rhs * denominator**2

    identity_vector = []
    for factor, coords in zip(factors, coordinates):
        identity_vector.extend(1 if i == j else 0 for i, j in coords)
    identity_vector = np.asarray(identity_vector, dtype=object)
    residual = rhs - rows @ identity_vector

    rows_float = np.asarray(rows, dtype=float)
    row_norms = np.linalg.norm(rows_float, axis=1)
    normalized = rows_float / row_norms[:, None]
    residual_float = np.asarray(residual, dtype=float) / row_norms
    preliminary, *_ = np.linalg.lstsq(normalized, residual_float, rcond=1e-12)
    correction_denominator = args.correction_denominator
    preliminary_integer = np.rint(preliminary * correction_denominator).astype(np.int64)
    preliminary_vector = identity_vector * correction_denominator + preliminary_integer.astype(object)
    residual = rhs * correction_denominator - rows @ preliminary_vector

    _, diagonal, pivots = qr(normalized, pivoting=True, mode="economic")
    rank = int(np.count_nonzero(np.abs(np.diag(diagonal)) > 1e-10))
    if rank != len(equations):
        raise AssertionError((rank, len(equations)))
    selected = [int(index) for index in pivots[:rank]]
    selected_matrix = sp.polys.matrices.DomainMatrix.from_Matrix(
        sp.Matrix([[int(rows[i, j]) for j in selected] for i in range(rank)])
    )
    selected_rhs = sp.polys.matrices.DomainMatrix.from_Matrix(
        sp.Matrix([int(value) for value in residual])
    )
    solution_num, solution_den = selected_matrix.inv_den()
    correction_num = solution_num.matmul(selected_rhs).to_Matrix()
    correction = [Fraction(int(correction_num[i, 0]), int(solution_den)) for i in range(rank)]

    offsets = np.cumsum([0] + [len(item) for item in coordinates])
    correction_values = [Fraction(int(value), correction_denominator) for value in preliminary_integer]
    for global_index, value in zip(selected, correction):
        correction_values[global_index] += value / correction_denominator
    sparse = []
    row_radii = [[Fraction(0) for _ in range(factor.shape[1])] for factor in factors]
    diagonals = [[Fraction(1) for _ in range(factor.shape[1])] for factor in factors]
    for global_index, value in enumerate(correction_values):
        if not value:
            continue
        block = int(np.searchsorted(offsets[1:], global_index, side="right"))
        local_index = global_index - int(offsets[block])
        i, j = coordinates[block][local_index]
        sparse.append([block, i, j, value.numerator, value.denominator])
        if i == j:
            diagonals[block][i] += value
        else:
            row_radii[block][i] += abs(value)
            row_radii[block][j] += abs(value)

    margins = []
    for block in range(2):
        block_margins = [diagonals[block][i] - row_radii[block][i] for i in range(len(diagonals[block]))]
        margins.append(min(block_margins))
        print(
            f"Y{block}: order={len(diagonals[block])} exact_DD_margin="
            f"{float(margins[-1]):.6g} ({margins[-1]})"
        )
    if min(margins) <= 0:
        raise AssertionError("sparse exact correction is not positive definite")

    certificate = {
        "atlas": 43,
        "left": "1/2",
        "right": "1",
        "factor_denominator": denominator,
        "preliminary_correction_denominator": correction_denominator,
        "B0": factors[0].tolist(),
        "B1": factors[1].tolist(),
        "corrections": sparse,
        "equation_count": len(equations),
        "ranks": [factor.shape[1] for factor in factors],
        "dd_margins": [[item.numerator, item.denominator] for item in margins],
    }
    Path(args.output).write_text(json.dumps(certificate, separators=(",", ":")), encoding="utf-8")
    print(f"wrote {args.output} ({Path(args.output).stat().st_size} bytes)")


if __name__ == "__main__":
    main()
