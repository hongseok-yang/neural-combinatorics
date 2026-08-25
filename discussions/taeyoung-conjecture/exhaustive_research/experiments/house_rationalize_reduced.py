"""Rationalize the strictly feasible, fully face-reduced Atlas-43 SOS."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path

import numpy as np
import sympy as sp
from scipy.linalg import qr

from house_rationalize_full import coefficient_rows, scaled_equations


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("floating_certificate")
    parser.add_argument("output")
    parser.add_argument("--factor-denominator", type=int, default=10_000_000)
    parser.add_argument("--correction-denominator", type=int, default=1_000_000_000_000)
    args = parser.parse_args()

    data = np.load(args.floating_certificate)
    bases = [np.asarray(data["B0"], dtype=np.int64), np.asarray(data["B1"], dtype=np.int64)]
    grams = [np.asarray(data["Y0"]), np.asarray(data["Y1"])]
    factor_denominator = args.factor_denominator
    factors = []
    for index, (basis, gram) in enumerate(zip(bases, grams)):
        cholesky = np.linalg.cholesky((gram + gram.T) / 2)
        rational_cholesky = np.rint(cholesky * factor_denominator).astype(np.int64)
        factor = basis @ rational_cholesky
        factors.append(factor)
        print(
            f"factor {index}: shape={factor.shape} maxabs={np.max(np.abs(factor))} "
            f"cholesky_rounding={np.max(np.abs(cholesky-rational_cholesky/factor_denominator)):.3e}"
        )

    equations = scaled_equations(sp.Rational(1, 2), sp.Rational(1))
    rows, rhs, coordinates = coefficient_rows(equations, factors)
    rhs = rhs * factor_denominator**2
    identity = np.asarray(
        [1 if i == j else 0 for coords in coordinates for i, j in coords], dtype=object
    )

    rows_float = np.asarray(rows, dtype=float)
    rhs_float = np.asarray(rhs, dtype=float)
    _, triangular, row_pivots = qr(rows_float.T, pivoting=True, mode="economic")
    row_tolerance = max(rows_float.shape) * np.finfo(float).eps * abs(triangular[0, 0])
    rank = int(np.count_nonzero(np.abs(np.diag(triangular)) > row_tolerance))
    selected_rows = sorted(int(index) for index in row_pivots[:rank])
    work_rows = rows[selected_rows, :]
    work_rhs = rhs[selected_rows]
    row_norms = np.linalg.norm(rows_float[selected_rows], axis=1)
    normalized = rows_float[selected_rows] / row_norms[:, None]
    residual_float = (
        np.asarray(work_rhs - work_rows @ identity, dtype=float) / row_norms
    )
    preliminary, *_ = np.linalg.lstsq(normalized, residual_float, rcond=1e-14)
    correction_denominator = args.correction_denominator
    preliminary_integer = np.rint(preliminary * correction_denominator).astype(np.int64)
    preliminary_vector = identity * correction_denominator + preliminary_integer.astype(object)
    exact_residual = work_rhs * correction_denominator - work_rows @ preliminary_vector

    _, column_triangular, column_pivots = qr(normalized, pivoting=True, mode="economic")
    column_rank = int(np.count_nonzero(np.abs(np.diag(column_triangular)) > 1e-12))
    if column_rank != rank:
        raise AssertionError((rank, column_rank))
    selected_columns = [int(index) for index in column_pivots[:rank]]
    exact_matrix = sp.polys.matrices.DomainMatrix.from_Matrix(
        sp.Matrix([[int(work_rows[i, j]) for j in selected_columns] for i in range(rank)])
    )
    exact_rhs = sp.polys.matrices.DomainMatrix.from_Matrix(
        sp.Matrix([int(value) for value in exact_residual])
    )
    inverse_num, inverse_den = exact_matrix.inv_den()
    final_num = inverse_num.matmul(exact_rhs).to_Matrix()
    corrections = [Fraction(int(value), correction_denominator) for value in preliminary_integer]
    for column, numerator in zip(selected_columns, final_num):
        corrections[column] += Fraction(int(numerator), int(inverse_den) * correction_denominator)

    offsets = np.cumsum([0] + [len(item) for item in coordinates])
    diagonals = [[Fraction(1) for _ in range(factor.shape[1])] for factor in factors]
    radii = [[Fraction(0) for _ in range(factor.shape[1])] for factor in factors]
    sparse = []
    for global_index, value in enumerate(corrections):
        if not value:
            continue
        block = int(np.searchsorted(offsets[1:], global_index, side="right"))
        i, j = coordinates[block][global_index - int(offsets[block])]
        sparse.append([block, i, j, value.numerator, value.denominator])
        if i == j:
            diagonals[block][i] += value
        else:
            radii[block][i] += abs(value)
            radii[block][j] += abs(value)
    margins = [
        min(diagonal - radius for diagonal, radius in zip(block_diagonal, block_radius))
        for block_diagonal, block_radius in zip(diagonals, radii)
    ]
    print(f"equation_rank={rank} DD_margins={[float(item) for item in margins]}")
    if min(margins) <= 0:
        raise AssertionError("corrected matrices are not strictly diagonally dominant")

    # Independent exact coefficient check, including the ten equations dropped
    # as redundant after facial reduction.
    exact_vector = [Fraction(int(value)) + correction for value, correction in zip(identity, corrections)]
    for equation_index, (row, target) in enumerate(zip(rows, rhs)):
        actual = sum(Fraction(int(coefficient)) * value for coefficient, value in zip(row, exact_vector))
        if actual != Fraction(int(target)):
            raise AssertionError((equation_index, actual, target))
    print(f"all {len(equations)} exact coefficient equations verified")

    certificate = {
        "atlas": 43,
        "interval": ["1/2", "1"],
        "factor_denominator": factor_denominator,
        "F0": factors[0].tolist(),
        "F1": factors[1].tolist(),
        "corrections": sparse,
        "orders": [factor.shape[1] for factor in factors],
        "dd_margins": [[item.numerator, item.denominator] for item in margins],
    }
    output = Path(args.output)
    output.write_text(json.dumps(certificate, separators=(",", ":")), encoding="utf-8")
    print(f"wrote {output} ({output.stat().st_size} bytes)")


if __name__ == "__main__":
    main()
