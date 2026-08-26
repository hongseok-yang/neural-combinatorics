"""Probe lower-height exact residual solves for an S4 SOS certificate.

The existing rationalizer rounds a numerical correction to a fixed
denominator and then solves an exact residual system on one square set of
floating-QR pivot columns.  Those square determinants are responsible for the
several-thousand-digit exceptional fractions.  This diagnostic reconstructs
that system from a certificate and measures alternative column lattices before
we change the certificate-producing path.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np
import sympy as sp
from flint import fmpq_mat, fmpz_mat
from scipy.linalg import qr

from s4_interval_rationalize import NAMES, coefficient_rows, exact_equations


sys.set_int_max_str_digits(0)


def nearest_integer(value: Fraction) -> int:
    """Round a Fraction to nearest, with halves away from zero."""
    if value < 0:
        return -nearest_integer(-value)
    return (2 * value.numerator + value.denominator) // (2 * value.denominator)


def digit_count(value: int) -> int:
    return len(str(abs(value))) if value else 1


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate")
    parser.add_argument(
        "--extra-columns", type=int, default=0,
        help="add this many post-rank QR columns before column-HNF",
    )
    parser.add_argument(
        "--exchange-candidates", type=int, default=0,
        help="consider this many post-rank QR columns for determinant-reducing exchanges",
    )
    parser.add_argument("--exchange-rounds", type=int, default=1)
    parser.add_argument(
        "--snf-extra-columns", type=int, default=0,
        help="measure the column-lattice index after adding QR columns",
    )
    args = parser.parse_args()

    certificate = json.loads(Path(args.certificate).read_text(encoding="utf-8"))
    transforms = [
        np.asarray(certificate["young_bases"][name], dtype=np.int64)
        for name in NAMES
    ]
    equations, _, _, _ = exact_equations(
        int(certificate["atlas"]),
        sp.Rational(certificate["interval"][0]),
        sp.Rational(certificate["interval"][1]),
        int(certificate["label_degree"]),
        certificate.get("degree_three_kind", "all"),
        int(certificate.get("polynomial_degree", 2)),
        young_transforms=transforms,
    )
    factors = [np.asarray(value, dtype=np.int64) for value in certificate["factors"]]
    rows, rhs, coordinates = coefficient_rows(equations, factors)
    rhs = rhs * int(certificate["factor_denominator"]) ** 2

    denominator = int(certificate.get("correction_denominator", 0))
    if not denominator:
        denominator_counts: dict[int, int] = {}
        for *_, entry_denominator in certificate["corrections"]:
            value = int(entry_denominator)
            denominator_counts[value] = denominator_counts.get(value, 0) + 1
        denominator = max(denominator_counts, key=denominator_counts.get)

    offsets = np.cumsum([0] + [len(block) for block in coordinates])
    current = [Fraction(0) for _ in range(int(offsets[-1]))]
    coordinate_lookup = [
        {coordinate: index for index, coordinate in enumerate(block)}
        for block in coordinates
    ]
    exceptional_columns = []
    for block, i, j, numerator, entry_denominator in certificate["corrections"]:
        block, i, j = int(block), int(i), int(j)
        index = int(offsets[block]) + coordinate_lookup[block][(i, j)]
        current[index] = Fraction(int(numerator), int(entry_denominator))
        if denominator % int(entry_denominator):
            exceptional_columns.append(index)

    identity = np.asarray(
        [1 if i == j else 0 for block in coordinates for i, j in block],
        dtype=object,
    )
    preliminary_correction = np.asarray(
        [nearest_integer(value * denominator) for value in current], dtype=object
    )
    preliminary = identity * denominator + preliminary_correction
    residual = rhs * denominator - rows @ preliminary

    rows_float = np.asarray(rows, dtype=float)
    _, triangular, row_pivots = qr(rows_float.T, pivoting=True, mode="economic")
    tolerance = max(rows_float.shape) * np.finfo(float).eps * abs(triangular[0, 0])
    rank = int(np.count_nonzero(np.abs(np.diag(triangular)) > tolerance))
    selected_rows = sorted(int(index) for index in row_pivots[:rank])
    work_rows = rows[selected_rows, :]
    work_residual = residual[selected_rows]

    if len(exceptional_columns) != rank:
        raise AssertionError(("exceptional columns", len(exceptional_columns), rank))
    square = fmpz_mat([
        [int(work_rows[i, j]) for j in exceptional_columns]
        for i in range(rank)
    ])
    solution = square.solve(fmpz_mat([[int(value)] for value in work_residual]))
    reconstructed = preliminary.copy()
    numerator_digits = 1
    denominator_digits = 1
    nonintegral = 0
    for column, value in zip(exceptional_columns, solution.entries()):
        rational = Fraction(int(value.numerator), int(value.denominator))
        reconstructed[column] += rational
        numerator_digits = max(numerator_digits, digit_count(rational.numerator))
        denominator_digits = max(denominator_digits, digit_count(rational.denominator))
        nonintegral += rational.denominator != 1
    expected = np.asarray([
        Fraction(identity[index]) + current[index]
        for index in range(len(current))
    ], dtype=object) * denominator
    if any(Fraction(reconstructed[i]) != expected[i] for i in range(len(current))):
        raise AssertionError("failed to reconstruct current residual solution")
    determinant = int(square.det())
    print(
        f"atlas={certificate['atlas']} equations={len(equations)} rank={rank} "
        f"variables={rows.shape[1]} denominator={denominator}"
    )
    print(
        f"current_pivots={len(exceptional_columns)} det_digits={digit_count(determinant)} "
        f"solution_num_digits={numerator_digits} "
        f"solution_den_digits={denominator_digits} nonintegral={nonintegral}"
    )

    def audit_solution(
        chosen: list[int], values: fmpq_mat, label: str,
    ) -> None:
        proposed = preliminary.copy()
        solution_num_digits = 1
        solution_den_digits = 1
        solution_nonintegral = 0
        max_absolute = Fraction(0)
        rational_values = []
        for column, value in zip(chosen, values.entries()):
            rational = Fraction(int(value.numerator), int(value.denominator))
            rational_values.append(rational)
            proposed[column] += rational
            solution_num_digits = max(
                solution_num_digits, digit_count(rational.numerator)
            )
            solution_den_digits = max(
                solution_den_digits, digit_count(rational.denominator)
            )
            solution_nonintegral += rational.denominator != 1
            max_absolute = max(max_absolute, abs(rational))

        # Audit all equations, not merely the independent subsystem used to
        # build the solution.  Only the selected coordinates are rational.
        for equation_index, row in enumerate(rows):
            actual_residual = sum(
                Fraction(int(row[column])) * value
                for column, value in zip(chosen, rational_values)
            )
            if actual_residual != int(residual[equation_index]):
                raise AssertionError(("equation", equation_index))

        diagonals = [[Fraction(1) for _ in factor_coordinates]
                     for factor_coordinates in coordinates]
        radii = [[Fraction(0) for _ in factor_coordinates]
                 for factor_coordinates in coordinates]
        exceptional_count = 0
        correction_num_digits = 1
        correction_den_digits = 1
        for block, factor_coordinates in enumerate(coordinates):
            for local, (i, j) in enumerate(factor_coordinates):
                value = Fraction(proposed[int(offsets[block]) + local], denominator)
                correction = value - (1 if i == j else 0)
                if correction:
                    correction_num_digits = max(
                        correction_num_digits, digit_count(correction.numerator)
                    )
                    correction_den_digits = max(
                        correction_den_digits, digit_count(correction.denominator)
                    )
                    exceptional_count += denominator % correction.denominator != 0
                if i == j:
                    diagonals[block][i] = value
                else:
                    radii[block][i] += abs(value)
                    radii[block][j] += abs(value)
        margins = [
            min(diagonal - radius for diagonal, radius in zip(block_diagonal, block_radius))
            for block_diagonal, block_radius in zip(diagonals, radii)
        ]
        print(
            f"{label}_solution_num_digits={solution_num_digits} "
            f"{label}_solution_den_digits={solution_den_digits} "
            f"{label}_nonintegral={solution_nonintegral} "
            f"max_abs={float(max_absolute):.3e}"
        )
        print(
            f"{label}_exceptional={exceptional_count} "
            f"correction_num_digits={correction_num_digits} "
            f"correction_den_digits={correction_den_digits} "
            f"min_dd_margin={float(min(margins)):.3e}"
        )

    if (args.extra_columns <= 0 and args.exchange_candidates <= 0
            and args.snf_extra_columns <= 0):
        return

    row_norms = np.linalg.norm(rows_float[selected_rows], axis=1)
    normalized = rows_float[selected_rows] / row_norms[:, None]
    _, _, column_pivots = qr(normalized, pivoting=True, mode="economic")
    exceptional_set = set(exceptional_columns)
    candidate_order = [
        int(column) for column in column_pivots
        if int(column) not in exceptional_set
    ]

    if args.snf_extra_columns > 0:
        snf_columns = exceptional_columns + candidate_order[:args.snf_extra_columns]
        snf_matrix = fmpz_mat([
            [int(work_rows[i, j]) for j in snf_columns]
            for i in range(rank)
        ])
        print(
            f"computing SNF index with {len(snf_columns)} generators",
            flush=True,
        )
        smith = snf_matrix.snf()
        lattice_index = 1
        for index in range(rank):
            lattice_index *= abs(int(smith[index, index]))
        print(
            f"snf_extra={args.snf_extra_columns} "
            f"lattice_index_digits={digit_count(lattice_index)}",
            flush=True,
        )

    if args.exchange_candidates > 0:
        exchanged_columns = exceptional_columns.copy()
        exchange_square = square
        exchange_determinant = determinant
        available = candidate_order[:args.exchange_candidates]
        for round_index in range(args.exchange_rounds):
            if not available:
                break
            candidate_matrix = fmpz_mat([
                [int(work_rows[i, column]) for column in available]
                for i in range(rank)
            ])
            coordinates_in_basis = exchange_square.solve(candidate_matrix)
            best: tuple[int, int, int, int] | None = None
            for candidate_index, column in enumerate(available):
                for position in range(rank):
                    coordinate = coordinates_in_basis[position, candidate_index]
                    if not coordinate:
                        continue
                    replacement = Fraction(exchange_determinant) * Fraction(
                        int(coordinate.numerator), int(coordinate.denominator)
                    )
                    if replacement.denominator != 1:
                        raise AssertionError("nonintegral replacement determinant")
                    candidate_value = (
                        abs(replacement.numerator), position, column,
                        replacement.numerator,
                    )
                    if best is None or candidate_value[0] < best[0]:
                        best = candidate_value
            if best is None or best[0] >= abs(exchange_determinant):
                print(f"exchange_round={round_index + 1} no improving exchange")
                break
            _, position, column, exchange_determinant = best
            removed = exchanged_columns[position]
            exchanged_columns[position] = column
            available.remove(column)
            available.append(removed)
            exchange_square = fmpz_mat([
                [int(work_rows[i, j]) for j in exchanged_columns]
                for i in range(rank)
            ])
            print(
                f"exchange_round={round_index + 1} removed={removed} added={column} "
                f"det_digits={digit_count(exchange_determinant)}",
                flush=True,
            )
        exchange_solution = exchange_square.solve(
            fmpz_mat([[int(value)] for value in work_residual])
        )
        audit_solution(exchanged_columns, exchange_solution, "exchange")

    if args.extra_columns <= 0:
        return

    candidates = candidate_order[:args.extra_columns]
    chosen_columns = exceptional_columns + candidates
    column_matrix = fmpz_mat([
        [int(work_rows[i, j]) for j in chosen_columns]
        for i in range(rank)
    ])
    print(
        f"computing column HNF with {len(chosen_columns)} generators "
        f"({len(candidates)} extra)", flush=True,
    )
    hnf, transform = column_matrix.transpose().hnf(transform=True)
    if any(hnf[i, j] for i in range(rank, hnf.nrows()) for j in range(rank)):
        raise AssertionError("unexpected nonzero HNF tail")
    hnf_basis = fmpz_mat([[hnf[i, j] for i in range(rank)] for j in range(rank)])
    basis_solution = hnf_basis.solve(
        fmpz_mat([[int(value)] for value in work_residual])
    )
    extended_solution = fmpq_mat(len(chosen_columns), 1)
    for index in range(rank):
        extended_solution[index, 0] = basis_solution[index, 0]
    lattice_solution = transform.transpose() * extended_solution
    audit_solution(chosen_columns, lattice_solution, "hnf")


if __name__ == "__main__":
    main()
