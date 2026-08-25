"""Exact rationalization of a face-reduced S4 interval SOS certificate."""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

import networkx as nx
import numpy as np
import sympy as sp
from networkx.algorithms.polynomials import chromatic_polynomial
from scipy.linalg import qr

from full_s4_interval_sos import raw_by_isolated
from full_s4_rooted_sos import young_integer_transforms
from rooted_sos_search import fixed_density_key


NAMES = ["4", "31", "22", "211", "1111"]


def coefficients(expression, variable, degree=5):
    polynomial = sp.Poly(sp.expand(expression), variable, domain=sp.QQ)
    return [sp.Rational(polynomial.nth(power)) for power in range(degree + 1)]


def exact_equations(
    atlas: int, left: sp.Rational, right: sp.Rational, label_degree: int,
    degree_three_kind: str = "all",
    polynomial_degree: int = 2,
):
    if polynomial_degree not in (2, 4):
        raise ValueError(polynomial_degree)
    order0 = polynomial_degree // 2 + 1
    order1 = polynomial_degree // 2
    transforms, factors, names, basis_indices = young_integer_transforms(
        label_degree, degree_three_kind
    )
    if names != NAMES or factors != [24] * 5:
        raise AssertionError((names, factors))
    raw = raw_by_isolated(basis_indices)
    pulled = {}
    for key, matrix in raw.items():
        pulled[key] = []
        for transform in transforms:
            value = transform.T @ matrix @ transform
            rounded = np.rint(value).astype(np.int64)
            if np.max(np.abs(value - rounded)) > 1e-8:
                raise AssertionError("nonintegral Young pullback")
            pulled[key].append(rounded)

    t = sp.symbols("t")
    p = left + (right - left) * t
    max_isolated = max(isolated for _, isolated in pulled)
    max_power = max(5, max_isolated + polynomial_degree)
    density = {
        isolated: coefficients(p**isolated, t, max_power)
        for isolated in range(max_isolated + 1)
    }
    graph = nx.graph_atlas(atlas)
    target_core, isolated = fixed_density_key(graph)
    if isolated:
        raise AssertionError("target must be connected")
    chromatic = chromatic_polynomial(graph)
    x = next(iter(chromatic.free_symbols))
    phi = sp.factor((1 - p) ** graph.number_of_nodes() * chromatic.subs(x, 1 / (1 - p)))
    target = {
        target_core: coefficients(sp.Integer(1), t, max_power),
        0: coefficients(-phi, t, max_power),
    }
    original_sizes = [transform.shape[1] for transform in transforms]
    zero_blocks = [np.zeros((size, size), dtype=np.int64) for size in original_sizes]
    cores = sorted(set(core for core, _ in pulled) | set(target))
    equations = []
    for core in cores:
        for power in range(max_power + 1):
            scalar_terms0 = []
            scalar_terms1 = []
            for isolated_count in range(max_isolated + 1):
                values = density[isolated_count]
                for u in range(order0):
                    for v in range(order0):
                        index = power - u - v
                        if 0 <= index < len(values) and values[index]:
                            scalar_terms0.append((isolated_count, u, v, values[index]))
                for u in range(order1):
                    for v in range(order1):
                        value1 = sp.Rational(0)
                        index = power - 1 - u - v
                        if 0 <= index < len(values):
                            value1 += values[index]
                        index = power - 2 - u - v
                        if 0 <= index < len(values):
                            value1 -= values[index]
                        if value1:
                            scalar_terms1.append((isolated_count, u, v, value1))
            rhs = target.get(core, [sp.Rational(0)] * (max_power + 1))[power]
            used = any(
                np.any(pulled.get((core, isolated_count), zero_blocks)[block])
                for isolated_count, *_ in scalar_terms0
                for block in range(5)
            ) or any(
                np.any(pulled.get((core, isolated_count), zero_blocks)[block])
                for isolated_count, *_ in scalar_terms1
                for block in range(5)
            )
            if not used and not rhs:
                continue
            denominators = [rhs.q]
            denominators.extend(value.q for *_, value in scalar_terms0)
            denominators.extend(value.q for *_, value in scalar_terms1)
            scale = int(sp.ilcm(*denominators))
            blocks0 = []
            blocks1 = []
            for block, size in enumerate(original_sizes):
                matrix0 = np.zeros((order0 * size, order0 * size), dtype=np.int64)
                matrix1 = np.zeros((order1 * size, order1 * size), dtype=np.int64)
                for isolated_count, u, v, value in scalar_terms0:
                    source = pulled.get((core, isolated_count), zero_blocks)[block]
                    matrix0[u*size:(u+1)*size, v*size:(v+1)*size] += int(scale * value) * source
                for isolated_count, u, v, value in scalar_terms1:
                    source = pulled.get((core, isolated_count), zero_blocks)[block]
                    matrix1[u*size:(u+1)*size, v*size:(v+1)*size] += int(scale * value) * source
                blocks0.append(24 * matrix0)
                blocks1.append(24 * matrix1)
            equations.append((blocks0 + blocks1, int(scale * rhs), core, power, scale))
    return equations, transforms, basis_indices, sp.factor(phi)


def coefficient_rows(equations, factors):
    coordinates = [
        [(i, j) for i in range(factor.shape[1]) for j in range(i, factor.shape[1])]
        for factor in factors
    ]
    rows = []
    rhs = []
    for matrices, target, *_ in equations:
        pieces = []
        for matrix, factor, coords in zip(matrices, factors, coordinates):
            pulled = factor.astype(object).T @ matrix.astype(object) @ factor.astype(object)
            pieces.extend(
                int(pulled[i, j]) if i == j else 2 * int(pulled[i, j])
                for i, j in coords
            )
        rows.append(pieces)
        rhs.append(target)
    return np.asarray(rows, dtype=object), np.asarray(rhs, dtype=object), coordinates


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("floating_certificate")
    parser.add_argument("output")
    parser.add_argument("--atlas", type=int, default=181)
    parser.add_argument("--left", default="2/3")
    parser.add_argument("--right", default="1")
    parser.add_argument("--label-degree", type=int, default=2)
    parser.add_argument("--polynomial-degree", type=int, choices=(2, 4), default=2)
    parser.add_argument(
        "--degree-three-kind", choices=(
            "all", "triangle", "star", "path", "paw4", "cycle4",
            "triangle_paw4", "star_paw4", "path_paw4", "all3_paw4",
            "all4", "none"
        ),
        default="all",
    )
    parser.add_argument("--factor-denominator", type=int, default=1_000_000)
    parser.add_argument("--correction-denominator", type=int, default=100_000_000_000)
    args = parser.parse_args()

    data = np.load(args.floating_certificate)
    gram_labels = [f"G0_{name}" for name in NAMES] + [f"G1_{name}" for name in NAMES]
    complement_labels = [f"C0_{name}" for name in NAMES] + [f"C1_{name}" for name in NAMES]
    reduction_norm_labels = (
        [f"reduction_norm0_{name}" for name in NAMES]
        + [f"reduction_norm1_{name}" for name in NAMES]
    )
    face_complements = [np.asarray(data[label], dtype=np.int64) for label in complement_labels]
    numerical_grams = []
    for gram_label, norm_label in zip(gram_labels, reduction_norm_labels):
        gram = np.asarray(data[gram_label])
        norm = np.asarray(data[norm_label])
        numerical_grams.append(gram / norm[:, None] / norm[None, :])

    denominator = args.factor_denominator
    factors = []
    for label, complement, gram in zip(gram_labels, face_complements, numerical_grams):
        cholesky = np.linalg.cholesky((gram + gram.T) / 2)
        rational_cholesky = np.rint(cholesky * denominator).astype(np.int64)
        factor = complement @ rational_cholesky
        factors.append(factor)
        print(
            f"{label}: factor={factor.shape} maxabs={np.max(np.abs(factor))} "
            f"rounding={np.max(np.abs(cholesky-rational_cholesky/denominator)):.3e}",
            flush=True,
        )

    left, right = sp.Rational(args.left), sp.Rational(args.right)
    equations, transforms, basis_indices, phi = exact_equations(
        args.atlas, left, right, args.label_degree, args.degree_three_kind,
        args.polynomial_degree,
    )
    rows, rhs, coordinates = coefficient_rows(equations, factors)
    rhs = rhs * denominator**2
    identity = np.asarray(
        [1 if i == j else 0 for coords in coordinates for i, j in coords], dtype=object
    )
    rows_float = np.asarray(rows, dtype=float)
    rhs_float = np.asarray(rhs, dtype=float)
    _, triangular, row_pivots = qr(rows_float.T, pivoting=True, mode="economic")
    tolerance = max(rows_float.shape) * np.finfo(float).eps * abs(triangular[0, 0])
    rank = int(np.count_nonzero(np.abs(np.diag(triangular)) > tolerance))
    selected_rows = sorted(int(index) for index in row_pivots[:rank])
    work_rows = rows[selected_rows, :]
    work_rhs = rhs[selected_rows]
    row_norms = np.linalg.norm(rows_float[selected_rows], axis=1)
    normalized = rows_float[selected_rows] / row_norms[:, None]
    residual_float = np.asarray(work_rhs - work_rows @ identity, dtype=float) / row_norms
    preliminary, *_ = np.linalg.lstsq(normalized, residual_float, rcond=1e-13)
    correction_denominator = args.correction_denominator
    preliminary_integer = np.rint(preliminary * correction_denominator).astype(np.int64)
    preliminary_vector = identity * correction_denominator + preliminary_integer.astype(object)
    exact_residual = work_rhs * correction_denominator - work_rows @ preliminary_vector
    print(
        f"equations={len(equations)} rank={rank} variables={rows.shape[1]} "
        f"preliminary_max={np.max(np.abs(preliminary)):.3e}", flush=True,
    )

    _, column_triangular, column_pivots = qr(normalized, pivoting=True, mode="economic")
    column_rank = int(np.count_nonzero(np.abs(np.diag(column_triangular)) > 1e-11))
    if column_rank != rank:
        raise AssertionError((rank, column_rank))
    selected_columns = [int(index) for index in column_pivots[:rank]]
    corrections = [Fraction(int(value), correction_denominator) for value in preliminary_integer]
    exact_rows = [
        [int(work_rows[i, j]) for j in selected_columns] for i in range(rank)
    ]
    exact_values = [int(value) for value in exact_residual]
    try:
        from flint import fmpz_mat

        solution = fmpz_mat(exact_rows).solve(fmpz_mat([[value] for value in exact_values]))
        exact_corrections = [
            Fraction(int(solution[index, 0].numerator), int(solution[index, 0].denominator))
            for index in range(rank)
        ]
    except ImportError:
        exact_matrix = sp.polys.matrices.DomainMatrix.from_Matrix(sp.Matrix(exact_rows))
        exact_rhs = sp.polys.matrices.DomainMatrix.from_Matrix(sp.Matrix(exact_values))
        solution_num, solution_den = exact_matrix.solve_den(exact_rhs, method="rref")
        exact_corrections = [
            Fraction(int(numerator), int(solution_den))
            for numerator in solution_num.to_Matrix()
        ]
    for column, value in zip(selected_columns, exact_corrections):
        corrections[column] += value / correction_denominator

    offsets = np.cumsum([0] + [len(item) for item in coordinates])
    diagonals = [[Fraction(1) for _ in range(factor.shape[1])] for factor in factors]
    radii = [[Fraction(0) for _ in range(factor.shape[1])] for factor in factors]
    sparse_corrections = []
    for global_index, value in enumerate(corrections):
        if not value:
            continue
        block = int(np.searchsorted(offsets[1:], global_index, side="right"))
        i, j = coordinates[block][global_index - int(offsets[block])]
        sparse_corrections.append([block, i, j, value.numerator, value.denominator])
        if i == j:
            diagonals[block][i] += value
        else:
            radii[block][i] += abs(value)
            radii[block][j] += abs(value)
    margins = [
        min(diagonal - radius for diagonal, radius in zip(block_diagonal, block_radius))
        for block_diagonal, block_radius in zip(diagonals, radii)
    ]
    print(f"DD margins={[float(value) for value in margins]}", flush=True)
    if min(margins) <= 0:
        raise AssertionError("rational correction lost positive definiteness")

    selected_row_set = set(selected_rows)
    for equation_index, (row, target) in enumerate(zip(rows, rhs)):
        if equation_index in selected_row_set:
            # These equations are exact by the defining integer solve above.
            continue
        actual = Fraction(int(row @ preliminary_vector), correction_denominator)
        actual += sum(
            Fraction(int(row[column]), correction_denominator) * value
            for column, value in zip(selected_columns, exact_corrections)
            if row[column]
        )
        if actual != Fraction(int(target)):
            raise AssertionError((equation_index, actual, target))
    print(
        f"all {len(equations)} exact equations verified "
        f"({rank} defining, {len(equations)-rank} redundant checks)", flush=True,
    )

    certificate = {
        "atlas": args.atlas,
        "interval": [str(left), str(right)],
        "label_degree": args.label_degree,
        "degree_three_kind": args.degree_three_kind,
        "polynomial_degree": args.polynomial_degree,
        "factor_denominator": denominator,
        "basis_indices": basis_indices,
        "phi": str(phi),
        "names": NAMES,
        "young_bases": {
            name: transform.tolist() for name, transform in zip(NAMES, transforms)
        },
        "factors": [factor.tolist() for factor in factors],
        "orders": [factor.shape[1] for factor in factors],
        "corrections": sparse_corrections,
        "dd_margins": [[value.numerator, value.denominator] for value in margins],
    }
    output = Path(args.output)
    output.write_text(json.dumps(certificate, separators=(",", ":")), encoding="utf-8")
    print(f"wrote {output} ({output.stat().st_size} bytes)")


if __name__ == "__main__":
    main()
