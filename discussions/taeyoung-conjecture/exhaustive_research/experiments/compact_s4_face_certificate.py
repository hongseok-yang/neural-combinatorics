"""Rationalize an S4 certificate in a small integer basis of its exact face.

This is an untrusted discovery/export tool.  It changes coordinates before
rounding the Gram matrices, rather than solving the residual in a rounded
Cholesky basis with million-sized entries.  The output needs a separate Lean
coefficient, positivity and graphon audit before it can close a catalogue row.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
import time
from fractions import Fraction
from math import lcm
from pathlib import Path

# Keep discovery within the sequential resource envelope too.
os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["OMP_NUM_THREADS"] = "1"
os.environ["MKL_NUM_THREADS"] = "1"

import numpy as np
import sympy as sp
from flint import fmpq, fmpq_mat, fmpz_mat, nmod_mat
from scipy.linalg import qr

from s4_interval_rationalize import NAMES, exact_equations

sys.set_int_max_str_digits(0)


def integer_face(factor: list[list[int]]):
    reduced, rank = fmpq_mat(factor).transpose().rref()
    rows = reduced.tolist()[:rank]
    pivots = [next(j for j, x in enumerate(row) if x) for row in rows]
    scales = [lcm(*(int(x.denominator) for x in row)) for row in rows]
    basis = [[int(rows[j][i] * scales[j]) for j in range(rank)]
             for i in range(len(factor))]
    coordinates = fmpq_mat([
        [fmpq(x, scales[j]) for x in factor[pivots[j]]]
        for j in range(rank)
    ])
    assert fmpq_mat(basis) * coordinates == fmpq_mat(factor)
    return basis, coordinates


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate")
    parser.add_argument("output")
    parser.add_argument("--rounding-denominator", type=int, default=10**12)
    parser.add_argument("--pivot-method", choices=("qr", "sparse"), default="sparse")
    args = parser.parse_args()
    started = time.monotonic()
    source = Path(args.certificate)
    certificate = json.loads(source.read_text(encoding="utf-8"))
    bases, coordinates = zip(*(integer_face(f) for f in certificate["factors"]))
    print("integer face bases", [(len(b), len(b[0]), max(abs(x) for r in b for x in r))
                                  for b in bases], flush=True)
    transformations = [np.array(certificate["young_bases"][name], dtype=np.int64)
                       for name in NAMES]
    equations, _, _, phi = exact_equations(
        int(certificate["atlas"]), *map(sp.Rational, certificate["interval"]),
        int(certificate["label_degree"]), certificate.get("degree_three_kind", "all"),
        int(certificate.get("polynomial_degree", 2)), transformations,
    )
    print("equations reconstructed", len(equations), round(time.monotonic()-started, 2), flush=True)
    orders = [len(b[0]) for b in bases]
    entries = [[(i, j) for i in range(n) for j in range(i, n)] for n in orders]
    matrices = [fmpz_mat(b) for b in bases]
    rows = []
    for equation, *_ in equations:
        row = []
        for m, basis, pairs in zip(equation, matrices, entries):
            pulled = basis.transpose() * fmpz_mat(m.tolist()) * basis
            row.extend(int(pulled[i, j]) * (1 if i == j else 2) for i, j in pairs)
        rows.append(row)
    integer_rows = fmpz_mat(rows)
    rhs = [int(e[1]) for e in equations]
    print("small coefficient matrix", len(rows), len(rows[0]),
          "max", max(abs(x) for r in rows for x in r),
          "seconds", round(time.monotonic()-started, 2), flush=True)

    # Floating point only chooses a nearby rational candidate and pivot set.
    zs = [np.eye(n) for n in orders]
    for block, i, j, numerator, denominator in certificate["corrections"]:
        value = float(Fraction(int(numerator), int(denominator)))
        zs[block][i, j] += value
        if i != j:
            zs[block][j, i] += value
    approximate = []
    min_eigenvalues = []
    for coordinate, z, pairs in zip(coordinates, zs, entries):
        a = np.array([[float(x) for x in r] for r in coordinate.tolist()])
        gram = a @ z @ a.T / int(certificate["factor_denominator"])**2
        approximate.extend(gram[i, j] for i, j in pairs)
        min_eigenvalues.append(float(np.linalg.eigvalsh(gram)[0]))
    print("approximate minimum eigenvalues", min_eigenvalues, flush=True)
    rounding = args.rounding_denominator
    preliminary = [int(round(float(x) * rounding)) for x in approximate]
    residual = fmpz_mat([[target * rounding] for target in rhs]) - integer_rows * fmpz_mat([[x] for x in preliminary])
    floating = np.asarray(rows, dtype=float)
    _, triangular, row_order = qr(floating.T, pivoting=True, mode="economic")
    tolerance = max(floating.shape) * np.finfo(float).eps * abs(triangular[0, 0])
    rank = int(np.count_nonzero(np.abs(np.diag(triangular)) > tolerance))
    selected_rows = sorted(int(x) for x in row_order[:rank])
    if args.pivot_method == "qr":
        normalized = floating[selected_rows]
        normalized /= np.linalg.norm(normalized, axis=1)[:, None]
        _, _, column_order = qr(normalized, pivoting=True, mode="economic")
        selected_columns = [int(x) for x in column_order[:rank]]
    else:
        # Favor columns with small support and small entries.  Modular RREF
        # selects independent columns; the subsequent rational solve and ALL
        # equation checks, rather than the modular calculation, establish exactness.
        column_order = sorted(range(len(rows[0])), key=lambda j: (
            np.count_nonzero(floating[:, j]), np.max(np.abs(floating[:, j])), j))
        modular = nmod_mat([[rows[i][j] for j in column_order] for i in selected_rows], 1000003)
        reduced, modular_rank = modular.rref()
        assert modular_rank == rank
        selected_columns = []
        first = 0
        for i in range(rank):
            while not reduced[i, first]:
                first += 1
            selected_columns.append(column_order[first])
            first += 1
    square = fmpz_mat([[rows[i][j] for j in selected_columns] for i in selected_rows])
    solution = square.solve(fmpz_mat([[int(residual[i, 0])] for i in selected_rows]))
    values = [Fraction(x, rounding) for x in preliminary]
    for index, correction in zip(selected_columns, solution.entries()):
        values[index] += Fraction(int(correction.numerator), int(correction.denominator) * rounding)
    denominator = lcm(*(x.denominator for x in values))
    scaled_values = [int(x * denominator) for x in values]
    actual = integer_rows * fmpz_mat([[x] for x in scaled_values])
    assert actual == fmpz_mat([[x * denominator] for x in rhs])
    print("ALL coefficient equations exact", len(rows), "rank", rank,
          "common denominator digits", len(str(denominator)),
          "seconds", round(time.monotonic()-started, 2), flush=True)
    grams = []
    offset = 0
    for order, pairs in zip(orders, entries):
        gram = [[0 for _ in range(order)] for _ in range(order)]
        for (i, j), x in zip(pairs, scaled_values[offset:offset + len(pairs)]):
            gram[i][j] = gram[j][i] = x
        grams.append(gram)
        offset += len(pairs)

    # Congruence by a nonsingular integer triangular matrix gives an exact
    # diagonally dominant matrix.  This avoids principal minors whose heights
    # grow proportionally to the matrix order.  Cholesky is only a proposal for
    # the integer matrix; multiplication and dominance are checked exactly.
    positivity = []
    for block, gram in enumerate(grams):
        n = len(gram)
        floating_gram = np.array([[float(Fraction(x, denominator)) for x in row] for row in gram])
        lower = np.linalg.cholesky(floating_gram)
        proposed = np.linalg.inv(lower.T) * 10**6
        preconditioner = [[int(round(proposed[i, j])) if i <= j else 0 for j in range(n)]
                          for i in range(n)]
        assert all(preconditioner[i][i] > 0 for i in range(n))
        pre = fmpz_mat(preconditioner)
        intermediate = fmpz_mat(gram) * pre
        dominant = pre.transpose() * intermediate
        margin = min(int(dominant[i, i]) - sum(abs(int(dominant[i, j])) for j in range(n) if i != j)
                     for i in range(n))
        assert margin > 0
        positivity.append({"preconditioner": preconditioner,
                           "intermediate": [[int(x) for x in r] for r in intermediate.tolist()],
                           "dominant": [[int(x) for x in r] for r in dominant.tolist()],
                           "margin": margin})
        print("exact PSD", block, "relative DD margin", float(Fraction(margin, denominator * 10**12)),
              "seconds", round(time.monotonic()-started, 2), flush=True)

    payload = {
        "source": str(source), "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "atlas": certificate["atlas"], "interval": certificate["interval"],
        "basis_indices": certificate["basis_indices"], "young_bases": certificate["young_bases"],
        "face_bases": bases, "gram_denominator": denominator, "gram_scaled": grams,
        "positivity": positivity, "phi": str(phi), "equation_count": len(equations),
        "formal_status": "untrusted candidate; not Lean verified",
    }
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(payload, separators=(",", ":")) + "\n", encoding="utf-8")
    print("wrote", output, "bytes", output.stat().st_size,
          "seconds", round(time.monotonic()-started, 2), flush=True)


if __name__ == "__main__":
    main()
