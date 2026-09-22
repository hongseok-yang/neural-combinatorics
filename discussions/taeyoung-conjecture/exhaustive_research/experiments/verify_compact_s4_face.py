"""Exact audit of a compact S4 candidate, independent of its rationalizer.

This finite-arithmetic audit is not a replacement for Lean verification of
the coefficient map or its graphon interpretation.
"""

import argparse
import json
import os
import sys
from pathlib import Path

os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["OMP_NUM_THREADS"] = "1"
import numpy as np
import sympy as sp
from flint import fmpz_mat

from s4_interval_rationalize import NAMES, exact_equations

sys.set_int_max_str_digits(0)


def square_matrix(rows, order):
    assert len(rows) == order and all(len(row) == order for row in rows)
    return fmpz_mat(rows)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate")
    args = parser.parse_args()
    c = json.loads(Path(args.certificate).read_text(encoding="utf-8"))
    assert len(c["face_bases"]) == len(c["gram_scaled"]) == len(c["positivity"]) == 10
    denominator = int(c["gram_denominator"])
    assert denominator > 0
    transforms = [np.asarray(c["young_bases"][name], dtype=np.int64) for name in NAMES]
    equations, _, basis_indices, target = exact_equations(
        int(c["atlas"]), *map(sp.Rational, c["interval"]), 2,
        young_transforms=transforms,
    )
    assert c["basis_indices"] == basis_indices
    assert sp.expand(sp.sympify(c["phi"]) - target) == 0
    grams = []
    for block, (face, entries, witness) in enumerate(zip(c["face_bases"], c["gram_scaled"], c["positivity"])):
        n = len(entries)
        expected_rows = transforms[block % 5].shape[1] * (2 if block < 5 else 1)
        assert len(face) == expected_rows and all(len(row) == n for row in face)
        gram = square_matrix(entries, n)
        assert gram == gram.transpose()
        pre = square_matrix(witness["preconditioner"], n)
        middle = square_matrix(witness["intermediate"], n)
        dominant = square_matrix(witness["dominant"], n)
        assert all(pre[i, i] != 0 for i in range(n))
        assert all(pre[i, j] == 0 for i in range(n) for j in range(i))
        assert gram * pre == middle
        assert pre.transpose() * middle == dominant
        assert dominant == dominant.transpose()
        margin = min(dominant[i, i] - sum(abs(dominant[i, j]) for j in range(n) if j != i)
                     for i in range(n))
        assert margin > 0 and margin == int(witness["margin"])
        basis = fmpz_mat(face)
        grams.append(basis * gram * basis.transpose())
    for matrices, rhs, core, power, _ in equations:
        actual = 0
        for matrix, gram in zip(matrices, grams):
            assert matrix.shape == (gram.nrows(), gram.ncols())
            actual += sum(int(matrix[i, j]) * gram[i, j]
                          for i in range(gram.nrows()) for j in range(gram.ncols()))
        assert actual == rhs * denominator, (core, power)
    print(f"Exact audit passed: Atlas {c['atlas']}, {len(equations)} coefficient equations, "
          f"10 positive matrices, common denominator {denominator}. This is not yet a Lean row proof.")


if __name__ == "__main__":
    main()
