"""Compute the exact Gram face forced by balanced Turan equality graphons.

For Atlas 43 the interval SOS is exact at every balanced complete k-partite
graphon.  The rooted basis evaluation vectors at those equality cases must
therefore lie in the kernels of the positive semidefinite Gram matrices.
This script constructs their rational span and compares it with a floating
certificate.
"""

from __future__ import annotations

import argparse
import itertools

import numpy as np
import sympy as sp

from house_certificate_faces import permutation_matrices, reconstruct
from rooted_sos_search import label_s3_irrep_transforms, rooted_basis


def rooted_turan_vector(basis, k: int, colors: tuple[int, int, int]) -> sp.Matrix:
    result = []
    for graph in basis:
        label_edges_ok = all(
            colors[u] != colors[v]
            for u, v in graph.edges()
            if u < 3 and v < 3
        )
        if not label_edges_ok:
            result.append(sp.Rational(0))
            continue
        neighbor_colors = {
            colors[u if v == 3 else v]
            for u, v in graph.edges()
            if u == 3 or v == 3
        }
        result.append(sp.Rational(k - len(neighbor_colors), k))
    return sp.Matrix(result)


def exact_face_bases(max_k: int = 12):
    basis = rooted_basis(3, 1)
    g1_columns = []
    g0_columns = []
    for k in range(2, max_k + 1):
        t = sp.Rational(k - 2, k)
        for colors in itertools.product(range(k), repeat=3):
            vector = rooted_turan_vector(basis, k, colors)
            g0_columns.append(vector.col_join(t * vector))
            if k >= 3:
                g1_columns.append(vector)
    g0 = sp.Matrix.hstack(*g0_columns).columnspace()
    g1 = sp.Matrix.hstack(*g1_columns).columnspace()
    return sp.Matrix.hstack(*g0), sp.Matrix.hstack(*g1)


def exact_face_complements(max_k: int = 5):
    """Integer bases for the orthogonal complements of the forced kernels."""
    complements = []
    for face in exact_face_bases(max_k):
        columns = []
        for vector in face.T.nullspace():
            common = sp.ilcm(*(entry.q for entry in vector))
            integers = [int(entry * common) for entry in vector]
            divisor = sp.igcd(*integers)
            columns.append(sp.Matrix([entry // divisor for entry in integers]))
        complements.append(sp.Matrix.hstack(*columns))
    return tuple(complements)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate")
    parser.add_argument("--max-k", type=int, default=8)
    args = parser.parse_args()
    faces = exact_face_bases(args.max_k)
    print(f"exact Turan face ranks: G0={faces[0].shape[1]} G1={faces[1].shape[1]}")
    if args.max_k >= 5:
        complements = exact_face_complements(5)
        print(
            "complements: "
            + " ".join(
                f"{matrix.shape} maxabs={max(abs(int(x)) for x in matrix)}"
                for matrix in complements
            )
        )
    if not args.certificate:
        return
    data = np.load(args.certificate)
    if "G0_1" in data.files:
        basis = rooted_basis(3, 1)
        transforms, _ = label_s3_irrep_transforms(basis)
        permutations = permutation_matrices(basis)
        matrices = [
            reconstruct([data[f"G0_{i}"] for i in range(3)], transforms, permutations, 2),
            reconstruct([data[f"G1_{i}"] for i in range(3)], transforms, permutations, 1),
        ]
    else:
        matrices = [data["G0_0"], data["G1_0"]]
    for name, matrix, face in zip(("G0", "G1"), matrices, faces):
        face_float = np.asarray(face, dtype=float)
        print(
            f"{name}: ||Q K||_2={np.linalg.norm(matrix @ face_float, ord=2):.6e} "
            f"max_entry={np.max(np.abs(matrix @ face_float)):.6e}"
        )


if __name__ == "__main__":
    main()
