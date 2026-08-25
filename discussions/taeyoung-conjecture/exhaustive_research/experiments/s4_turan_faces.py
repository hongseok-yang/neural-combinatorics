"""Exact Turan-equality faces for the degree-cutoff S4 rooted cone."""

from __future__ import annotations

import argparse
import itertools

import numpy as np
import sympy as sp

from full_s4_rooted_sos import LABEL_EDGES, young_integer_transforms


def equality_patterns(length: int = 4):
    """Restricted-growth strings, one representative of each set partition."""
    result = []

    def extend(prefix):
        if len(prefix) == length:
            result.append(tuple(prefix))
            return
        largest = max(prefix, default=-1)
        for value in range(largest + 2):
            extend(prefix + [value])

    extend([])
    return result


def rooted_turan_vector(basis_indices: list[int], k: int, colors: tuple[int, ...]):
    values = []
    for index in basis_indices:
        label_mask, branch_mask = divmod(index, 16)
        if any(
            label_mask & (1 << bit) and colors[u] == colors[v]
            for bit, (u, v) in enumerate(LABEL_EDGES)
        ):
            values.append(sp.Rational(0))
            continue
        forbidden = {colors[root] for root in range(4) if branch_mask & (1 << root)}
        values.append(sp.Rational(k - len(forbidden), k))
    return sp.Matrix(values)


def integer_complement(columns: list[sp.Matrix], order: int) -> sp.Matrix:
    if columns:
        face = sp.Matrix.hstack(*columns).columnspace()
        if face:
            face_matrix = sp.Matrix.hstack(*face)
            nullspace = face_matrix.T.nullspace()
        else:
            nullspace = [sp.eye(order).col(index) for index in range(order)]
    else:
        nullspace = [sp.eye(order).col(index) for index in range(order)]
    result = []
    for vector in nullspace:
        common = sp.ilcm(*(entry.q for entry in vector))
        integers = [int(entry * common) for entry in vector]
        divisor = sp.igcd(*integers)
        result.append(sp.Matrix([entry // divisor for entry in integers]))
    return sp.Matrix.hstack(*result)


def exact_turan_complements(
    label_degree: int, degree_three_kind: str,
    left: sp.Rational, right: sp.Rational, max_k: int,
    polynomial_degree: int = 2,
):
    if polynomial_degree not in (2, 4):
        raise ValueError(polynomial_degree)
    order0 = polynomial_degree // 2 + 1
    order1 = polynomial_degree // 2
    transforms, _, names, basis_indices = young_integer_transforms(
        label_degree, degree_three_kind
    )
    patterns = equality_patterns()
    complements0 = []
    complements1 = []
    for name, transform_numpy in zip(names, transforms):
        transform = sp.Matrix(transform_numpy.tolist())
        g0_columns = []
        g1_columns = []
        for k in range(2, max_k + 1):
            p = sp.Rational(k - 1, k)
            if p < left or p > right:
                continue
            interval_t = (p - left) / (right - left)
            for colors in patterns:
                if len(set(colors)) > k:
                    continue
                vector = transform.T * rooted_turan_vector(basis_indices, k, colors)
                g0_columns.append(sp.Matrix.vstack(*(
                    interval_t**power * vector for power in range(order0)
                )))
                if left < p < right:
                    g1_columns.append(sp.Matrix.vstack(*(
                        interval_t**power * vector for power in range(order1)
                    )))
        complement0 = integer_complement(g0_columns, order0 * transform.shape[1])
        complement1 = integer_complement(g1_columns, order1 * transform.shape[1])
        complements0.append(complement0)
        complements1.append(complement1)
        print(
            f"{name}: G0 forced={order0*transform.shape[1]-complement0.shape[1]} "
            f"allowed={complement0.shape[1]} maxabs={max(abs(int(x)) for x in complement0)}; "
            f"G1 forced={order1*transform.shape[1]-complement1.shape[1]} "
            f"allowed={complement1.shape[1]} maxabs={max(abs(int(x)) for x in complement1)}",
            flush=True,
        )
    return complements0, complements1, transforms, names, basis_indices


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--label-degree", type=int, default=2)
    parser.add_argument(
        "--degree-three-kind", choices=(
            "all", "triangle", "star", "path", "paw4", "cycle4",
            "triangle_paw4", "star_paw4", "path_paw4", "all3_paw4",
            "all4", "none"
        ),
        default="all",
    )
    parser.add_argument("--left", default="2/3")
    parser.add_argument("--right", default="1")
    parser.add_argument("--max-k", type=int, default=8)
    parser.add_argument("--polynomial-degree", type=int, choices=(2, 4), default=2)
    parser.add_argument("--save")
    args = parser.parse_args()
    left, right = sp.Rational(args.left), sp.Rational(args.right)
    c0, c1, transforms, names, basis_indices = exact_turan_complements(
        args.label_degree, args.degree_three_kind, left, right, args.max_k,
        args.polynomial_degree,
    )
    if args.save:
        payload = {
            "basis_indices": np.asarray(basis_indices),
            "left": str(left), "right": str(right),
            "degree_three_kind": args.degree_three_kind,
            "polynomial_degree": args.polynomial_degree,
        }
        for name, transform, item0, item1 in zip(names, transforms, c0, c1):
            payload[f"B_{name}"] = transform
            payload[f"C0_{name}"] = np.asarray(item0, dtype=np.int64)
            payload[f"C1_{name}"] = np.asarray(item1, dtype=np.int64)
        np.savez(args.save, **payload)


if __name__ == "__main__":
    main()
