"""Interval SOS search in the S4-reduced four-label rooted cone.

For t in [0,1] and p=a+(b-a)t, every irrep block is represented as

    Q(t) = [I,tI]^T G0 [I,tI] + t(1-t) G1,

with G0,G1 positive semidefinite.  Coefficients are matched exactly at the
symbolic level, then passed to a numerical SDP.  This is a discovery tool;
successful solutions still require facial reduction and rational auditing.
"""

from __future__ import annotations

import argparse
from collections import defaultdict

import cvxpy as cp
import networkx as nx
import numpy as np
import sympy as sp
from networkx.algorithms.polynomials import chromatic_polynomial
from scipy import sparse
from scipy.linalg import qr

from full_s4_rooted_sos import (
    graph_key,
    irrep_transforms,
    rooted_basis_indices,
    restrict_transforms,
    young_integer_transforms,
)
from rooted_sos_search import fixed_density_key


def polynomial_coefficients(expression, variable, degree=5):
    polynomial = sp.Poly(sp.expand(expression), variable, domain=sp.QQ)
    return [sp.Rational(polynomial.nth(power)) for power in range(degree + 1)]


def raw_by_isolated(basis_indices: list[int]):
    entries = defaultdict(lambda: ([], [], []))
    cache = {}
    for local_i, i in enumerate(basis_indices):
        left_label, left_branch = divmod(i, 16)
        for local_j in range(local_i, len(basis_indices)):
            j = basis_indices[local_j]
            right_label, right_branch = divmod(j, 16)
            lookup = (left_label | right_label, left_branch, right_branch)
            if lookup not in cache:
                cache[lookup] = graph_key(*lookup)
            key = cache[lookup]
            rows, columns, values = entries[key]
            rows.append(local_i)
            columns.append(local_j)
            values.append(1.0)
            if local_i != local_j:
                rows.append(local_j)
                columns.append(local_i)
                values.append(1.0)
    size = len(basis_indices)
    return {
        key: sparse.coo_matrix((values, (rows, columns)), shape=(size, size)).tocsr()
        for key, (rows, columns, values) in entries.items()
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--atlas", type=int, required=True)
    parser.add_argument("--left", required=True)
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
    parser.add_argument(
        "--rational-slices", action="store_true",
        help="Use integer Young-symmetrizer slice bases (normalized only for the SDP).",
    )
    parser.add_argument(
        "--turan-faces",
        help="NPZ of exact allowed-face bases from s4_turan_faces.py.",
    )
    parser.add_argument("--solver", choices=("CLARABEL", "SCS", "CVXOPT"), default="CLARABEL")
    parser.add_argument("--objective", choices=("zero", "trace", "margin"), default="zero")
    parser.add_argument(
        "--fixed-margin", type=float,
        help="Require every reduced Gram block to dominate this scalar identity.",
    )
    parser.add_argument("--find-exposer", action="store_true")
    parser.add_argument("--save")
    parser.add_argument("--initial", help="NPZ whose Gram values initialize the solver.")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--scs-eps", type=float, default=2e-6)
    parser.add_argument("--scs-max-iters", type=int, default=100_000)
    args = parser.parse_args()

    left, right = sp.Rational(args.left), sp.Rational(args.right)
    t = sp.symbols("t")
    p = left + (right - left) * t
    order0 = args.polynomial_degree // 2 + 1
    order1 = args.polynomial_degree // 2
    integer_transforms = None
    if args.rational_slices:
        integer_transforms, factors, names, basis_indices = young_integer_transforms(
            args.label_degree, args.degree_three_kind
        )
        norms = [np.linalg.norm(transform.astype(float), axis=0) for transform in integer_transforms]
        transforms = [
            transform.astype(float) / norm[None, :]
            for transform, norm in zip(integer_transforms, norms)
        ]
    else:
        transforms, factors, names = irrep_transforms()
        basis_indices = rooted_basis_indices(args.label_degree, args.degree_three_kind)
        transforms = restrict_transforms(transforms, basis_indices)
        norms = [np.ones(transform.shape[1]) for transform in transforms]
    raw = raw_by_isolated(basis_indices)
    matrices = {
        key: [transform.T @ matrix @ transform for transform in transforms]
        for key, matrix in raw.items()
    }
    original_sizes = [transform.shape[1] for transform in transforms]
    max_isolated = max(isolated for _, isolated in matrices)
    max_power = max(5, max_isolated + args.polynomial_degree)
    density_coefficients = {
        isolated: polynomial_coefficients(p**isolated, t, max_power)
        for isolated in range(max_isolated + 1)
    }

    graph = nx.graph_atlas(args.atlas)
    target_core, target_isolated = fixed_density_key(graph)
    if target_isolated:
        raise AssertionError("the requested graph should be connected")
    x = next(iter(chromatic_polynomial(graph).free_symbols))
    phi = sp.factor((1 - p) ** graph.number_of_nodes() *
                    chromatic_polynomial(graph).subs(x, 1 / (1 - p)))
    target = {
        target_core: polynomial_coefficients(sp.Integer(1), t, max_power),
        0: polynomial_coefficients(-phi, t, max_power),
    }

    cores = sorted(set(core for core, _ in matrices) | set(target))
    zero_blocks = [np.zeros((size, size)) for size in original_sizes]
    equation_specs = []
    for core in cores:
        for total_power in range(max_power + 1):
            blocks0 = []
            blocks1 = []
            used = False
            for block, size in enumerate(original_sizes):
                matrix0 = np.zeros((order0 * size, order0 * size))
                matrix1 = np.zeros((order1 * size, order1 * size))
                for isolated in range(max_isolated + 1):
                    source = matrices.get((core, isolated), zero_blocks)[block]
                    if not np.any(source):
                        continue
                    coefficients = density_coefficients[isolated]
                    for u in range(order0):
                        for v in range(order0):
                            index = total_power - u - v
                            if 0 <= index < len(coefficients):
                                matrix0[u*size:(u+1)*size, v*size:(v+1)*size] += (
                                    float(coefficients[index]) * source
                                )
                    for u in range(order1):
                        for v in range(order1):
                            index = total_power - 1 - u - v
                            if 0 <= index < len(coefficients):
                                matrix1[u*size:(u+1)*size, v*size:(v+1)*size] += (
                                    float(coefficients[index]) * source
                                )
                            index = total_power - 2 - u - v
                            if 0 <= index < len(coefficients):
                                matrix1[u*size:(u+1)*size, v*size:(v+1)*size] -= (
                                    float(coefficients[index]) * source
                                )
                blocks0.append(matrix0)
                blocks1.append(matrix1)
                used = used or np.any(matrix0) or np.any(matrix1)
            target_value = float(target.get(core, [0] * (max_power + 1))[total_power])
            if used or target_value:
                equation_specs.append((blocks0 + blocks1, target_value, core, total_power))

    face_complements0 = face_complements1 = None
    reduction_norms0 = reduction_norms1 = None
    if args.turan_faces:
        if not args.rational_slices:
            raise ValueError("--turan-faces requires --rational-slices")
        face_data = np.load(args.turan_faces)
        face_complements0 = [np.asarray(face_data[f"C0_{name}"], dtype=float) for name in names]
        face_complements1 = [np.asarray(face_data[f"C1_{name}"], dtype=float) for name in names]
        reductions0 = []
        reductions1 = []
        reduction_norms0 = []
        reduction_norms1 = []
        for norm, complement0, complement1 in zip(norms, face_complements0, face_complements1):
            raw0 = np.diag(np.tile(norm, order0)) @ complement0
            raw1 = np.diag(np.tile(norm, order1)) @ complement1
            column_norm0 = np.linalg.norm(raw0, axis=0)
            column_norm1 = np.linalg.norm(raw1, axis=0)
            reductions0.append(raw0 / column_norm0[None, :])
            reductions1.append(raw1 / column_norm1[None, :])
            reduction_norms0.append(column_norm0)
            reduction_norms1.append(column_norm1)
        reduced_specs = []
        reductions = reductions0 + reductions1
        for blocks, target_value, core, power in equation_specs:
            reduced_specs.append(([
                reduction.T @ matrix @ reduction
                for reduction, matrix in zip(reductions, blocks)
            ], target_value, core, power))
        equation_specs = reduced_specs
        sizes = [item.shape[1] for item in reductions0]
        sizes1 = [item.shape[1] for item in reductions1]
    else:
        sizes = original_sizes
        sizes1 = original_sizes

    g0 = [cp.Variable((size, size), symmetric=True) for size in (
        [order0 * value for value in original_sizes] if not args.turan_faces else sizes
    )]
    # In the unreduced case ``sizes`` stores the rooted block orders, whereas
    # after facial reduction it already stores the G0 orders.
    if not args.turan_faces:
        g0 = [cp.Variable((order0 * size, order0 * size), symmetric=True) for size in original_sizes]
        sizes1 = [order1 * size for size in original_sizes]
    g1 = [cp.Variable((size, size), symmetric=True) for size in sizes1]
    grams = g0 + g1
    constraints = [gram >> 0 for gram in grams]
    if args.fixed_margin is not None:
        constraints.extend(
            gram - args.fixed_margin * np.eye(gram.shape[0]) >> 0
            for gram in grams
        )
    labels = [f"G0_{name}" for name in names] + [f"G1_{name}" for name in names]
    if args.initial:
        initial = np.load(args.initial)
        for label, gram in zip(labels, grams):
            gram.value = np.asarray(initial[label])

    def symmetric_vector(matrix):
        indices = np.triu_indices(matrix.shape[0])
        values = matrix[indices].copy()
        values[indices[0] != indices[1]] *= 2
        return values

    block_factors = factors + factors
    rows = np.vstack([
        np.concatenate([
            factor * symmetric_vector(matrix)
            for factor, matrix in zip(block_factors, blocks)
        ])
        for blocks, *_ in equation_specs
    ])
    rhs = np.asarray([value for _, value, *_ in equation_specs])
    _, triangular, pivots = qr(rows.T, mode="economic", pivoting=True)
    tolerance = max(rows.shape) * np.finfo(float).eps * abs(triangular[0, 0])
    rank = int(np.count_nonzero(np.abs(np.diag(triangular)) > tolerance))
    augmented_rank = np.linalg.matrix_rank(np.c_[rows, rhs])
    print(
        f"atlas={args.atlas} interval=[{left},{right}] basis={len(basis_indices)} "
        f"blocks0={dict(zip(names, [gram.shape[0] for gram in g0]))} "
        f"blocks1={dict(zip(names, [gram.shape[0] for gram in g1]))} "
        f"equations={len(equation_specs)} "
        f"rank={rank} augmented={augmented_rank}", flush=True,
    )
    if augmented_rank != rank:
        raise AssertionError((rank, augmented_rank))
    selected = sorted(int(index) for index in pivots[:rank])
    selected_specs = []
    for index in selected:
        blocks, target_value, *_ = equation_specs[index]
        scale = np.linalg.norm(rows[index])
        selected_specs.append((blocks, target_value, scale))
        constraints.append(sum(
            factor * cp.sum(cp.multiply(matrix / scale, gram))
            for factor, matrix, gram in zip(block_factors, blocks, grams)
        ) == target_value / scale)

    if args.find_exposer:
        dual = cp.Variable(rank)
        exposers = []
        for block_index in range(len(grams)):
            exposers.append(sum(
                dual[equation_index] * blocks[block_index] / scale
                for equation_index, (blocks, _, scale) in enumerate(selected_specs)
            ))
        dual_constraints = [exposer >> 0 for exposer in exposers]
        dual_constraints.append(sum(
            dual[index] * target_value / scale
            for index, (_, target_value, scale) in enumerate(selected_specs)
        ) == 0)
        dual_constraints.append(sum(cp.trace(exposer) for exposer in exposers) == 1)
        dual_problem = cp.Problem(cp.Minimize(cp.sum_squares(dual)), dual_constraints)
        if args.solver == "CLARABEL":
            dual_problem.solve(
                solver="CLARABEL", tol_gap_abs=1e-9, tol_feas=1e-9,
                max_iter=500, verbose=args.verbose,
            )
        elif args.solver == "SCS":
            dual_problem.solve(
                solver="SCS", eps=args.scs_eps, max_iters=args.scs_max_iters,
                verbose=args.verbose,
            )
        else:
            dual_problem.solve(
                solver="CVXOPT", feastol=1e-9, abstol=1e-9, reltol=1e-9,
                max_iters=300, verbose=args.verbose,
            )
        print(f"exposer_status={dual_problem.status} objective={dual_problem.value}")
        if dual.value is None:
            return
        values = []
        for label, exposer in zip(labels, exposers):
            value = np.asarray(exposer.value)
            values.append(value)
            eigenvalues = np.linalg.eigvalsh((value + value.T) / 2)
            print(
                f"Z_{label}: min={eigenvalues[0]:.5e} max={eigenvalues[-1]:.5e} "
                f"rank1e-7={np.count_nonzero(eigenvalues > 1e-7)}"
            )
        if args.save:
            payload = {f"Z_{label}": value for label, value in zip(labels, values)}
            payload["dual"] = dual.value
            payload["selected"] = np.asarray(selected)
            for name, norm in zip(names, norms):
                payload[f"norm_{name}"] = norm
            if face_complements0 is not None:
                for name, complement0, complement1, norm0, norm1 in zip(
                    names, face_complements0, face_complements1,
                    reduction_norms0, reduction_norms1,
                ):
                    payload[f"C0_{name}"] = complement0.astype(np.int64)
                    payload[f"C1_{name}"] = complement1.astype(np.int64)
                    payload[f"reduction_norm0_{name}"] = norm0
                    payload[f"reduction_norm1_{name}"] = norm1
            np.savez(args.save, **payload)
        return

    if args.objective == "zero":
        objective = cp.Minimize(0)
    elif args.objective == "trace":
        objective = cp.Minimize(sum(
            factor * cp.trace(gram) for factor, gram in zip(block_factors, grams)
        ))
    else:
        margin = cp.Variable()
        constraints.extend(gram - margin * np.eye(gram.shape[0]) >> 0 for gram in grams)
        objective = cp.Maximize(margin)
    problem = cp.Problem(objective, constraints)
    if args.solver == "CLARABEL":
        problem.solve(solver="CLARABEL", tol_gap_abs=1e-8, tol_feas=1e-8,
                      max_iter=500, verbose=args.verbose, warm_start=bool(args.initial))
    elif args.solver == "SCS":
        problem.solve(
            solver="SCS", eps=args.scs_eps, max_iters=args.scs_max_iters,
            verbose=args.verbose, warm_start=bool(args.initial),
        )
    else:
        problem.solve(
            solver="CVXOPT", feastol=1e-9, abstol=1e-9, reltol=1e-9,
            max_iters=300, verbose=args.verbose,
        )
    print(f"status={problem.status} objective={problem.value}")
    if any(gram.value is None for gram in grams):
        return
    residuals = [
        abs(sum(factor * np.sum(matrix * gram.value)
                for factor, matrix, gram in zip(block_factors, blocks, grams)) - target_value)
        for blocks, target_value, *_ in equation_specs
    ]
    for label, gram in zip(labels, grams):
        eigenvalues = np.linalg.eigvalsh((gram.value + gram.value.T) / 2)
        print(f"{label}: min={eigenvalues[0]:.5e} rank1e-7={np.count_nonzero(eigenvalues > 1e-7)}")
    print(f"max_residual={max(residuals):.6e}")
    if args.save:
        payload = {
            **{label: gram.value for label, gram in zip(labels, grams)},
            "selected": np.asarray(selected),
            "basis_indices": np.asarray(basis_indices),
            "left": str(left), "right": str(right),
            "polynomial_degree": args.polynomial_degree,
        }
        for name, norm in zip(names, norms):
            payload[f"norm_{name}"] = norm
        if integer_transforms is not None:
            for name, transform in zip(names, integer_transforms):
                payload[f"B_{name}"] = transform
        if face_complements0 is not None:
            for name, complement0, complement1, norm0, norm1 in zip(
                names, face_complements0, face_complements1,
                reduction_norms0, reduction_norms1,
            ):
                payload[f"C0_{name}"] = complement0.astype(np.int64)
                payload[f"C1_{name}"] = complement1.astype(np.int64)
                payload[f"reduction_norm0_{name}"] = norm0
                payload[f"reduction_norm1_{name}"] = norm1
        np.savez(args.save, **payload)


if __name__ == "__main__":
    main()
