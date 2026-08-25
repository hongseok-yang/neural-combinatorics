"""Interval matrix-SOS search for the Atlas 43 graphon inequality.

On p in [a,b], put t=(p-a)/(b-a).  In each S3 representation block use

  Q(t) = [I,tI]^T G0 [I,tI] + t(1-t) G1,

with G0,G1 PSD.  Exact polynomial coefficient matching modulo the fixed edge
density identity then yields a certificate valid on the whole interval.
"""

from __future__ import annotations

from collections import defaultdict
import argparse
import cvxpy as cp
import numpy as np
import sympy as sp
from scipy.linalg import qr

from rooted_sos_search import (
    fixed_density_key,
    label_s3_irrep_transforms,
    rooted_basis,
    rooted_product,
)


def coefficients_in_t(
    expression: sp.Expr, p: sp.Symbol, t: sp.Symbol, a: sp.Rational, b: sp.Rational
) -> list[sp.Rational]:
    polynomial = sp.Poly(sp.expand(expression.subs(p, a + (b - a) * t)), t, domain=sp.QQ)
    return [sp.Rational(polynomial.nth(power)) for power in range(polynomial.degree() + 1)]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--left", default="1/2")
    parser.add_argument("--right", default="71/100")
    parser.add_argument("--solver", choices=("CLARABEL", "SCS", "CVXOPT"), default="CLARABEL")
    parser.add_argument("--objective", choices=("trace", "zero", "margin"), default="trace")
    parser.add_argument(
        "--full-basis", action="store_true",
        help="Use the rational 64-element basis directly instead of floating S3 blocks.",
    )
    parser.add_argument(
        "--find-exposer", action="store_true",
        help="Solve for a normalized dual facial exposer instead of a primal certificate.",
    )
    parser.add_argument("--save")
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()

    a = sp.Rational(args.left)
    b = sp.Rational(args.right)
    p, t = sp.symbols("p t")

    labels, branches = 3, 1
    basis = rooted_basis(labels, branches)
    if args.full_basis:
        transforms, factors = [np.eye(len(basis))], [1]
    else:
        transforms, factors = label_s3_irrep_transforms(basis)
    block_sizes = [transform.shape[1] for transform in transforms]

    raw: dict[tuple[int, int], np.ndarray] = defaultdict(
        lambda: np.zeros((len(basis), len(basis)), dtype=float)
    )
    for i, left in enumerate(basis):
        for j in range(i, len(basis)):
            product = rooted_product(left, basis[j], labels, branches)
            core, isolated = fixed_density_key(product)
            raw[(core, isolated)][i, j] += 1
            if i != j:
                raw[(core, isolated)][j, i] += 1
    matrices = {
        key: [transform.T @ matrix @ transform for transform in transforms]
        for key, matrix in raw.items()
    }
    for items in matrices.values():
        for matrix in items:
            matrix[np.abs(matrix) < 1e-10] = 0

    max_isolated = max(isolated for _, isolated in matrices)
    density_coefficients = {
        isolated: coefficients_in_t(p**isolated, p, t, a, b)
        for isolated in range(max_isolated + 1)
    }
    phi = 6 * p**4 - 9 * p**3 + 5 * p**2 - p
    target = {
        0: coefficients_in_t(-phi, p, t, a, b),
        43: coefficients_in_t(sp.Integer(1), p, t, a, b),
    }
    for values in target.values():
        values.extend([sp.Rational(0)] * (5 - len(values)))

    g0 = [cp.Variable((2 * size, 2 * size), symmetric=True) for size in block_sizes]
    g1 = [cp.Variable((size, size), symmetric=True) for size in block_sizes]
    constraints = [item >> 0 for item in g0 + g1]
    cores = sorted(set(core for core, _ in matrices) | {0, 43})
    zero_blocks = [np.zeros((size, size)) for size in block_sizes]

    equation_specs: list[tuple[list[np.ndarray], float]] = []
    for core in cores:
        for total_power in range(5):
            used = False
            spec0: list[np.ndarray] = []
            spec1: list[np.ndarray] = []
            for block, size in enumerate(block_sizes):
                matrix0 = np.zeros((2 * size, 2 * size))
                matrix1 = np.zeros((size, size))
                for isolated in range(max_isolated + 1):
                    source = matrices.get((core, isolated), zero_blocks)[block]
                    if not np.any(source):
                        continue
                    coefficients = density_coefficients[isolated]
                    for u in range(2):
                        for v in range(2):
                            index = total_power - u - v
                            if 0 <= index < len(coefficients):
                                matrix0[u * size : (u + 1) * size, v * size : (v + 1) * size] += (
                                    float(coefficients[index]) * source
                                )
                    index1 = total_power - 1
                    index2 = total_power - 2
                    if 0 <= index1 < len(coefficients):
                        matrix1 += float(coefficients[index1]) * source
                    if 0 <= index2 < len(coefficients):
                        matrix1 -= float(coefficients[index2]) * source
                matrix0 *= factors[block]
                matrix1 *= factors[block]
                spec0.append(matrix0)
                spec1.append(matrix1)
                used = used or np.any(matrix0) or np.any(matrix1)
            target_value = float(target.get(core, [0] * 5)[total_power])
            if used or target_value:
                equation_specs.append((spec0 + spec1, target_value))

    def symmetric_vector(matrix: np.ndarray) -> np.ndarray:
        indices = np.triu_indices(matrix.shape[0])
        values = matrix[indices].copy()
        values[indices[0] != indices[1]] *= 2
        return values

    rows = np.vstack(
        [np.concatenate([symmetric_vector(matrix) for matrix in matrices_for_equation]) for matrices_for_equation, _ in equation_specs]
    )
    rhs_vector = np.array([value for _, value in equation_specs])
    _, diagonal, pivots = qr(rows.T, mode="economic", pivoting=True)
    tolerance = max(rows.shape) * np.finfo(float).eps * abs(diagonal[0, 0])
    rank = int(np.count_nonzero(np.abs(np.diag(diagonal)) > tolerance))
    selected = sorted(int(index) for index in pivots[:rank])
    augmented_rank = np.linalg.matrix_rank(np.c_[rows, rhs_vector])
    if augmented_rank != rank:
        raise AssertionError((rank, augmented_rank))
    selected_specs = [equation_specs[index] for index in selected]
    for matrices_for_equation, target_value in selected_specs:
        expression = sum(
            cp.sum(cp.multiply(matrix, variable))
            for matrix, variable in zip(matrices_for_equation, g0 + g1)
            if np.any(matrix)
        )
        constraints.append(expression == target_value)

    if args.find_exposer:
        dual = cp.Variable(len(selected_specs))
        exposers = []
        for variable_index, variable in enumerate(g0 + g1):
            exposer = sum(
                dual[equation_index] * matrices_for_equation[variable_index]
                for equation_index, (matrices_for_equation, _) in enumerate(selected_specs)
            )
            exposers.append(exposer)
        dual_constraints = [item >> 0 for item in exposers]
        dual_constraints.append(
            sum(
                dual[index] * target_value
                for index, (_, target_value) in enumerate(selected_specs)
            )
            == 0
        )
        dual_constraints.append(sum(cp.trace(item) for item in exposers) == 1)
        dual_problem = cp.Problem(cp.Minimize(cp.sum_squares(dual)), dual_constraints)
        solver_options = (
            {"tol_gap_abs": 1e-9, "tol_feas": 1e-9}
            if args.solver == "CLARABEL"
            else ({"eps": 1e-7, "max_iters": 500_000} if args.solver == "SCS"
                  else {"abstol": 1e-10, "reltol": 1e-10, "feastol": 1e-10,
                        "max_iters": 500})
        )
        dual_problem.solve(solver=args.solver, verbose=args.verbose, **solver_options)
        print(
            f"exposer_status={dual_problem.status} objective={dual_problem.value} "
            f"interval=[{a},{b}] blocks={block_sizes} rank={rank}"
        )
        if dual.value is None:
            return
        values = []
        for index, item in enumerate(exposers):
            value = np.asarray(item.value)
            values.append(value)
            eigenvalues = np.linalg.eigvalsh((value + value.T) / 2)
            print(
                f"Z_{index}: size={value.shape[0]} min={eigenvalues[0]:.9g} "
                f"max={eigenvalues[-1]:.9g} rank1e-7={np.count_nonzero(eigenvalues > 1e-7)}"
            )
        if args.save:
            np.savez(
                args.save, dual=dual.value,
                **{f"Z_{index}": value for index, value in enumerate(values)},
                left=str(a), right=str(b), selected=np.asarray(selected),
            )
        return

    trace_objective = sum(
        factors[block] * (cp.trace(g0[block]) + cp.trace(g1[block]))
        for block in range(len(block_sizes))
    )
    if args.objective == "trace":
        objective = cp.Minimize(trace_objective)
    elif args.objective == "zero":
        objective = cp.Minimize(0)
    else:
        margin = cp.Variable()
        for item in g0 + g1:
            constraints.append(item - margin * np.eye(item.shape[0]) >> 0)
        objective = cp.Maximize(margin)
    problem = cp.Problem(objective, constraints)
    print(
        f"interval=[{a},{b}] blocks={block_sizes} equations={len(equation_specs)} "
        f"rank={rank} constraints={len(constraints)} rows_shape={rows.shape}",
        flush=True,
    )
    if args.solver == "CLARABEL":
        problem.solve(
            solver="CLARABEL", tol_gap_abs=1e-9, tol_feas=1e-9,
            verbose=args.verbose,
        )
    elif args.solver == "SCS":
        problem.solve(
            solver="SCS", eps=1e-7, max_iters=500_000,
            verbose=args.verbose,
        )
    else:
        problem.solve(
            solver="CVXOPT", abstol=1e-10, reltol=1e-10, feastol=1e-10,
            max_iters=500, verbose=args.verbose,
        )
    print(
        f"status={problem.status} objective={problem.value} interval=[{a},{b}] "
        f"blocks={block_sizes} equations={len(equation_specs)} rank={rank} constraints={len(constraints)}"
    )
    variables = g0 + g1
    if any(item.value is None for item in variables):
        return
    for name, item in zip(
            [f"G0_{index}" for index in range(len(block_sizes))]
            + [f"G1_{index}" for index in range(len(block_sizes))],
        variables,
    ):
        eigenvalues = np.linalg.eigvalsh(item.value)
        print(
            f"{name}: size={item.shape[0]} min={eigenvalues[0]:.9g} "
            f"max={eigenvalues[-1]:.9g} rank1e-7={np.count_nonzero(eigenvalues > 1e-7)}"
        )
    if args.save:
        np.savez(
            args.save,
            **{name: item.value for name, item in zip(
                [f"G0_{index}" for index in range(len(block_sizes))]
                + [f"G1_{index}" for index in range(len(block_sizes))],
                variables,
            )},
            left=str(a),
            right=str(b),
        )


if __name__ == "__main__":
    main()
