"""Solve the Atlas-43 interval SOS after exact Turan facial reduction."""

from __future__ import annotations

import argparse
from pathlib import Path

import cvxpy as cp
import numpy as np
import sympy as sp
from scipy.linalg import qr

from house_rationalize_full import scaled_equations
from house_turan_face import exact_face_complements


def integer_orthogonal_complement(kernel: np.ndarray) -> np.ndarray:
    columns = []
    for vector in sp.Matrix(kernel.tolist()).T.nullspace():
        common = sp.ilcm(*(entry.q for entry in vector))
        integers = [int(entry * common) for entry in vector]
        divisor = sp.igcd(*integers)
        columns.append(sp.Matrix([entry // divisor for entry in integers]))
    return np.asarray(sp.Matrix.hstack(*columns), dtype=np.int64)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", choices=("CLARABEL", "CVXOPT", "SCS"), default="CLARABEL")
    parser.add_argument("--save")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--find-exposer", action="store_true")
    parser.add_argument(
        "--second-face", default="experiments/house_face_second_exposer.npz",
        help="Use the rational half-integral second-face ansatz recovered from this exposer; pass '' to disable.",
    )
    parser.add_argument(
        "--third-face", default="experiments/house_face_third_exposer.npz",
        help="Use the rational half-integral face for the G1 block; pass '' to disable.",
    )
    args = parser.parse_args()

    equations = scaled_equations(sp.Rational(1, 2), sp.Rational(1))
    exact_bases = exact_face_complements(5)
    integer_bases = [np.asarray(matrix, dtype=np.int64) for matrix in exact_bases]
    if args.second_face:
        face_data = np.load(Path(args.second_face))
        z0 = np.asarray(face_data["Z0"])
        old_norms = np.asarray(face_data["norms0"])
        z0_integer = old_norms[:, None] * z0 * old_norms[None, :]
        values, vectors = np.linalg.eigh((z0_integer + z0_integer.T) / 2)
        space = vectors[:, -6:]
        _, _, face_pivots = qr(space.T, pivoting=True, mode="economic")
        pivot_rows = sorted(int(index) for index in face_pivots[:6])
        normalized_space = space @ np.linalg.inv(space[pivot_rows, :])
        half_integral_kernel = np.rint(2 * normalized_space).astype(np.int64)
        error = np.max(np.abs(normalized_space - half_integral_kernel / 2))
        if error > 1e-6:
            raise AssertionError(f"second face did not rationalize: {error}")
        second_complement = integer_orthogonal_complement(half_integral_kernel)
        integer_bases[0] = integer_bases[0] @ second_complement
        print(
            f"second face: kernel_rank=6 complement={second_complement.shape} "
            f"rounding_error={error:.3e}"
        )
    if args.third_face:
        face_data = np.load(Path(args.third_face))
        z1 = np.asarray(face_data["Z1"])
        old_norms = np.asarray(face_data["norms1"])
        z1_integer = old_norms[:, None] * z1 * old_norms[None, :]
        _, vectors = np.linalg.eigh((z1_integer + z1_integer.T) / 2)
        space = vectors[:, -6:]
        _, _, face_pivots = qr(space.T, pivoting=True, mode="economic")
        pivot_rows = sorted(int(index) for index in face_pivots[:6])
        normalized_space = space @ np.linalg.inv(space[pivot_rows, :])
        half_integral_kernel = np.rint(2 * normalized_space).astype(np.int64)
        error = np.max(np.abs(normalized_space - half_integral_kernel / 2))
        if error > 1e-6:
            raise AssertionError(f"third face did not rationalize: {error}")
        third_complement = integer_orthogonal_complement(half_integral_kernel)
        integer_bases[1] = integer_bases[1] @ third_complement
        print(
            f"third face: kernel_rank=6 complement={third_complement.shape} "
            f"rounding_error={error:.3e}"
        )
    norms = [np.linalg.norm(matrix.astype(float), axis=0) for matrix in integer_bases]
    bases = [matrix / norm[None, :] for matrix, norm in zip(integer_bases, norms)]
    sizes = [matrix.shape[1] for matrix in bases]
    grams = [cp.Variable((size, size), symmetric=True) for size in sizes]
    margin = cp.Variable()
    constraints = [gram - margin * np.eye(size) >> 0 for gram, size in zip(grams, sizes)]
    all_pulled = []
    for m0, m1, rhs, core, power, scale in equations:
        pulled = [basis.T @ matrix @ basis for basis, matrix in zip(bases, (m0, m1))]
        all_pulled.append((pulled, rhs, core, power, scale))

    def symmetric_vector(matrix):
        indices = np.triu_indices(matrix.shape[0])
        values = matrix[indices].copy()
        values[indices[0] != indices[1]] *= 2
        return values

    rows = np.vstack([
        np.concatenate([symmetric_vector(matrix) for matrix in pulled])
        for pulled, *_ in all_pulled
    ])
    rhs_vector = np.asarray([rhs for _, rhs, *_ in all_pulled], dtype=float)
    _, triangular, pivots = qr(rows.T, pivoting=True, mode="economic")
    tolerance = max(rows.shape) * np.finfo(float).eps * abs(triangular[0, 0])
    rank = int(np.count_nonzero(np.abs(np.diag(triangular)) > tolerance))
    augmented_rank = np.linalg.matrix_rank(np.c_[rows, rhs_vector])
    print(f"linear equations={len(equations)} reduced_rank={rank} augmented_rank={augmented_rank}")
    if augmented_rank != rank:
        raise AssertionError((rank, augmented_rank))
    selected = sorted(int(index) for index in pivots[:rank])
    pulled_equations = [all_pulled[index] for index in selected]
    for pulled, rhs, *_ in pulled_equations:
        norm = np.linalg.norm(np.concatenate([matrix.ravel() for matrix in pulled]))
        constraints.append(
            sum(cp.sum(cp.multiply(matrix / norm, gram)) for matrix, gram in zip(pulled, grams))
            == rhs / norm
        )
    if args.find_exposer:
        dual = cp.Variable(rank)
        exposers = []
        for block in range(2):
            exposers.append(sum(
                dual[index] * equation[0][block]
                / np.linalg.norm(np.concatenate([matrix.ravel() for matrix in equation[0]]))
                for index, equation in enumerate(pulled_equations)
            ))
        dual_constraints = [item >> 0 for item in exposers]
        dual_constraints.append(sum(
            dual[index] * equation[1]
            / np.linalg.norm(np.concatenate([matrix.ravel() for matrix in equation[0]]))
            for index, equation in enumerate(pulled_equations)
        ) == 0)
        dual_constraints.append(sum(cp.trace(item) for item in exposers) == 1)
        dual_problem = cp.Problem(cp.Minimize(cp.sum_squares(dual)), dual_constraints)
        dual_problem.solve(solver="CLARABEL", tol_gap_abs=1e-10, tol_feas=1e-10,
                           tol_gap_rel=1e-10, max_iter=500, verbose=args.verbose)
        print(f"exposer_status={dual_problem.status} objective={dual_problem.value}")
        if dual.value is None:
            return
        values = []
        for index, item in enumerate(exposers):
            value = np.asarray(item.value)
            values.append(value)
            eigenvalues = np.linalg.eigvalsh((value + value.T) / 2)
            print(
                f"Z{index}: min={eigenvalues[0]:.6e} max={eigenvalues[-1]:.6e} "
                f"rank1e-7={np.count_nonzero(eigenvalues > 1e-7)}"
            )
        if args.save:
            np.savez(args.save, dual=dual.value, Z0=values[0], Z1=values[1],
                     B0=integer_bases[0], B1=integer_bases[1],
                     norms0=norms[0], norms1=norms[1], selected=np.asarray(selected))
        return
    problem = cp.Problem(cp.Maximize(margin), constraints)
    options = {"verbose": args.verbose}
    if args.solver == "CLARABEL":
        options.update(tol_gap_abs=1e-10, tol_feas=1e-10, tol_gap_rel=1e-10, max_iter=500)
    elif args.solver == "CVXOPT":
        options.update(abstol=1e-9, reltol=1e-9, feastol=1e-9, max_iters=500)
    else:
        options.update(eps=1e-7, max_iters=500_000)
    problem.solve(solver=args.solver, **options)
    print(f"status={problem.status} margin={margin.value} sizes={sizes} equations={rank}")
    if any(gram.value is None for gram in grams):
        return
    residuals = [
        abs(sum(np.sum(matrix * gram.value) for matrix, gram in zip(pulled, grams)) - rhs)
        for pulled, rhs, *_ in pulled_equations
    ]
    reduced_grams = [
        gram.value / norm[:, None] / norm[None, :]
        for gram, norm in zip(grams, norms)
    ]
    for index, (gram, reduced) in enumerate(zip(grams, reduced_grams)):
        print(
            f"Y{index}: normalized_min={np.linalg.eigvalsh(gram.value)[0]:.9g} "
            f"integer_basis_min={np.linalg.eigvalsh(reduced)[0]:.9g}"
        )
    print(f"max_residual={max(residuals):.9g}")
    if args.save:
        np.savez(
            args.save,
            B0=integer_bases[0], B1=integer_bases[1],
            Y0=reduced_grams[0], Y1=reduced_grams[1],
            normalized_Y0=grams[0].value, normalized_Y1=grams[1].value,
            norms0=norms[0], norms1=norms[1], margin=margin.value,
        )


if __name__ == "__main__":
    main()
