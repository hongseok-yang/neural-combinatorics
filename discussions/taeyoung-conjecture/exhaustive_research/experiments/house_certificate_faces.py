"""Inspect the exact faces suggested by interval-SOS solutions for Atlas 43.

This is a discovery/audit helper.  It reconstructs the full 64-dimensional
Gram matrices from the S3 multiplicity blocks and tries to recognize their
numerical kernels as rational subspaces.
"""

from __future__ import annotations

import argparse
import itertools
from fractions import Fraction

import numpy as np
from scipy.linalg import qr

from rooted_sos_search import label_s3_irrep_transforms, rooted_basis


def permutation_matrices(basis):
    edge_to_index = {
        frozenset((min(u, v), max(u, v)) for u, v in graph.edges()): index
        for index, graph in enumerate(basis)
    }
    result = []
    for permutation in itertools.permutations(range(3)):
        matrix = np.zeros((len(basis), len(basis)))
        for index, graph in enumerate(basis):
            mapping = {label: permutation[label] for label in range(3)}
            mapping[3] = 3
            edges = frozenset(
                (min(mapping[u], mapping[v]), max(mapping[u], mapping[v]))
                for u, v in graph.edges()
            )
            matrix[edge_to_index[edges], index] = 1
        result.append(matrix)
    return result


def reconstruct(blocks, transforms, permutations, polynomial_degree):
    size = transforms[0].shape[0]
    lifts = [np.kron(np.eye(polynomial_degree), transform) for transform in transforms]
    actions = [np.kron(np.eye(polynomial_degree), action) for action in permutations]
    result = lifts[0] @ blocks[0] @ lifts[0].T
    result += lifts[1] @ blocks[1] @ lifts[1].T
    seed = lifts[2] @ blocks[2] @ lifts[2].T
    result += sum(action @ seed @ action.T for action in actions) / 3
    return (result + result.T) / 2


def rational_kernel(matrix, nullity, max_denominator):
    values, vectors = np.linalg.eigh(matrix)
    kernel = vectors[:, :nullity]
    # Select a well-conditioned set of pivot rows, then normalize those rows
    # to the identity.  The resulting coordinates are invariant under the
    # arbitrary orthogonal basis chosen by eigh.
    _, _, pivots = qr(kernel.T, pivoting=True, mode="economic")
    pivot_rows = sorted(int(index) for index in pivots[:nullity])
    normalized = kernel @ np.linalg.inv(kernel[pivot_rows, :])
    rational = np.array(
        [
            [float(Fraction(float(value)).limit_denominator(max_denominator)) for value in row]
            for row in normalized
        ]
    )
    residual = np.linalg.norm(matrix @ rational, ord=2)
    subspace_error = np.linalg.norm(
        rational @ np.linalg.pinv(rational) - kernel @ kernel.T, ord=2
    )
    max_entry_error = np.max(np.abs(rational - normalized))
    return values, pivot_rows, rational, residual, subspace_error, max_entry_error


def rational_range(matrix, rank, max_denominator):
    values, vectors = np.linalg.eigh((matrix + matrix.T) / 2)
    space = vectors[:, -rank:]
    _, _, pivots = qr(space.T, pivoting=True, mode="economic")
    pivot_rows = sorted(int(index) for index in pivots[:rank])
    normalized = space @ np.linalg.inv(space[pivot_rows, :])
    rational = np.array(
        [[float(Fraction(float(value)).limit_denominator(max_denominator)) for value in row]
         for row in normalized]
    )
    residual = np.linalg.norm(matrix - rational @ np.linalg.pinv(rational) @ matrix, ord=2)
    subspace_error = np.linalg.norm(
        rational @ np.linalg.pinv(rational) - space @ space.T, ord=2
    )
    return values, pivot_rows, rational, residual, subspace_error, np.max(np.abs(rational - normalized))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate")
    parser.add_argument("--max-denominator", type=int, default=1000)
    parser.add_argument("--show-space", action="store_true")
    args = parser.parse_args()

    data = np.load(args.certificate)
    if "Z0" in data.files:
        for index in range(2):
            matrix = np.asarray(data[f"Z{index}"])
            norms = np.asarray(data[f"norms{index}"])
            matrix = norms[:, None] * matrix * norms[None, :]
            rank = int(np.count_nonzero(np.linalg.eigvalsh((matrix + matrix.T) / 2) > 1e-7))
            if not rank:
                continue
            values, pivots, space, residual, subspace_error, entry_error = rational_range(
                matrix, rank, args.max_denominator
            )
            print(
                f"Z{index}_integer_coordinates: dimension={matrix.shape[0]} rank={rank} "
                f"range_residual={residual:.3e} subspace_error={subspace_error:.3e} "
                f"entry_error={entry_error:.3e} pivots={pivots}"
            )
            if args.show_space:
                for row_index, row in enumerate(space):
                    entries = [(column, str(Fraction(float(value)).limit_denominator(args.max_denominator)))
                               for column, value in enumerate(row) if abs(value) > 1e-7]
                    if entries:
                        print(f"  row {row_index}: {entries}")
        return
    if "Z_0" in data.files:
        for key in sorted(item for item in data.files if item.startswith("Z_")):
            matrix = np.asarray(data[key])
            rank = int(np.count_nonzero(np.linalg.eigvalsh((matrix + matrix.T) / 2) > 1e-7))
            if not rank:
                continue
            values, pivots, space, residual, subspace_error, entry_error = rational_range(
                matrix, rank, args.max_denominator
            )
            print(
                f"{key}: dimension={matrix.shape[0]} rank={rank} min_positive={values[-rank]:.6g} "
                f"range_residual={residual:.3e} subspace_error={subspace_error:.3e} "
                f"entry_error={entry_error:.3e} pivots={pivots}"
            )
            if args.show_space:
                for row_index, row in enumerate(space):
                    entries = [
                        (column, str(Fraction(float(value)).limit_denominator(args.max_denominator)))
                        for column, value in enumerate(row) if abs(value) > 1e-8
                    ]
                    if entries:
                        print(f"  row {row_index}: {entries}")
        return
    basis = rooted_basis(3, 1)
    is_full = "G0_1" not in data.files
    if not is_full:
        transforms, _ = label_s3_irrep_transforms(basis)
        permutations = permutation_matrices(basis)
    for prefix, degree in (("G0", 2), ("G1", 1)):
        if is_full:
            matrix = (data[f"{prefix}_0"] + data[f"{prefix}_0"].T) / 2
        else:
            blocks = [data[f"{prefix}_{index}"] for index in range(3)]
            matrix = reconstruct(blocks, transforms, permutations, degree)
        nullity = int(np.count_nonzero(np.linalg.eigvalsh(matrix) < 1e-7))
        values, pivots, kernel, residual, subspace_error, entry_error = rational_kernel(
            matrix, nullity, args.max_denominator
        )
        print(
            f"{prefix}: dimension={matrix.shape[0]} nullity={nullity} "
            f"min={values[0]:.3e} first_positive={values[nullity]:.6g} "
            f"kernel_residual={residual:.3e} subspace_error={subspace_error:.3e} "
            f"entry_error={entry_error:.3e} pivots={pivots}"
        )
        nonzero = kernel[np.abs(kernel) > 1e-12]
        denominators = [Fraction(float(value)).limit_denominator(args.max_denominator).denominator for value in nonzero]
        print(f"  rational coordinate denominator max={max(denominators, default=1)}")


if __name__ == "__main__":
    main()
