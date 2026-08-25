"""Full four-label/one-branch rooted SOS, reduced by S4 symmetry.

The 1024 basis elements are all simple graphs on four labelled roots and
one unlabelled branch vertex.  Their products have six vertices.  Since the
coefficient map forgets the labels, every Gram matrix may be averaged over
S4.  We realize one multiplicity-space slice of each of the five irreducible
S4 representations; the corresponding dimensions are

    90, 150, 96, 90, 22

with representation multiplicities 1, 3, 2, 3, 1.  This is an ordinary
partially-labelled graphon sum of squares, not an induced flag calculation.

This file is a numerical discovery tool.  A feasible result is not a proof
until it has been rationalized and checked coefficient by coefficient.
"""

from __future__ import annotations

import argparse
import itertools
from collections import defaultdict

import cvxpy as cp
import networkx as nx
import numpy as np
from scipy import sparse
from scipy.linalg import qr

from rooted_sos_search import fixed_density_key, phi_value


PERMS = list(itertools.permutations(range(4)))


def compose(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(left[right[i]] for i in range(4))


def inverse(permutation: tuple[int, ...]) -> tuple[int, ...]:
    result = [0] * 4
    for i, value in enumerate(permutation):
        result[value] = i
    return tuple(result)


def cycle_type(permutation: tuple[int, ...]) -> tuple[int, ...]:
    unseen = set(range(4))
    lengths = []
    while unseen:
        start = min(unseen)
        current = start
        length = 0
        while current in unseen:
            unseen.remove(current)
            length += 1
            current = permutation[current]
        lengths.append(length)
    return tuple(sorted(lengths, reverse=True))


CHARACTERS = {
    "4": {(1, 1, 1, 1): 1, (2, 1, 1): 1, (2, 2): 1, (3, 1): 1, (4,): 1},
    "31": {(1, 1, 1, 1): 3, (2, 1, 1): 1, (2, 2): -1, (3, 1): 0, (4,): -1},
    "22": {(1, 1, 1, 1): 2, (2, 1, 1): 0, (2, 2): 2, (3, 1): -1, (4,): 0},
    "211": {(1, 1, 1, 1): 3, (2, 1, 1): -1, (2, 2): -1, (3, 1): 0, (4,): 1},
    "1111": {(1, 1, 1, 1): 1, (2, 1, 1): -1, (2, 2): 1, (3, 1): 1, (4,): -1},
}
DIMENSIONS = {"4": 1, "31": 3, "22": 2, "211": 3, "1111": 1}
EXPECTED_MULTIPLICITIES = {"4": 90, "31": 150, "22": 96, "211": 90, "1111": 22}


def generated_subgroup(generators: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
    identity = tuple(range(4))
    group = {identity}
    changed = True
    while changed:
        changed = False
        for left in list(group):
            for right in generators:
                for item in (compose(left, right), compose(right, left)):
                    if item not in group:
                        group.add(item)
                        changed = True
    return sorted(group)


def slice_subgroups() -> dict[str, list[tuple[int, ...]]]:
    identity = tuple(range(4))
    s4 = PERMS
    a4 = [p for p in PERMS if CHARACTERS["1111"][cycle_type(p)] == 1]
    s3 = [p for p in PERMS if p[3] == 3]
    v4 = generated_subgroup([(1, 0, 2, 3), (0, 1, 3, 2)])
    a3 = generated_subgroup([(1, 2, 0, 3)])
    assert identity in v4 and [len(s4), len(a4), len(s3), len(v4), len(a3)] == [24, 12, 6, 4, 3]
    return {"4": s4, "31": s3, "22": v4, "211": a3, "1111": a4}


LABEL_EDGES = list(itertools.combinations(range(4), 2))


def permute_basis_index(index: int, permutation: tuple[int, ...]) -> int:
    label_mask = index // 16
    branch_mask = index % 16
    new_label_mask = 0
    for bit, (u, v) in enumerate(LABEL_EDGES):
        if label_mask & (1 << bit):
            edge = tuple(sorted((permutation[u], permutation[v])))
            new_label_mask |= 1 << LABEL_EDGES.index(edge)
    new_branch_mask = 0
    for root in range(4):
        if branch_mask & (1 << root):
            new_branch_mask |= 1 << permutation[root]
    return 16 * new_label_mask + new_branch_mask


def permutation_actions() -> dict[tuple[int, ...], np.ndarray]:
    return {
        permutation: np.asarray(
            [permute_basis_index(index, permutation) for index in range(1024)], dtype=np.int32
        )
        for permutation in PERMS
    }


def orbit_transform(subgroup: list[tuple[int, ...]], actions) -> np.ndarray:
    unseen = set(range(1024))
    columns = []
    while unseen:
        representative = min(unseen)
        orbit = sorted({int(actions[p][representative]) for p in subgroup})
        vector = np.zeros(1024)
        vector[orbit] = 1 / np.sqrt(len(orbit))
        columns.append(vector)
        unseen.difference_update(orbit)
    return np.asarray(columns).T


def irrep_transforms() -> tuple[list[np.ndarray], list[int], list[str]]:
    actions = permutation_actions()
    transforms = []
    names = ["4", "31", "22", "211", "1111"]
    for name in names:
        source = orbit_transform(slice_subgroups()[name], actions)
        projected = np.zeros_like(source)
        factor = DIMENSIONS[name] / 24
        for permutation in PERMS:
            character = CHARACTERS[name][cycle_type(permutation)]
            if character:
                # R_g has a one in row action_g(i), column i.
                projected[actions[permutation], :] += factor * character * source
        q, triangular, _ = qr(projected, mode="economic", pivoting=True)
        diagonal = np.abs(np.diag(triangular))
        rank = int(np.count_nonzero(diagonal > 1e-8))
        if rank != EXPECTED_MULTIPLICITIES[name]:
            raise AssertionError((name, source.shape, rank, diagonal[: rank + 2]))
        transforms.append(q[:, :rank])
        print(f"S4 slice {name}: source={source.shape[1]} multiplicity={rank}", flush=True)
    return transforms, [DIMENSIONS[name] for name in names], names


def restrict_transforms(
    transforms: list[np.ndarray], basis_indices: list[int]
) -> list[np.ndarray]:
    """Restrict the S4 slices to an invariant coordinate subset."""
    restricted = []
    index_array = np.asarray(basis_indices, dtype=int)
    for transform in transforms:
        compression = transform[index_array, :].T @ transform[index_array, :]
        values, vectors = np.linalg.eigh((compression + compression.T) / 2)
        keep = values > 0.5
        lifted = transform @ vectors[:, keep]
        outside = np.ones(1024, dtype=bool)
        outside[index_array] = False
        error = np.max(np.abs(lifted[outside, :])) if np.any(outside) and np.any(keep) else 0.0
        result = lifted[index_array, :]
        if error > 1e-7 or np.max(np.abs(result.T @ result - np.eye(result.shape[1]))) > 1e-7:
            raise AssertionError((error, values[:3], values[-3:]))
        restricted.append(result)
    return restricted


YOUNG_ROWS_COLUMNS = {
    "4": ([[0, 1, 2, 3]], [[0], [1], [2], [3]]),
    "31": ([[0, 1, 2], [3]], [[0, 3], [1], [2]]),
    "22": ([[0, 1], [2, 3]], [[0, 2], [1, 3]]),
    "211": ([[0, 1], [2], [3]], [[0, 2, 3], [1]]),
    "1111": ([[0], [1], [2], [3]], [[0, 1, 2, 3]]),
}


def setwise_stabilizer(blocks: list[list[int]]) -> list[tuple[int, ...]]:
    block_sets = [set(block) for block in blocks]
    return [
        permutation for permutation in PERMS
        if all({permutation[item] for item in block} == block_set
               for block, block_set in zip(blocks, block_sets))
    ]


def permutation_sign(permutation: tuple[int, ...]) -> int:
    inversions = sum(
        permutation[i] > permutation[j]
        for i in range(4) for j in range(i + 1, 4)
    )
    return -1 if inversions % 2 else 1


def young_integer_transforms(
    label_degree: int,
    degree_three_kind: str = "all",
) -> tuple[list[np.ndarray], list[int], list[str], list[int]]:
    """Integer bases for primitive Young-symmetrizer slices.

    To turn a PSD Gram matrix in one returned slice into an invariant PSD
    Gram matrix, sum all 24 S4 translates.  Consequently every block has
    coefficient factor 24 in the unlabeled density equations.
    """
    names = ["4", "31", "22", "211", "1111"]
    basis_indices = rooted_basis_indices(label_degree, degree_three_kind)
    position = {index: local for local, index in enumerate(basis_indices)}
    actions = permutation_actions()
    local_actions = {
        permutation: np.asarray(
            [position[int(actions[permutation][index])] for index in basis_indices],
            dtype=np.int32,
        )
        for permutation in PERMS
    }
    if label_degree == 6:
        expected_dimensions = EXPECTED_MULTIPLICITIES
    else:
        numerical, _, numerical_names = irrep_transforms()
        numerical_restrictions = restrict_transforms(numerical, basis_indices)
        expected_dimensions = {
            name: numerical_restrictions[numerical_names.index(name)].shape[1]
            for name in names
        }
    transforms = []
    for name in names:
        row_blocks, column_blocks = YOUNG_ROWS_COLUMNS[name]
        row_group = setwise_stabilizer(row_blocks)
        column_group = setwise_stabilizer(column_blocks)
        operator = np.zeros((len(basis_indices), len(basis_indices)), dtype=np.int16)
        columns = np.arange(len(basis_indices))
        for row in row_group:
            for column in column_group:
                permutation = compose(row, column)
                operator[local_actions[permutation], columns] += permutation_sign(column)
        _, triangular, pivots = qr(operator.astype(float), mode="economic", pivoting=True)
        rank = int(np.count_nonzero(np.abs(np.diag(triangular)) > 1e-8))
        expected = expected_dimensions[name]
        if rank != expected:
            raise AssertionError((name, rank, expected))
        transform = operator[:, np.asarray(pivots[:rank], dtype=int)].astype(np.int64)
        transforms.append(transform)
        print(
            f"Young slice {name}: rows={len(row_group)} columns={len(column_group)} "
            f"multiplicity={rank} maxabs={np.max(np.abs(transform))}", flush=True,
        )
    return transforms, [24] * len(names), names, basis_indices


def rooted_basis_indices(label_degree: int, degree_three_kind: str = "all") -> list[int]:
    if degree_three_kind not in {
        "all", "triangle", "star", "path", "paw4", "cycle4",
        "triangle_paw4", "star_paw4", "path_paw4", "all3_paw4", "all4", "none"
    }:
        raise ValueError(degree_three_kind)
    result = []
    for index in range(1024):
        label_mask = index // 16
        count = bin(label_mask).count("1")
        if count > label_degree:
            continue
        if count == 3 and degree_three_kind != "all":
            degrees = [0] * 4
            for bit, (u, v) in enumerate(LABEL_EDGES):
                if label_mask & (1 << bit):
                    degrees[u] += 1
                    degrees[v] += 1
            shape = {
                (0, 2, 2, 2): "triangle",
                (1, 1, 1, 3): "star",
                (1, 1, 2, 2): "path",
            }[tuple(sorted(degrees))]
            accepted_three = {
                "triangle_paw4": {"triangle"},
                "star_paw4": {"star"},
                "path_paw4": {"path"},
                "all3_paw4": {"triangle", "star", "path"},
            }.get(degree_three_kind, {degree_three_kind})
            if shape not in accepted_three:
                continue
        if count == 4 and degree_three_kind != "all":
            degrees = [0] * 4
            for bit, (u, v) in enumerate(LABEL_EDGES):
                if label_mask & (1 << bit):
                    degrees[u] += 1
                    degrees[v] += 1
            shape = {
                (2, 2, 2, 2): "cycle4",
                (1, 2, 2, 3): "paw4",
            }[tuple(sorted(degrees))]
            accepted_four = {
                "paw4": {"paw4"},
                "cycle4": {"cycle4"},
                "triangle_paw4": {"paw4"},
                "star_paw4": {"paw4"},
                "path_paw4": {"paw4"},
                "all3_paw4": {"paw4"},
                "all4": {"paw4", "cycle4"},
            }.get(degree_three_kind, set())
            if shape not in accepted_four:
                continue
        result.append(index)
    return result


def graph_key(label_union: int, left_branch: int, right_branch: int) -> tuple[int, int]:
    graph = nx.Graph()
    graph.add_nodes_from(range(6))
    graph.add_edges_from(
        edge for bit, edge in enumerate(LABEL_EDGES) if label_union & (1 << bit)
    )
    graph.add_edges_from((root, 4) for root in range(4) if left_branch & (1 << root))
    graph.add_edges_from((root, 5) for root in range(4) if right_branch & (1 << root))
    return fixed_density_key(graph)


def raw_sparse_matrices(p: float) -> dict[int, sparse.csr_matrix]:
    entries = defaultdict(lambda: ([], [], []))
    cache = {}
    for i in range(1024):
        left_label, left_branch = divmod(i, 16)
        for j in range(i, 1024):
            right_label, right_branch = divmod(j, 16)
            lookup = (left_label | right_label, left_branch, right_branch)
            if lookup not in cache:
                cache[lookup] = graph_key(*lookup)
            core, isolated = cache[lookup]
            rows, columns, values = entries[core]
            value = p**isolated
            rows.append(i)
            columns.append(j)
            values.append(value)
            if i != j:
                rows.append(j)
                columns.append(i)
                values.append(value)
    return {
        core: sparse.coo_matrix((values, (rows, columns)), shape=(1024, 1024)).tocsr()
        for core, (rows, columns, values) in entries.items()
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--atlas", type=int, required=True)
    parser.add_argument("--p", type=float, required=True)
    parser.add_argument("--solver", choices=("CLARABEL", "SCS"), default="CLARABEL")
    parser.add_argument("--objective", choices=("zero", "trace", "margin"), default="zero")
    parser.add_argument(
        "--label-degree", type=int, default=6,
        help="Keep label-edge masks of size at most this value (default: full basis).",
    )
    parser.add_argument("--save")
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()

    transforms, factors, names = irrep_transforms()
    basis_indices = [
        index for index in range(1024)
        if bin(index // 16).count("1") <= args.label_degree
    ]
    if len(basis_indices) < 1024:
        transforms = restrict_transforms(transforms, basis_indices)
    raw_full = raw_sparse_matrices(args.p)
    raw = {
        core: matrix[np.asarray(basis_indices), :][:, np.asarray(basis_indices)]
        for core, matrix in raw_full.items()
    }
    matrices = {
        core: [transform.T @ matrix @ transform for transform in transforms]
        for core, matrix in raw.items()
    }
    target_core, target_isolated = fixed_density_key(nx.graph_atlas(args.atlas))
    rhs = defaultdict(float)
    rhs[target_core] += args.p**target_isolated
    rhs[0] -= phi_value(nx.graph_atlas(args.atlas), args.p)
    cores = sorted(set(matrices) | set(rhs))
    sizes = [transform.shape[1] for transform in transforms]
    grams = [cp.Variable((size, size), symmetric=True) for size in sizes]
    constraints = [gram >> 0 for gram in grams]

    equation_specs = []
    for core in cores:
        blocks = matrices.get(core, [np.zeros((size, size)) for size in sizes])
        equation_specs.append((blocks, rhs[core]))

    def symmetric_vector(matrix):
        indices = np.triu_indices(matrix.shape[0])
        values = matrix[indices].copy()
        values[indices[0] != indices[1]] *= 2
        return values

    rows = np.vstack([
        np.concatenate([factor * symmetric_vector(matrix) for factor, matrix in zip(factors, blocks)])
        for blocks, _ in equation_specs
    ])
    rhs_vector = np.asarray([value for _, value in equation_specs])
    _, triangular, pivots = qr(rows.T, mode="economic", pivoting=True)
    tolerance = max(rows.shape) * np.finfo(float).eps * abs(triangular[0, 0])
    rank = int(np.count_nonzero(np.abs(np.diag(triangular)) > tolerance))
    augmented_rank = np.linalg.matrix_rank(np.c_[rows, rhs_vector])
    print(
        f"atlas={args.atlas} p={args.p} blocks={dict(zip(names, sizes))} "
        f"equations={len(equation_specs)} rank={rank} augmented={augmented_rank}", flush=True
    )
    if augmented_rank != rank:
        raise AssertionError((rank, augmented_rank))
    selected = sorted(int(index) for index in pivots[:rank])
    for index in selected:
        blocks, target = equation_specs[index]
        scale = np.linalg.norm(rows[index])
        constraints.append(sum(
            factor * cp.sum(cp.multiply(matrix / scale, gram))
            for factor, matrix, gram in zip(factors, blocks, grams)
        ) == target / scale)

    if args.objective == "zero":
        objective = cp.Minimize(0)
    elif args.objective == "trace":
        objective = cp.Minimize(sum(factor * cp.trace(gram) for factor, gram in zip(factors, grams)))
    else:
        margin = cp.Variable()
        constraints.extend(gram - margin * np.eye(size) >> 0 for gram, size in zip(grams, sizes))
        objective = cp.Maximize(margin)
    problem = cp.Problem(objective, constraints)
    if args.solver == "CLARABEL":
        problem.solve(solver="CLARABEL", tol_gap_abs=1e-8, tol_feas=1e-8,
                      max_iter=500, verbose=args.verbose)
    else:
        problem.solve(solver="SCS", eps=1e-6, max_iters=300_000, verbose=args.verbose)
    print(f"status={problem.status} objective={problem.value}")
    if any(gram.value is None for gram in grams):
        return
    residuals = [
        abs(sum(factor * np.sum(matrix * gram.value)
                for factor, matrix, gram in zip(factors, blocks, grams)) - target)
        for blocks, target in equation_specs
    ]
    for name, gram in zip(names, grams):
        eigenvalues = np.linalg.eigvalsh((gram.value + gram.value.T) / 2)
        print(f"{name}: min={eigenvalues[0]:.6e} rank1e-7={np.count_nonzero(eigenvalues > 1e-7)}")
    print(f"max_residual={max(residuals):.6e}")
    if args.save:
        np.savez(args.save, **{f"Q_{name}": gram.value for name, gram in zip(names, grams)})


if __name__ == "__main__":
    main()
