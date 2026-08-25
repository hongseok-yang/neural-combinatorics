"""Prototype direct rooted-graph sum-of-squares search.

This does *not* use induced-density flags or asymptotic flag-algebra rules.
For a list of partially labelled simple graphs F_i it asks whether

    t(H,W) - Phi_H(p) = integral sum_ij Q_ij F_i(x) F_j(x)

holds modulo the exact fixed-density identity t(G union K2,W)=p t(G,W),
with Q positive semidefinite.  Any successful floating-point solution must
still be rationalized and checked coefficient-by-coefficient before it is a
proof.  The script is a discovery tool for small explicit graphon SOS
identities.
"""

from __future__ import annotations

import argparse
import itertools
from collections import defaultdict

import cvxpy as cp
import networkx as nx
import numpy as np
import sympy as sp
from networkx.algorithms.polynomials import chromatic_polynomial


def phi_value(graph: nx.Graph, density: float) -> float:
    p = sp.symbols("p")
    polynomial = chromatic_polynomial(graph)
    x = next(iter(polynomial.free_symbols))
    expression = sp.factor(
        (1 - p) ** graph.number_of_nodes() * polynomial.subs(x, 1 / (1 - p))
    )
    return float(expression.subs(p, density))


ATLAS = nx.graph_atlas_g()
ATLAS_GROUPS: dict[tuple[int, int], list[tuple[int, nx.Graph]]] = defaultdict(list)
for atlas_id, graph in enumerate(ATLAS):
    if graph.number_of_nodes() <= 6:
        ATLAS_GROUPS[(graph.number_of_nodes(), graph.number_of_edges())].append(
            (atlas_id, graph)
        )


def atlas_id(graph: nx.Graph) -> int:
    graph = nx.convert_node_labels_to_integers(graph)
    for candidate_id, candidate in ATLAS_GROUPS[
        (graph.number_of_nodes(), graph.number_of_edges())
    ]:
        if nx.is_isomorphic(graph, candidate):
            return candidate_id
    raise AssertionError(f"graph not found in the six-vertex atlas: {sorted(graph.edges())}")


def fixed_density_key(graph: nx.Graph) -> tuple[int, int]:
    """Return (core Atlas id, number of isolated-edge components)."""
    graph = graph.copy()
    graph.remove_nodes_from(list(nx.isolates(graph)))
    edge_components = 0
    remove: list[int] = []
    for component in nx.connected_components(graph):
        subgraph = graph.subgraph(component)
        if subgraph.number_of_nodes() == 2 and subgraph.number_of_edges() == 1:
            edge_components += 1
            remove.extend(component)
    graph.remove_nodes_from(remove)
    graph.remove_nodes_from(list(nx.isolates(graph)))
    return atlas_id(graph), edge_components


def rooted_basis(
    label_count: int, branch_count: int, include_label_edges: bool = True
) -> list[nx.Graph]:
    order = label_count + branch_count
    edges = [
        edge
        for edge in itertools.combinations(range(order), 2)
        if include_label_edges or not (edge[0] < label_count and edge[1] < label_count)
    ]
    basis: list[nx.Graph] = []
    for mask in range(1 << len(edges)):
        graph = nx.Graph()
        graph.add_nodes_from(range(order))
        graph.add_edges_from(edge for bit, edge in enumerate(edges) if mask & (1 << bit))
        basis.append(graph)
    return basis


def rooted_product(
    left: nx.Graph, right: nx.Graph, label_count: int, branch_count: int
) -> nx.Graph:
    product = nx.Graph()
    product.add_nodes_from(range(label_count + 2 * branch_count))
    product.add_edges_from(left.edges())
    mapping = {vertex: vertex for vertex in range(label_count)}
    mapping.update(
        {
            label_count + index: label_count + branch_count + index
            for index in range(branch_count)
        }
    )
    product.add_edges_from((mapping[u], mapping[v]) for u, v in right.edges())
    return product


def label_orbit_transform(basis: list[nx.Graph], label_count: int) -> np.ndarray:
    """Columns are normalized orbit sums under permutations of the labels."""
    permutations = list(itertools.permutations(range(label_count)))
    edge_to_index = {
        frozenset((min(u, v), max(u, v)) for u, v in graph.edges()): index
        for index, graph in enumerate(basis)
    }
    unseen = set(range(len(basis)))
    orbits: list[list[int]] = []
    while unseen:
        representative = min(unseen)
        orbit: set[int] = set()
        for permutation in permutations:
            mapping = {label: permutation[label] for label in range(label_count)}
            mapping.update({vertex: vertex for vertex in basis[representative] if vertex >= label_count})
            edges = frozenset(
                (min(mapping[u], mapping[v]), max(mapping[u], mapping[v]))
                for u, v in basis[representative].edges()
            )
            orbit.add(edge_to_index[edges])
        members = sorted(orbit)
        orbits.append(members)
        unseen.difference_update(members)
    transform = np.zeros((len(basis), len(orbits)))
    for column, members in enumerate(orbits):
        transform[members, column] = 1 / np.sqrt(len(members))
    return transform


def label_s3_irrep_transforms(basis: list[nx.Graph]) -> tuple[list[np.ndarray], list[int]]:
    """Return multiplicity-space slices for the trivial, sign, standard S3 blocks."""
    label_count = 3
    permutations = list(itertools.permutations(range(label_count)))
    edge_to_index = {
        frozenset((min(u, v), max(u, v)) for u, v in graph.edges()): index
        for index, graph in enumerate(basis)
    }
    representations: list[np.ndarray] = []
    signs: list[int] = []
    for permutation in permutations:
        matrix = np.zeros((len(basis), len(basis)))
        inversions = sum(
            permutation[i] > permutation[j]
            for i in range(label_count)
            for j in range(i + 1, label_count)
        )
        signs.append(-1 if inversions % 2 else 1)
        for index, graph in enumerate(basis):
            mapping = {label: permutation[label] for label in range(label_count)}
            mapping.update({vertex: vertex for vertex in graph if vertex >= label_count})
            edges = frozenset(
                (min(mapping[u], mapping[v]), max(mapping[u], mapping[v]))
                for u, v in graph.edges()
            )
            matrix[edge_to_index[edges], index] = 1
        representations.append(matrix)

    trivial_projector = sum(representations) / 6
    sign_projector = sum(sign * matrix for sign, matrix in zip(signs, representations)) / 6
    identity = np.eye(len(basis))
    standard_projector = identity - trivial_projector - sign_projector

    def range_basis(projector: np.ndarray, threshold: float = 0.5) -> np.ndarray:
        values, vectors = np.linalg.eigh((projector + projector.T) / 2)
        return vectors[:, values > threshold]

    trivial = range_basis(trivial_projector)
    sign = range_basis(sign_projector)
    transposition = representations[permutations.index((1, 0, 2))]
    standard_plus_projector = standard_projector @ ((identity + transposition) / 2) @ standard_projector
    standard_plus = range_basis(standard_plus_projector)
    if (trivial.shape[1], sign.shape[1], standard_plus.shape[1]) != (20, 4, 20):
        raise AssertionError(
            (trivial.shape[1], sign.shape[1], standard_plus.shape[1])
        )
    return [trivial, sign, standard_plus], [1, 1, 2]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--atlas", type=int, required=True)
    parser.add_argument("--p", type=float, required=True)
    parser.add_argument("--labels", type=int, default=2)
    parser.add_argument("--branches", type=int, default=2)
    parser.add_argument("--eps", type=float, default=1e-7)
    parser.add_argument("--solver", choices=("CLARABEL", "SCS"), default="SCS")
    parser.add_argument("--typed", action="store_true")
    parser.add_argument("--label-symmetric", action="store_true")
    args = parser.parse_args()

    target = nx.graph_atlas(args.atlas)
    if args.typed and args.labels != 2:
        raise ValueError("the prototype typed mode currently supports exactly two labels")
    basis = rooted_basis(args.labels, args.branches, include_label_edges=not args.typed)
    size = len(basis)
    type_names = ("plain", "edge", "nonedge") if args.typed else ("plain",)
    coefficient_matrices: dict[str, dict[int, np.ndarray]] = {
        name: defaultdict(lambda: np.zeros((size, size), dtype=float)) for name in type_names
    }

    for i, left in enumerate(basis):
        for j in range(i, size):
            product = rooted_product(left, basis[j], args.labels, args.branches)
            expansions: dict[str, list[tuple[float, nx.Graph]]] = {"plain": [(1.0, product)]}
            if args.typed:
                with_edge = product.copy()
                with_edge.add_edge(0, 1)
                expansions["edge"] = [(1.0, with_edge)]
                expansions["nonedge"] = [(1.0, product), (-1.0, with_edge)]
            for type_name, terms in expansions.items():
                for sign, term in terms:
                    core, edge_components = fixed_density_key(term)
                    coefficient = sign * args.p**edge_components
                    coefficient_matrices[type_name][core][i, j] += coefficient
                    if i != j:
                        coefficient_matrices[type_name][core][j, i] += coefficient

    if args.label_symmetric:
        transform = label_orbit_transform(basis, args.labels)
        coefficient_matrices = {
            name: {
                core: transform.T @ matrix @ transform
                for core, matrix in matrices.items()
            }
            for name, matrices in coefficient_matrices.items()
        }
        size = transform.shape[1]

    target_core, target_edges = fixed_density_key(target)
    rhs = defaultdict(float)
    rhs[target_core] += args.p**target_edges
    rhs[0] -= phi_value(target, args.p)

    all_cores = sorted(
        set(rhs).union(*(set(matrices) for matrices in coefficient_matrices.values()))
    )
    grams = {name: cp.Variable((size, size), symmetric=True) for name in type_names}
    constraints = [gram >> 0 for gram in grams.values()]
    for core in all_cores:
        constraints.append(
            sum(
                cp.sum(cp.multiply(coefficient_matrices[name][core], grams[name]))
                for name in type_names
            )
            == rhs[core]
        )
    problem = cp.Problem(cp.Minimize(sum(cp.trace(gram) for gram in grams.values())), constraints)
    if args.solver == "SCS":
        problem.solve(solver="SCS", eps=args.eps, max_iters=200_000)
    else:
        problem.solve(solver="CLARABEL", tol_gap_abs=args.eps, tol_feas=args.eps)

    print(f"status={problem.status} objective={problem.value} basis={size}")
    if any(gram.value is None for gram in grams.values()):
        return
    residuals = []
    for core in all_cores:
        residuals.append(
            abs(
                sum(
                    float(np.sum(coefficient_matrices[name][core] * grams[name].value))
                    for name in type_names
                )
                - rhs[core]
            )
        )
    print(f"max_residual={max(residuals):.6e}")
    for name in type_names:
        eigenvalues, eigenvectors = np.linalg.eigh(grams[name].value)
        print(
            f"type={name} min_eigenvalue={eigenvalues[0]:.6e} "
            f"rank_1e-7={sum(eigenvalues > 1e-7)}"
        )
        for index in np.argsort(eigenvalues)[-5:][::-1]:
            if eigenvalues[index] <= 1e-8:
                continue
            vector = eigenvectors[:, index]
            support = np.argsort(np.abs(vector))[-8:][::-1]
            print(
                "eig",
                f"{eigenvalues[index]:.8g}",
                [(int(item), float(vector[item])) for item in support if abs(vector[item]) > 1e-5],
            )


if __name__ == "__main__":
    main()
