"""Add finite graph-classification witnesses used by the Lean checker.

The mathematical certificate remains unchanged.  These extra fields record,
for each of the 64 x 64 glued flag products, its fixed-density Atlas core and
an explicit five-vertex relabelling to the Atlas representative padded with
isolated vertices.  Lean independently checks every witness.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import networkx as nx

from rooted_sos_search import ATLAS, fixed_density_key, rooted_basis, rooted_product


def adjacency_code(graph: nx.Graph, order: int = 5) -> list[list[bool]]:
    return [[graph.has_edge(i, j) for j in range(order)] for i in range(order)]


def lean_fixed_core(graph: nx.Graph) -> nx.Graph:
    """Replicate `fixedCoreGraphFin5`'s deterministic labelled core."""
    isolated_edges = sorted(
        (min(component), max(component))
        for component in nx.connected_components(graph)
        if len(component) == 2 and graph.subgraph(component).number_of_edges() == 1
    )
    isolated_vertices = [vertex for edge in isolated_edges for vertex in edge]
    order = [vertex for vertex in range(5) if vertex not in isolated_vertices]
    order.extend(isolated_vertices)
    inverse = {old: new for new, old in enumerate(order)}
    result = nx.relabel_nodes(graph, inverse, copy=True)
    if len(isolated_edges) >= 1:
        result.remove_edge(3, 4)
    if len(isolated_edges) >= 2:
        result.remove_edge(1, 2)
    result.add_nodes_from(range(5))
    return result


def padded_atlas_graph(atlas_index: int) -> nx.Graph:
    graph = nx.convert_node_labels_to_integers(ATLAS[atlas_index])
    graph.add_nodes_from(range(5))
    return graph


def relabelling_witness(source: nx.Graph, target: nx.Graph) -> list[int]:
    """Return old source vertices read in target's vertex order."""
    matcher = nx.algorithms.isomorphism.GraphMatcher(target, source)
    mapping = next(matcher.isomorphisms_iter())
    return [int(mapping[index]) for index in range(5)]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "certificate", nargs="?", default="experiments/house_atlas43_rational.json"
    )
    parser.add_argument(
        "--output", default="experiments/house_atlas43_lean_classification.json"
    )
    args = parser.parse_args()
    path = Path(args.certificate)
    certificate = json.loads(path.read_text(encoding="utf-8"))
    if certificate.get("atlas") != 43:
        raise AssertionError("wrong certificate")

    basis = rooted_basis(3, 1)
    core_ids: list[list[int]] = []
    core_permutations: list[list[list[int]]] = []
    used_ids: set[int] = {0, 43}
    for left in basis:
        id_row: list[int] = []
        permutation_row: list[list[int]] = []
        for right in basis:
            product = rooted_product(left, right, 3, 1)
            core_id, _ = fixed_density_key(product)
            source = lean_fixed_core(product)
            target = padded_atlas_graph(core_id)
            id_row.append(core_id)
            permutation_row.append(relabelling_witness(source, target))
            used_ids.add(core_id)
        core_ids.append(id_row)
        core_permutations.append(permutation_row)

    atlas_codes = [adjacency_code(padded_atlas_graph(index)) for index in range(53)]
    house = nx.Graph()
    house.add_nodes_from(range(5))
    house.add_edges_from([(0, 1), (0, 3), (0, 4), (1, 2), (2, 3), (3, 4)])
    house_permutation = relabelling_witness(house, padded_atlas_graph(43))

    classification = {
        "core_ids": core_ids,
        "core_permutations": core_permutations,
        "atlas_codes": atlas_codes,
        "house_permutation": house_permutation,
    }
    output = Path(args.output)
    output.write_text(json.dumps(classification, separators=(",", ":")), encoding="utf-8")
    print(
        f"wrote {output}: used_core_ids={sorted(used_ids)} "
        f"bytes={output.stat().st_size}"
    )


if __name__ == "__main__":
    main()
