"""Export bounded six-vertex classification witnesses for the S4 flag basis.

For every ordered pair of the 352 raw flags, the witness records:

* the row of the 143 fixed-density graph groups; and
* an explicit permutation from the standard ``core ⊔ m K₂`` labelling to
  the six vertices of the glued flag graph.

Lean checks every permutation and adjacency matrix.  The Graph Atlas lookup
performed here is therefore an untrusted witness generator, not part of the
trusted proof.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import networkx as nx

from full_s4_rooted_sos import LABEL_EDGES
from rooted_sos_search import fixed_density_key


MAX_BYTES = 32_000
PAIR_GROUP_BASE = 143
PAIR_PERMUTATION_BASE = 6
PAIR_CELL_BASE = 10_000_000


def compact_json(value: object) -> str:
    return json.dumps(value, separators=(",", ":")) + "\n"


def write_if_changed(path: Path, contents: str) -> None:
    if path.exists() and path.read_text(encoding="utf-8") == contents:
        return
    path.write_text(contents, encoding="utf-8")


def adjacency_code(graph: nx.Graph, order: int) -> list[list[bool]]:
    return [
        [graph.has_edge(i, j) for j in range(order)]
        for i in range(order)
    ]


def padded_atlas_graph(core: int, order: int) -> nx.Graph:
    atlas_graph = nx.convert_node_labels_to_integers(nx.graph_atlas(core))
    if atlas_graph.number_of_nodes() > order:
        raise AssertionError((core, atlas_graph.number_of_nodes(), order))
    result = nx.Graph()
    result.add_nodes_from(range(order))
    result.add_edges_from(atlas_graph.edges())
    return result


def standard_graph(core: int, isolated: int) -> nx.Graph:
    if not 0 <= isolated <= 3:
        raise AssertionError((core, isolated))
    core_order = 6 - 2 * isolated
    result = padded_atlas_graph(core, core_order)
    result.add_nodes_from(range(6))
    for component in range(isolated):
        left = core_order + 2 * component
        result.add_edge(left, left + 1)
    return result


def glued_graph(left_index: int, right_index: int) -> nx.Graph:
    left_label, left_branch = divmod(left_index, 16)
    right_label, right_branch = divmod(right_index, 16)
    label_union = left_label | right_label
    return graph_from_masks(
        left_label | right_label, left_branch, right_branch
    )


def graph_from_masks(label_union: int, left_branch: int, right_branch: int) -> nx.Graph:
    graph = nx.Graph()
    graph.add_nodes_from(range(6))
    graph.add_edges_from(
        edge for bit, edge in enumerate(LABEL_EDGES)
        if label_union & (1 << bit)
    )
    graph.add_edges_from(
        (root, 4) for root in range(4) if left_branch & (1 << root)
    )
    graph.add_edges_from(
        (root, 5) for root in range(4) if right_branch & (1 << root)
    )
    return graph


def relabelling_witness(source: nx.Graph, target: nx.Graph) -> list[int]:
    """Old source vertices in the target vertex order."""
    matcher = nx.algorithms.isomorphism.GraphMatcher(target, source)
    candidates = (
        tuple(int(mapping[i]) for i in range(6))
        for mapping in matcher.isomorphisms_iter()
    )
    try:
        return list(min(candidates))
    except ValueError as error:
        raise AssertionError(
            (sorted(source.edges()), sorted(target.edges()))
        ) from error


def encode_pair_cell(witness: list[int]) -> int:
    row, *permutation = witness
    if len(permutation) != 6:
        raise AssertionError(witness)
    value = row
    place = PAIR_GROUP_BASE
    for vertex in permutation:
        value += place * vertex
        place *= PAIR_PERMUTATION_BASE
    if not 0 <= value < PAIR_CELL_BASE:
        raise AssertionError((value, witness))
    return value


def encode_pair_row(witnesses: list[list[int]]) -> int:
    return sum(
        encode_pair_cell(witness) * PAIR_CELL_BASE**column
        for column, witness in enumerate(witnesses)
    )


def encode_group_row(witnesses: list[list[int]]) -> int:
    return sum(
        witness[0] * PAIR_GROUP_BASE**column
        for column, witness in enumerate(witnesses)
    )


def write_chunks(
    output: Path,
    label: str,
    rows: list[object],
    max_bytes: int = MAX_BYTES,
) -> list[dict[str, object]]:
    descriptors: list[dict[str, object]] = []
    start = 0
    while start < len(rows):
        stop = start + 1
        while stop < len(rows):
            candidate = compact_json({"start": start, "data": rows[start : stop + 1]})
            if len(candidate.encode("utf-8")) > max_bytes:
                break
            stop += 1
        contents = compact_json({"start": start, "data": rows[start:stop]})
        path = output.with_name(
            f"{output.stem}_{label}_{start:03d}_{stop - 1:03d}{output.suffix}"
        )
        write_if_changed(path, contents)
        descriptors.append({
            "file": path.name,
            "start": start,
            "stop": stop,
            "bytes": path.stat().st_size,
        })
        start = stop
    return descriptors


def group_chunk_payload(start: int, rows: list[dict[str, object]]) -> dict[str, object]:
    return {
        "start": start,
        "keys": [[row["core"], row["isolated"]] for row in rows],
        "core6": [row["core6"] for row in rows],
        "core4": [row["core4"] for row in rows],
        "core2": [row["core2"] for row in rows],
        "standard": [row["standard"] for row in rows],
    }


def write_group_chunks(
    output: Path,
    rows: list[dict[str, object]],
    max_bytes: int = MAX_BYTES,
) -> list[dict[str, object]]:
    descriptors: list[dict[str, object]] = []
    start = 0
    while start < len(rows):
        stop = start + 1
        while stop < len(rows):
            candidate = compact_json(group_chunk_payload(start, rows[start : stop + 1]))
            if len(candidate.encode("utf-8")) > max_bytes:
                break
            stop += 1
        contents = compact_json(group_chunk_payload(start, rows[start:stop]))
        path = output.with_name(
            f"{output.stem}_groups_{start:03d}_{stop - 1:03d}{output.suffix}"
        )
        write_if_changed(path, contents)
        descriptors.append({
            "file": path.name,
            "start": start,
            "stop": stop,
            "bytes": path.stat().st_size,
        })
        start = stop
    return descriptors


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--common", default="experiments/s4_lean_common.json"
    )
    parser.add_argument(
        "--output", default="experiments/s4_lean_classification_manifest.json"
    )
    args = parser.parse_args()

    common_path = Path(args.common)
    common = json.loads(common_path.read_text(encoding="utf-8"))
    basis_indices = list(map(int, common["basis_indices"]))
    group_keys = [tuple(map(int, key)) for key in common["raw_group_keys"]]
    if len(basis_indices) != 352 or len(group_keys) != 143:
        raise AssertionError((len(basis_indices), len(group_keys)))
    group_index = {key: row for row, key in enumerate(group_keys)}

    group_rows: list[dict[str, object]] = []
    standards: list[nx.Graph] = []
    for row, (core, isolated) in enumerate(group_keys):
        small_order = 6 - 2 * isolated
        standard = standard_graph(core, isolated)
        standards.append(standard)
        group_rows.append({
            "row": row,
            "core": core,
            "isolated": isolated,
            "core6": adjacency_code(padded_atlas_graph(core, 6), 6),
            "core4": adjacency_code(
                padded_atlas_graph(core, 4) if small_order <= 4 else nx.empty_graph(4),
                4,
            ),
            "core2": adjacency_code(
                padded_atlas_graph(core, 2) if small_order <= 2 else nx.empty_graph(2),
                2,
            ),
            "standard": adjacency_code(standard, 6),
        })

    label_masks = [index // 16 for index in basis_indices]
    label_unions = sorted({left | right for left in label_masks for right in label_masks})
    if len(label_unions) != 57:
        raise AssertionError(len(label_unions))
    union_index = [0] * 64
    for row, mask in enumerate(label_unions):
        union_index[mask] = row

    lookup_rows: list[int] = []
    group_lookup_rows: list[int] = []
    decoded_group_lookup_rows: list[list[list[int]]] = []
    for label_union in label_unions:
        row_witnesses: list[list[int]] = []
        for left_branch in range(16):
            for right_branch in range(16):
                graph = graph_from_masks(label_union, left_branch, right_branch)
                key = fixed_density_key(graph)
                row = group_index[key]
                row_witnesses.append(
                    [row, *relabelling_witness(graph, standards[row])]
                )
        lookup_rows.append(encode_pair_row(row_witnesses))
        group_lookup_rows.append(encode_group_row(row_witnesses))
        decoded_group_lookup_rows.append([
            [row_witnesses[16 * left + right][0] for right in range(16)]
            for left in range(16)
        ])

    output = Path(args.output)
    group_chunks = write_group_chunks(output, group_rows)
    lookup_chunks = write_chunks(output, "lookups", lookup_rows)
    group_lookup_chunks = write_chunks(output, "lookup_groups", group_lookup_rows)
    decoded_group_lookup_chunks = write_chunks(
        output, "lookup_group_arrays", decoded_group_lookup_rows
    )
    manifest = {
        "source": common_path.name,
        "basis_size": len(basis_indices),
        "group_count": len(group_keys),
        "max_bytes": MAX_BYTES,
        "pair_group_base": PAIR_GROUP_BASE,
        "pair_permutation_base": PAIR_PERMUTATION_BASE,
        "pair_cell_base": PAIR_CELL_BASE,
        "label_unions": label_unions,
        "union_index": union_index,
        "group_chunks": group_chunks,
        "lookup_chunks": lookup_chunks,
        "group_lookup_chunks": group_lookup_chunks,
        "decoded_group_lookup_chunks": decoded_group_lookup_chunks,
    }
    write_if_changed(output, compact_json(manifest))
    sizes = [int(item["bytes"]) for item in
             group_chunks + lookup_chunks + group_lookup_chunks
             + decoded_group_lookup_chunks]
    print(
        f"wrote {output}: groups={len(group_rows)} lookups={len(label_unions) * 256} "
        f"leaves={len(sizes)} max_bytes={max(sizes)}"
    )


if __name__ == "__main__":
    main()
