"""Untrusted compact witnesses for induced six-vertex certificate checking.

Every labelled six-vertex graph receives an explicit vertex-permutation witness.
Flag products are counted by filling their unspecified cross edges, independently
of verify_remaining_cases_induced.py's ordered samples of each host graph.
No row-specific certificate numbers are stored in this common witness.
"""

from collections import Counter
import itertools as it
import json
from pathlib import Path

import networkx as nx

from verify_remaining_cases_induced import flag_definition


def main():
    atlas = nx.graph_atlas_g()
    hosts = [g for g in atlas if len(g) == 6]
    edges = list(it.combinations(range(6), 2))
    edge_index = {e: k for k, e in enumerate(edges)}
    permutations = list(it.permutations(range(6)))
    permutation_index = {p: k for k, p in enumerate(permutations)}
    inverses = [tuple(p.index(i) for i in range(6)) for p in permutations]
    edge_permutations = [
        [edge_index[tuple(sorted((p[i], p[j])))] for i, j in edges]
        for p in permutations
    ]
    codes = [sum(1 << edge_index[tuple(sorted(e))] for e in g.edges()) for g in hosts]
    classification = [None] * (1 << 15)
    for j, g in enumerate(hosts):
        for pi, p in enumerate(permutations):
            mask = sum(1 << edge_index[tuple(sorted((p[i], p[k])))] for i, k in g.edges())
            if classification[mask] is None:
                # The stored permutation carries the labelled graph TO the host.
                classification[mask] = [j, permutation_index[inverses[pi]]]
            else:
                assert classification[mask][0] == j
    assert all(row is not None for row in classification)
    for mask, (j, pi) in enumerate(classification):
        assert all(((mask >> k) & 1) == ((codes[j] >> edge_permutations[pi][k]) & 1)
                   for k in range(15))
    orbits = [0] * 156
    for j, _ in classification:
        orbits[j] += 1
    assert sum(orbits) == 32768
    # This also accommodates the empty-graph expansion, with all 2^15 patterns.
    # Individual flag-pair columns use at most 3*3*512 = 4608 completions.
    bound = 32768
    base = 2*bound+1

    def encode(counter):
        assert all(0 <= v < base for v in counter.values())
        assert sum(counter.values()) <= bound
        return str(sum(v * base ** j for j, v in counter.items()))

    types = []
    completion_count = 0
    for m in (0, 2, 4):
        r = (6-m)//2
        branch_edges, lut, nf = flag_definition(m, r)
        first = [edge_index[e] for e in branch_edges]
        second = [edge_index[(i if i < m else i+r, j+r)] for i, j in branch_edges]
        cross = [edge_index[(i, j)] for i in range(m, m+r) for j in range(m+r, 6)]
        root_edges = list(it.combinations(range(m), 2))
        assert sorted([edge_index[e] for e in root_edges]+first+second+cross) == list(range(15))

        def placements(indices):
            return [sum(1 << target for k, target in enumerate(indices) if mask >> k & 1)
                    for mask in range(1 << len(indices))]

        first_codes, second_codes, cross_codes = map(placements, (first, second, cross))
        for typ in (g for g in atlas if len(g) == m):
            root = sum(1 << edge_index[tuple(sorted(e))] for e in typ.edges())
            counts = [[Counter() for _ in range(nf)] for _ in range(nf)]
            raw_counts = []
            for a, first_code in enumerate(first_codes):
                raw_row = []
                for b, second_code in enumerate(second_codes):
                    counter = Counter(classification[root | first_code | second_code | c][0]
                                      for c in cross_codes)
                    counts[lut[a]][lut[b]].update(counter)
                    raw_row.append(encode(counter))
                    completion_count += len(cross_codes)
                raw_counts.append(raw_row)
            assert sum(sum(counter.values()) for row in counts for counter in row) == (
                len(first_codes) * len(second_codes) * len(cross_codes))
            types.append(dict(roots=m, branches=r, root_code=root,
                              branch_pairs=branch_edges, first_indices=first,
                              second_indices=second, cross_indices=cross,
                              flag_lookup=lut, flag_count=nf,
                              members=[[a for a, i in enumerate(lut) if i == j] for j in range(nf)],
                              first_codes=first_codes, second_codes=second_codes,
                              cross_codes=cross_codes, raw_encoded_counts=raw_counts,
                              encoded_counts=[[encode(c) for c in row] for row in counts]))
    assert completion_count == 71168

    def hom_counts(required):
        c = Counter(classification[mask][0] for mask in range(32768)
                    if mask & required == required)
        return [c[j] for j in range(156)]

    four = [g for g in atlas if len(g) == 4]
    four_codes = [sum(1 << edge_index[tuple(sorted(e))] for e in g.edges()) for g in four]
    result = dict(format='induced-six-common-completions-v1', pairs=edges,
                  graph6=[nx.to_graph6_bytes(g, header=False).strip().decode() for g in hosts],
                  host_codes=codes, orbit_sizes=orbits, permutations=permutations,
                  inverse_indices=[permutation_index[p] for p in inverses],
                  edge_permutations=edge_permutations, classification=classification,
                  histogram_base=base, histogram_bound=bound,
                  completion_count=completion_count, types=types,
                  four_codes=four_codes, four_hom_counts=[hom_counts(c) for c in four_codes],
                  four_edge_hom_counts=[hom_counts(c | (1 << edge_index[(4, 5)])) for c in four_codes])
    path = Path('experiments/induced_six_common.json')
    path.write_text(json.dumps(result, separators=(',', ':'))+'\n', encoding='utf-8')
    print(f'Wrote {path}: {path.stat().st_size} bytes; 32768 classification witnesses; '
          f'{completion_count} completions; {len(types)} root types; histogram base {base}', flush=True)


if __name__ == '__main__':
    main()
