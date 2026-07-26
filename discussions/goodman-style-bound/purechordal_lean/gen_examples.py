"""Generate Lean certificates + k-partite optimality theorems for all
non-clique pure chordal graphs on <= 6 vertices."""
import itertools, sys
import networkx as nx

def all_graphs(n):
    verts = list(range(n))
    edges = list(itertools.combinations(verts, 2))
    for k in range(len(edges) + 1):
        for es in itertools.combinations(edges, k):
            G = nx.Graph(); G.add_nodes_from(verts); G.add_edges_from(es)
            yield G

def is_pure_chordal(G):
    if not nx.is_chordal(G): return None
    cl = list(nx.find_cliques(G))
    if not cl: return None
    r = len(cl[0])
    if r < 3: return None
    if any(len(c) != r for c in cl): return None
    return r

def non_iso(graphs):
    uniq = []
    for G in graphs:
        if not any(nx.is_isomorphic(G, U) for U in uniq):
            uniq.append(G)
    return uniq

def clique_tree(cliques):
    """cliques: list of frozenset (all maximal, equal size). Return (ordered
    cliques, parent list) with parent[i] < i for i>0, parent[0]=0, satisfying
    index-order running intersection."""
    M = len(cliques)
    IG = nx.Graph(); IG.add_nodes_from(range(M))
    for a in range(M):
        for b in range(a + 1, M):
            IG.add_edge(a, b, weight=len(cliques[a] & cliques[b]))
    T = nx.maximum_spanning_tree(IG)
    bfs = nx.bfs_tree(T, 0)
    order = list(bfs.nodes())
    newidx = {old: i for i, old in enumerate(order)}
    parent_old = {}
    for old in order:
        preds = list(bfs.predecessors(old))
        parent_old[old] = preds[0] if preds else old
    ordered = [cliques[order[i]] for i in range(M)]
    parent = [newidx[parent_old[order[i]]] for i in range(M)]
    # verify (root i=0 is exempt: its separator is empty by definition)
    for i in range(1, M):
        earlier = set().union(*[ordered[j] for j in range(i)])
        assert (ordered[i] & earlier) == (ordered[i] & ordered[parent[i]]), \
            f"running intersection fails at {i}"
        assert parent[i] < i
    assert parent[0] == 0
    return ordered, parent

def finset(s):
    return "{" + ", ".join(str(x) for x in sorted(s)) + "}"

def match_body(indent, values):
    lines = []
    for i, v in enumerate(values):
        pat = "_" if i == len(values) - 1 else str(i)
        lines.append(f"{indent}| {pat} => {v}")
    return "\n".join(lines)

def gen_graph(name, n, r, ordered, parent):
    M = len(ordered)
    bag_vals = [finset(c) for c in ordered]
    par_vals = [str(p) for p in parent]
    out = []
    out.append(f"namespace PureChordal.Examples.{name}")
    out.append("")
    out.append(f"/-- Bags (maximal `K{r}` cliques) of a pure chordal graph on"
               f" {n} vertices. -/")
    out.append(f"def bags : Fin {M} → Finset (Fin {n})")
    out.append(f"  | i => match i.1 with")
    out.append(match_body("    ", bag_vals))
    out.append("")
    out.append(f"/-- The graph, presented as the union of its {M} maximal"
               f" cliques. -/")
    out.append(f"def graph : SimpleGraph (Fin {n}) :=")
    out.append(f"  SimpleGraph.fromRel fun u v =>")
    out.append(f"    ∃ i : Fin {M}, u ∈ bags i ∧ v ∈ bags i")
    out.append("")
    out.append(f"noncomputable instance : DecidableRel graph.Adj :=")
    out.append(f"  Classical.decRel _")
    out.append("")
    out.append(f"/-- Parent indices of a rooted clique tree. -/")
    out.append(f"def parent : Fin {M} → Fin {M}")
    out.append(f"  | i => match i.1 with")
    out.append(match_body("    ", par_vals))
    out.append("")
    out.append(f"/-- The pure clique-tree certificate. -/")
    out.append(f"def decomp : PureCliqueTreeDecomp graph {r} {M} where")
    out.append(f"  root := 0")
    out.append(f"  root_val := by decide")
    out.append(f"  parent := parent")
    out.append(f"  parent_lt := by decide")
    out.append(f"  parent_root := by decide")
    out.append(f"  bag := bags")
    out.append(f"  bag_card := by decide")
    out.append(f"  bag_clique := by")
    out.append(f"    intro i")
    out.append(f"    rw [SimpleGraph.isClique_iff]")
    out.append(f"    intro u hu v hv huv")
    out.append(f"    rw [graph, SimpleGraph.fromRel_adj]")
    out.append(f"    exact ⟨huv, Or.inl ⟨i, hu, hv⟩⟩")
    out.append(f"  bag_injective := by decide")
    out.append(f"  vertex_cover := by decide")
    out.append(f"  edge_cover := by")
    out.append(f"    intro u v huv")
    out.append(f"    rw [graph, SimpleGraph.fromRel_adj] at huv")
    out.append(f"    rcases huv with ⟨hne, h | h⟩")
    out.append(f"    · exact h")
    out.append(f"    · rcases h with ⟨i, hv, hu⟩")
    out.append(f"      exact ⟨i, hu, hv⟩")
    out.append(f"  old_eq_parentSeparator := by decide")
    out.append("")
    out.append(f"/-- `k`-partite optimality: at edge density `1 - 1/k` with"
               f" `{r} ≤ k`, the balanced")
    out.append(f"complete `k`-partite graphon minimizes this graph's"
               f" homomorphism density. -/")
    out.append(f"theorem optimality")
    out.append(f"    {{Ω : Type*}} [MeasurableSpace Ω]"
               f" {{μ : MeasureTheory.Measure Ω}}")
    out.append(f"    [MeasureTheory.IsProbabilityMeasure μ]")
    out.append(f"    (W : Graphon Ω μ) (k : ℕ) [NeZero k] (hrk : {r} ≤ k)")
    out.append(f"    (hp : cliqueDensity 2 W = 1 - 1 / (k : ℝ)) :")
    out.append(f"    homDensity graph (balancedMultipartiteGraphon k) ≤"
               f" homDensity graph W :=")
    out.append(f"  decomp.balancedMultipartite_minimal k W (by norm_num) hrk hp")
    out.append("")
    out.append(f"end PureChordal.Examples.{name}")
    return "\n".join(out)

def main():
    groups = {}
    for n in range(4, 7):
        uniq = non_iso([G for G in all_graphs(n) if is_pure_chordal(G)])
        items = []
        for G in uniq:
            r = is_pure_chordal(G)
            cliques = [frozenset(c) for c in nx.find_cliques(G)]
            if len(cliques) < 2:   # skip cliques (single maximal clique)
                continue
            ordered, parent = clique_tree(cliques)
            items.append((n, r, ordered, parent))
        groups[n] = items
    total = sum(len(v) for v in groups.values())
    print(f"# non-clique pure chordal graphs: "
          f"n4={len(groups[4])} n5={len(groups[5])} n6={len(groups[6])} "
          f"total={total}", file=sys.stderr)

    outdir = sys.argv[1]
    for n, items in groups.items():
        blocks = []
        for idx, (nn, r, ordered, parent) in enumerate(items, 1):
            name = f"G{n}_{idx}"
            blocks.append(gen_graph(name, nn, r, ordered, parent))
        header = ("import PureChordal.ChromaticFactorization\n\n"
                  "/-!\n"
                  f"# Pure chordal graphs on {n} vertices\n\n"
                  "Auto-generated certificates and `k`-partite optimality\n"
                  "theorems for the non-clique pure chordal graphs on "
                  f"{n} vertices.\n-/\n\n")
        content = header + "\n".join(blocks) + "\n"
        path = f"{outdir}/N{n}.lean"
        open(path, "w", encoding="utf-8", newline="\n").write(content)
        print(f"wrote {path} ({len(items)} graphs)", file=sys.stderr)

if __name__ == "__main__":
    main()
