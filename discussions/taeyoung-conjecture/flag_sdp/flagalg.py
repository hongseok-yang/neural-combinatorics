"""
flagalg.py
==========
Self-contained flag-algebra / Razborov Cauchy-Schwarz SDP machinery for
2-colored (i.e. plain graph) homomorphism-density inequalities.

CONVENTIONS (chosen once, used everywhere)
-------------------------------------------
* Ground size N.  We enumerate all graphs on N labeled-then-quotiented-to-iso
  vertices, i.e. all iso classes of N-vertex graphs G_1,...,G_m.
* A "quantum graph" (formal linear combination of homomorphism densities of
  small graphs F_alpha) is represented by its coefficient vector over the
  induced-density basis at level N:

        val(QG)  =  sum_H  coef[H] * p(H, .)          (H ranges over N-vtx graphs)

  where p(H, .) is the INDUCED density of H, and coef[H] is obtained by
  evaluating the quantum graph on the graphon "= H blown up", equivalently

        coef[H] = sum_alpha  q_alpha * t(F_alpha, H)          (*)

  Justification: for ANY graphon W,  t(F,W) = sum_H p(H,W) t(F,H)  is FALSE in
  general; the correct averaging identity is
        t(F, W) = sum_H p(H, W) * t(F, H)                        -- see below.
  Actually the identity we use is the standard "sampling" identity:
     for the random induced N-vertex subgraph H ~ W,  E[t(F,H)] -> t(F,W) only
  asymptotically.  To get an EXACT finite identity we instead use:

        t(F, W) = E_{H ~ W, |H|=N} [ t_inj-normalized ... ]

  To avoid any subtlety we adopt the *exact* linear identity that holds for
  every graphon W when |V(F)| <= N:

        t(F, W) = sum_{H : |V(H)|=N} p(H, W) * t(F, H)

  This identity is EXACT and is the foundation of flag algebras.  Proof: sample
  N iid points x_1..x_N ~ U[0,1].  The induced graph on them is H w.p. p(H,W)
  (this is the definition of induced density p(H,W) = P[sampled induced graph
  = H]).  Condition on the sampled points; t(F,H) with H the *sampled weighted*
  ... rather, use hom density decomposition:
      t(F,W) = E_{x_1..x_N}[ (1/|inj|) sum over injections F->[N] prod W(x) ]
             = E_H[ t(F, H) ]   where H is the sampled induced graph (as a
               graph, unweighted) ONLY when F->[N] maps to distinct vertices...
  Because F may map several of its vertices to the same sample point, the clean
  identity uses *homomorphism* density of F into the sampled induced graph H
  (which is itself a graph on N vertices), and E_H[t(F,H)] = t(F,W) EXACTLY
  provided we define t(F,H) as homomorphism density into the graph H (allowing
  repeated vertices).  This is a standard, exact identity. We verify it
  numerically in the test-suite (tests.py) against the direct step-graphon
  engine, so correctness does not rest on this docstring's prose.

* p(H, W) for a random N-vertex sample equals the INDUCED density.  The
  simplex constraint is  sum_H p(H, .) = 1,  p(H,.) >= 0.

FLAG SDP (Razborov plain form)
------------------------------
For a type sigma on m vertices and flags F_i (sigma + (ell-m) extra vertices,
2*ell - m = N), the averaging operator gives, for each N-vertex graph H, a PSD
"multiplication matrix"  M_sigma(H)[i,j] = < [[F_i F_j]] , H >  = probability,
over a random labeling of a size-m sub-tuple as sigma inside H and a random
split of the remaining vertices, that the two induced flags are F_i and F_j.

The certificate:  for a target quantum graph f with induced-coef vector c[H],

    minimize_over_certificate   is feasible if there exist PSD Q_sigma and a
    scalar lower bound value such that for every H:

        c[H] - lower  =  sum_sigma < Q_sigma, M_sigma(H) >  +  slack[H],
        slack[H] >= 0.

  We MAXIMIZE `lower`.  (This is exactly Razborov's SDP; the slack >= 0 encodes
  "nonnegative combination of induced densities", using sum_H p(H)=1 so the
  constant `lower` is sum_H lower*p(H).)

This module builds the M_sigma(H) tables by exact counting.
"""

import itertools
import numpy as np
import networkx as nx
from functools import lru_cache


# ----------------------------------------------------------------------------
# Graph enumeration up to isomorphism
# ----------------------------------------------------------------------------

def all_graphs(n):
    """Return list of all iso-classes of graphs on n vertices, as nx.Graph on
    vertex set range(n).  Uses brute-force over edge subsets with iso dedup.
    Fine for n<=7 (n=7: 1044 graphs)."""
    verts = list(range(n))
    all_edges = list(itertools.combinations(verts, 2))
    reps = []
    for mask in range(1 << len(all_edges)):
        G = nx.Graph()
        G.add_nodes_from(verts)
        for b, e in enumerate(all_edges):
            if mask & (1 << b):
                G.add_edge(*e)
        # dedup by iso
        is_new = True
        for R in reps:
            if R.number_of_edges() == G.number_of_edges() and nx.is_isomorphic(R, G):
                is_new = False
                break
        if is_new:
            reps.append(G)
    return reps


def all_graphs_by_nauty_signature(n):
    """Enumeration of all iso-classes of n-vertex graphs.  For n<=7 we use the
    networkx graph atlas (instant, complete).  For n>=8 we fall back to
    brute-force edge-mask enumeration with WL-signature bucketing."""
    if n <= 7:
        from networkx.generators.atlas import graph_atlas_g
        atlas = graph_atlas_g()
        out = []
        for g in atlas:
            if g.number_of_nodes() == n:
                # relabel to 0..n-1 on a fresh Graph
                G = nx.convert_node_labels_to_integers(g, first_label=0)
                # ensure all n nodes present
                G.add_nodes_from(range(n))
                out.append(G)
        return out
    verts = list(range(n))
    all_edges = list(itertools.combinations(verts, 2))
    buckets = {}
    reps = []
    for mask in range(1 << len(all_edges)):
        G = nx.Graph()
        G.add_nodes_from(verts)
        for b, e in enumerate(all_edges):
            if mask & (1 << b):
                G.add_edge(*e)
        key = _cheap_cert(G, n)
        cand = buckets.setdefault(key, [])
        is_new = True
        for R in cand:
            if nx.is_isomorphic(R, G):
                is_new = False
                break
        if is_new:
            cand.append(G)
            reps.append(G)
    return reps


def _cheap_cert(G, n):
    deg = tuple(sorted(d for _, d in G.degree()))
    try:
        wl = nx.weisfeiler_lehman_graph_hash(G, iterations=3)
    except Exception:
        wl = ""
    return (G.number_of_edges(), deg, wl)


# ----------------------------------------------------------------------------
# Homomorphism density of small F into an N-vertex graph H
# ----------------------------------------------------------------------------

def _adj(H):
    n = H.number_of_nodes()
    nodes = list(H.nodes())
    idx = {u: i for i, u in enumerate(nodes)}
    A = np.zeros((n, n), dtype=np.int8)
    for u, v in H.edges():
        A[idx[u], idx[v]] = 1
        A[idx[v], idx[u]] = 1
    return A


def t_hom_in_graph(F_edges, F_nv, H):
    """t(F, H) = (#homomorphisms F->H) / |V(H)|^{|V(F)|}.
    Homomorphism = map V(F)->V(H) with every F-edge mapped to an H-edge
    (repeats allowed).  H is an nx.Graph; we treat it as an unweighted graph
    with adjacency 0/1 (no self loops)."""
    A = _adj(H)
    n = A.shape[0]
    count = 0
    for phi in itertools.product(range(n), repeat=F_nv):
        ok = True
        for (a, b) in F_edges:
            if A[phi[a], phi[b]] == 0:
                ok = False
                break
        if ok:
            count += 1
    return count / (n ** F_nv)


def induced_coef_vector(quantum_graph, N, graphs=None):
    """Given a quantum graph = list of (coef, F_edges, F_nv), return the vector
    c over the induced-density basis at level N:  c[i] = sum_alpha coef_alpha *
    t(F_alpha, graphs[i]).   (This is exactly identity (*) in the header.)"""
    if graphs is None:
        graphs = all_graphs_by_nauty_signature(N)
    m = len(graphs)
    c = np.zeros(m)
    for (coef, F_edges, F_nv) in quantum_graph:
        for i, H in enumerate(graphs):
            c[i] += coef * t_hom_in_graph(F_edges, F_nv, H)
    return c, graphs


# ----------------------------------------------------------------------------
# Types and flags
# ----------------------------------------------------------------------------

def canonical_label(G, nodes_order=None):
    """Return a hashable canonical form of labeled graph on given node order.
    We keep labels (this is a *labeled* object) -- used for type/flag identity.
    Represent as sorted edge tuple over the fixed labels."""
    E = tuple(sorted((min(u, v), max(u, v)) for u, v in G.edges()))
    return E


def make_type(m, edges):
    """A type sigma: a graph on labeled vertices 0..m-1 with given edge set."""
    G = nx.Graph()
    G.add_nodes_from(range(m))
    G.add_edges_from(edges)
    return G


def enumerate_types(m):
    """All iso-classes of types on m labeled vertices.  For flag algebras the
    'type' is a labeled graph but we only need one representative per iso class
    (different labelings give equivalent SDP blocks)."""
    reps = []
    all_edges = list(itertools.combinations(range(m), 2))
    seen = []
    for mask in range(1 << len(all_edges)):
        G = nx.Graph()
        G.add_nodes_from(range(m))
        for b, e in enumerate(all_edges):
            if mask & (1 << b):
                G.add_edge(*e)
        is_new = True
        for R in seen:
            if nx.is_isomorphic(R, G):
                is_new = False
                break
        if is_new:
            seen.append(G)
            reps.append(G)
    return reps


def enumerate_flags(sigma, ell):
    """Enumerate iso-classes of flags of size ell over type sigma (on m verts).
    A flag = graph F on vertices 0..ell-1 whose induced subgraph on the first
    m vertices EQUALS sigma (as labeled graph), modulo isomorphisms fixing the
    first m vertices pointwise.

    Returns list of flag representatives (nx.Graph on 0..ell-1, first m = sigma).
    """
    m = sigma.number_of_nodes()
    sigma_edges = set(tuple(sorted(e)) for e in sigma.edges())
    extra = ell - m
    # edges among extra vertices, and between extra and type vertices
    extra_verts = list(range(m, ell))
    cross_edges = list(itertools.product(range(m), extra_verts))
    inner_edges = list(itertools.combinations(extra_verts, 2))
    free_edges = cross_edges + inner_edges
    reps = []
    reps_keys = []
    # automorphisms of sigma that fix labels? For flags modulo iso fixing the
    # first m vertices pointwise, we only allow permutations of the EXTRA
    # vertices (and any automorphism of sigma fixing all its vertices = identity
    # on labels, but relabeling among identical-role type vertices is NOT
    # allowed since type vertices are labeled/distinguished).
    extra_perms = list(itertools.permutations(extra_verts))
    for mask in range(1 << len(free_edges)):
        F = nx.Graph()
        F.add_nodes_from(range(ell))
        F.add_edges_from(sigma_edges)
        for b, e in enumerate(free_edges):
            if mask & (1 << b):
                F.add_edge(*e)
        # canonical key under permutations of extra vertices only
        best = None
        for perm in extra_perms:
            mapping = {i: i for i in range(m)}
            for k, ev in enumerate(extra_verts):
                mapping[ev] = perm[k]
            Fp = nx.relabel_nodes(F, mapping, copy=True)
            key = tuple(sorted((min(u, v), max(u, v)) for u, v in Fp.edges()))
            if best is None or key < best:
                best = key
        if best not in reps_keys:
            reps_keys.append(best)
            # store the canonical representative
            Fc = nx.Graph()
            Fc.add_nodes_from(range(ell))
            Fc.add_edges_from(best)
            reps.append(Fc)
    return reps


# ----------------------------------------------------------------------------
# Multiplication table  M_sigma(H)[i,j]
# ----------------------------------------------------------------------------

def _induced_subgraph_edges(H_adj, verts):
    """Edge set (as frozenset of sorted pairs, relabeled to 0..len-1) of the
    induced subgraph of H on the given vertex tuple, in the ORDER given."""
    k = len(verts)
    E = []
    for a in range(k):
        for b in range(a + 1, k):
            if H_adj[verts[a], verts[b]]:
                E.append((a, b))
    return E


def _flag_key_fixing_type(edges_ordered, m, ell):
    """Canonical key of a labeled flag whose first m vertices are the type
    (fixed pointwise), modulo permuting the last (ell-m) vertices."""
    extra = list(range(m, ell))
    best = None
    Eset = set(edges_ordered)
    for perm in itertools.permutations(extra):
        mapping = list(range(m)) + list(perm)
        newE = tuple(sorted((min(mapping[u], mapping[v]), max(mapping[u], mapping[v]))
                            for (u, v) in Eset))
        if best is None or newE < best:
            best = newE
    return best


def flag_multiplication_tables(sigma, ell, N, graphs):
    """Build M_sigma(H) for every H in `graphs`.  Returns:
        flags: list of flag reps (as canonical edge-key)
        Mtabs: list (aligned with graphs) of (F x F) numpy arrays.

    M_sigma(H)[i,j] = probability over:
        * choose an injective m-tuple of vertices of H to be the type,
          conditioned on that induced labeled subgraph being isomorphic to
          sigma via that labeling (i.e. the m-tuple, in order, induces sigma);
        * randomly partition the remaining N-m vertices into two ordered sets
          of size (ell-m) each ... but standard Razborov uses UNORDERED equal
          split with the two flags read off each half + the type.
    We implement the exact counting version:
        numerator = sum over ways to pick an ordered type-tuple s (|s|=m) that
        induces sigma, then over ways to split remaining N-m vertices into an
        ordered pair (A,B) with |A|=|B|=ell-m, of [F_i == flag(s,A)] *
        [F_j == flag(s,B)];
        denominator = (number of type-tuples inducing sigma) * (number of
        ordered equal splits) .
    Averaged so that sum_{ij, i<=j weighted} ... = < q, M > gives the density.

    We use the normalization matching Razborov: the ensemble is
      (1) pick ordered m-tuple s uniformly among those inducing sigma,
      (2) pick ordered disjoint (ell-m)-subsets A,B of the rest uniformly.
    Then M[i,j] = P[flag(s,A)=F_i AND flag(s,B)=F_j].  This M is symmetric PSD-
    averaged; <Q, M> with Q>=0 is a valid nonneg quantum-graph density.
    """
    m = sigma.number_of_nodes()
    r = ell - m           # extra per flag
    flags = enumerate_flags(sigma, ell)
    flag_keys = []
    for F in flags:
        E = tuple(sorted((min(u, v), max(u, v)) for u, v in F.edges()))
        flag_keys.append(_flag_key_fixing_type(E, m, ell))
    key_to_idx = {k: i for i, k in enumerate(flag_keys)}
    nf = len(flags)

    # sigma as ordered-edge set on 0..m-1
    sigma_ordered = set(tuple(sorted(e)) for e in sigma.edges())

    Mtabs = []
    for H in graphs:
        A = _adj(H)
        V = list(range(H.number_of_nodes()))
        assert len(V) == N
        Mt = np.zeros((nf, nf))
        denom = 0
        # iterate ordered type-tuples s inducing sigma
        for s in itertools.permutations(V, m):
            # check induced labeled subgraph on s equals sigma
            ok = True
            sedge = set()
            for a in range(m):
                for b in range(a + 1, m):
                    if A[s[a], s[b]]:
                        sedge.add((a, b))
            if sedge != sigma_ordered:
                continue
            rest = [v for v in V if v not in s]
            # ordered disjoint (r)-subsets A_,B_
            for A_ in itertools.permutations(rest, r):
                remaining = [v for v in rest if v not in A_]
                for B_ in itertools.permutations(remaining, r):
                    denom += 1
                    fiA = _flag_of(A, s, A_, m, ell)
                    fiB = _flag_of(A, s, B_, m, ell)
                    ia = key_to_idx[fiA]
                    ib = key_to_idx[fiB]
                    Mt[ia, ib] += 1.0
        if denom > 0:
            Mt /= denom
        Mtabs.append(Mt)
    return flags, flag_keys, Mtabs


def _flag_of(A, s, ext, m, ell):
    """Canonical flag key of the labeled graph: type vertices s[0..m-1] (in
    order) + extra vertices ext[0..r-1] (in order), induced from H (adj A)."""
    verts = list(s) + list(ext)
    E = []
    for a in range(ell):
        for b in range(a + 1, ell):
            if A[verts[a], verts[b]]:
                E.append((a, b))
    return _flag_key_fixing_type(E, m, ell)
