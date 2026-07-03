"""
n8lib.py
========
N=8 extension of the validated flag_sdp pipeline.

Core objects:
  * 8-vertex graphs as 28-bit edge masks (pair order = itertools.combinations(range(8),2)).
  * enumeration of all 12346 iso classes by extending the validated 1044
    7-vertex classes with an 8th vertex (2^7 neighborhoods) + invariant-bucket
    dedup with nx.is_isomorphic inside buckets.
  * Classifier: arbitrary 28-bit mask -> class index (same buckets).
  * fast injective-hom counting (bitmask backtracking) -> t_inj(F,H).
  * automorphism counting (for exact p(H, W=const p)).

All conventions match flag_sdp/ (induced-density basis, coef[H]=sum q_a t_inj(F_a,H)).
"""
import os, sys, time, pickle, itertools
import numpy as np
import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
FLAGSDP = os.path.dirname(HERE)
sys.path.insert(0, FLAGSDP)
sys.path.insert(0, os.path.join(os.path.dirname(FLAGSDP), "scripts"))

DATA = os.path.join(HERE, "data")
os.makedirs(DATA, exist_ok=True)

N = 8
PAIRS = list(itertools.combinations(range(N), 2))   # 28 pairs, lexicographic
PIDX = {e: k for k, e in enumerate(PAIRS)}
NPAIR = len(PAIRS)


# ---------------------------------------------------------------- mask utils
def mask_from_graph(G):
    m = 0
    for u, v in G.edges():
        a, b = (u, v) if u < v else (v, u)
        m |= 1 << PIDX[(a, b)]
    return m


def graph_from_mask(mask, n=N):
    G = nx.Graph()
    G.add_nodes_from(range(n))
    for k, (a, b) in enumerate(PAIRS):
        if a < n and b < n and (mask >> k) & 1:
            G.add_edge(a, b)
    return G


def adjrows_from_mask(mask):
    """adj[v] = bitmask over vertices adjacent to v."""
    adj = [0] * N
    for k, (a, b) in enumerate(PAIRS):
        if (mask >> k) & 1:
            adj[a] |= 1 << b
            adj[b] |= 1 << a
    return adj


def mask_edge_count(mask):
    return bin(mask).count("1")


# ------------------------------------------------------- invariants / dedup
def invariant_key(mask):
    """Cheap, iso-invariant bucket key: (#edges, sorted degseq,
    sorted (deg, sorted nbr degs), integer char poly of adjacency)."""
    adj = adjrows_from_mask(mask)
    deg = [bin(a).count("1") for a in adj]
    nbrdeg = []
    for v in range(N):
        ds = tuple(sorted(deg[u] for u in range(N) if (adj[v] >> u) & 1))
        nbrdeg.append((deg[v], ds))
    A = np.zeros((N, N))
    for k, (a, b) in enumerate(PAIRS):
        if (mask >> k) & 1:
            A[a, b] = A[b, a] = 1.0
    ev = np.linalg.eigvalsh(A)
    cp = np.poly(ev)                       # integer coefficients for 0/1 adjacency
    cpi = tuple(int(round(x)) for x in cp)
    return (bin(mask).count("1"), tuple(sorted(deg)), tuple(sorted(nbrdeg)), cpi)


class Classifier:
    """Bucketed iso-class lookup for 28-bit masks."""
    def __init__(self):
        self.buckets = {}     # key -> list of (mask, class_index)
        self.masks = []       # class index -> representative mask
        self._nxcache = {}    # rep mask -> nx graph

    def _nx(self, mask):
        g = self._nxcache.get(mask)
        if g is None:
            g = graph_from_mask(mask)
            self._nxcache[mask] = g
        return g

    def add_or_get(self, mask, key=None):
        """Return (class_index, is_new)."""
        if key is None:
            key = invariant_key(mask)
        bucket = self.buckets.setdefault(key, [])
        if bucket:
            G = graph_from_mask(mask)
            for (m2, idx) in bucket:
                if m2 == mask or nx.is_isomorphic(self._nx(m2), G):
                    return idx, False
        idx = len(self.masks)
        self.masks.append(mask)
        bucket.append((mask, idx))
        return idx, True

    def classify(self, mask):
        """Class index of an existing class (raises if unknown)."""
        key = invariant_key(mask)
        bucket = self.buckets.get(key)
        if not bucket:
            raise KeyError("unknown iso class")
        if len(bucket) == 1:
            return bucket[0][1]
        G = graph_from_mask(mask)
        for (m2, idx) in bucket:
            if m2 == mask or nx.is_isomorphic(self._nx(m2), G):
                return idx
        raise KeyError("unknown iso class (bucket miss)")


def enumerate8(verbose=True):
    """All 12346 iso classes of 8-vertex graphs; cached.  Returns Classifier."""
    fn = os.path.join(DATA, "graphs8.pkl")
    if os.path.exists(fn):
        with open(fn, "rb") as f:
            payload = pickle.load(f)
        cl = Classifier()
        cl.masks = payload["masks"]
        cl.buckets = payload["buckets"]
        return cl
    t0 = time.time()
    with open(os.path.join(FLAGSDP, "data", "graphs_N7.pkl"), "rb") as f:
        g7 = pickle.load(f)
    assert len(g7) == 1044, f"expected 1044 7-vertex graphs, got {len(g7)}"
    cl = Classifier()
    cand = 0
    for G7 in g7:
        base = 0
        for u, v in G7.edges():
            a, b = (u, v) if u < v else (v, u)
            base |= 1 << PIDX[(a, b)]
        for nb in range(1 << 7):
            m = base
            for u in range(7):
                if (nb >> u) & 1:
                    m |= 1 << PIDX[(u, 7)]
            cl.add_or_get(m)
            cand += 1
    if verbose:
        print(f"enumerate8: {cand} candidates -> {len(cl.masks)} classes "
              f"({time.time()-t0:.1f}s)")
    assert len(cl.masks) == 12346, f"COUNT MISMATCH: {len(cl.masks)} != 12346"
    # self-consistency: complement closure + symmetric edge histogram
    full = (1 << NPAIR) - 1
    hist = {}
    for m in cl.masks:
        hist[mask_edge_count(m)] = hist.get(mask_edge_count(m), 0) + 1
    for e, c in hist.items():
        assert hist[NPAIR - e] == c, "edge histogram not symmetric"
    for m in cl.masks[:200]:
        cl.classify(full ^ m)     # must exist
    with open(fn, "wb") as f:
        pickle.dump({"masks": cl.masks, "buckets": cl.buckets}, f)
    if verbose:
        print(f"enumerate8: cached to {fn}")
    return cl


# ------------------------------------------------- injective hom counting
def _order_pattern(edges, nv):
    """Vertex order for backtracking: each new vertex maximally back-connected."""
    adj = [set() for _ in range(nv)]
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    order = []
    remaining = set(range(nv))
    # start at max degree
    while remaining:
        if order:
            best = max(remaining,
                       key=lambda v: (len(adj[v] & set(order)), len(adj[v])))
        else:
            best = max(remaining, key=lambda v: len(adj[v]))
        order.append(best)
        remaining.discard(best)
    pos = {v: i for i, v in enumerate(order)}
    # back-neighbor lists in the new order
    back = [[] for _ in range(nv)]
    for a, b in edges:
        pa, pb = pos[a], pos[b]
        if pa > pb:
            back[pa].append(pb)
        else:
            back[pb].append(pa)
    return back


def count_inj_hom(back, nv, adj):
    """# injective homs of pattern (back-neighbor structure) into graph with
    adjacency bitmask rows adj (8 vertices)."""
    FULL = (1 << N) - 1
    img = [0] * nv

    def rec(d, used):
        if d == nv:
            return 1
        cand = FULL & ~used
        for pb in back[d]:
            cand &= adj[img[pb]]
        total = 0
        while cand:
            v = (cand & -cand).bit_length() - 1
            cand &= cand - 1
            img[d] = v
            total += rec(d + 1, used | (1 << v))
        return total

    return rec(0, 0)


def falling(n, k):
    r = 1
    for i in range(k):
        r *= (n - i)
    return r


def t_inj_mask(F_edges, F_nv, adj):
    back = _order_pattern(F_edges, F_nv)
    return count_inj_hom(back, F_nv, adj) / falling(N, F_nv)


def aut_count(adj):
    """|Aut| of the 8-vertex graph with adjacency rows adj: injective maps
    preserving adjacency AND non-adjacency."""
    deg = [bin(a).count("1") for a in adj]
    FULL = (1 << N) - 1
    img = [0] * N

    def rec(d, used):
        if d == N:
            return 1
        total = 0
        cand = FULL & ~used
        while cand:
            v = (cand & -cand).bit_length() - 1
            cand &= cand - 1
            if deg[v] != deg[d]:
                continue
            ok = True
            for e in range(d):
                want = (adj[d] >> e) & 1
                have = (adj[v] >> img[e]) & 1
                if want != have:
                    ok = False
                    break
            if ok:
                img[d] = v
                total += rec(d + 1, used | (1 << v))
        return total

    return rec(0, 0)


# ----------------------------------------------- exact p(H,W) for validation
def pvec_01_stepgraphon(w, M01, cl):
    """Exact induced-density vector over the 12346 classes for a 0/1 step
    graphon (weights w, 0/1 matrix M01): iterate colorings, the sampled graph
    is deterministic.  Returns pvec (sums to 1)."""
    nb = len(w)
    w = np.asarray(w, float)
    M01 = np.asarray(M01)
    assert set(np.unique(M01)).issubset({0, 1}), "M must be 0/1"
    acc = {}
    for c in itertools.product(range(nb), repeat=N):
        wt = 1.0
        for v in c:
            wt *= w[v]
        if wt == 0.0:
            continue
        m = 0
        for k, (a, b) in enumerate(PAIRS):
            if M01[c[a], c[b]]:
                m |= 1 << k
        acc[m] = acc.get(m, 0.0) + wt
    pvec = np.zeros(len(cl.masks))
    for m, wt in acc.items():
        pvec[cl.classify(m)] += wt
    return pvec


def pvec_const(p, cl, labeled_counts):
    """Exact induced-density vector for W == p (constant graphon):
    p(H) = n_labeled(H) * p^e * (1-p)^(28-e)."""
    pv = np.zeros(len(cl.masks))
    for i, m in enumerate(cl.masks):
        e = mask_edge_count(m)
        pv[i] = labeled_counts[i] * (p ** e) * ((1 - p) ** (NPAIR - e))
    return pv


def labeled_counts(cl, cache=True):
    """n_labeled(H) = 8!/|Aut(H)| for every class; cached."""
    fn = os.path.join(DATA, "labeled_counts.npy")
    if cache and os.path.exists(fn):
        return np.load(fn)
    out = np.zeros(len(cl.masks))
    f8 = falling(8, 8)
    for i, m in enumerate(cl.masks):
        out[i] = f8 // aut_count(adjrows_from_mask(m))
    if cache:
        np.save(fn, out)
    return out
