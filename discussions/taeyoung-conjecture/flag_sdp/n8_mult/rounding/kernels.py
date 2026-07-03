"""
kernels.py -- exact (Fraction) flag-evaluation vectors of the equality
graphons T_k (balanced complete multipartite, k=2..8) and W==1, per SDP block.

Conventions (must match build_tables.py / multlib.py exactly):

Q blocks (ground 8):
  m=0  : flags = canonical 4-vtx 6-bit patterns (bt.FIDX4), 11 flags.
  m=2  : type nonedge/edge; flags 9-bit (bt.FIDX2): bits 2t,2t+1 = r0~e_t,
         r1~e_t (t=0,1,2); bits 6,7,8 = inner pairs (0,1),(0,2),(1,2). 120.
  m=4  : type = bt.TYPES4[t] labeled rep; flags 9-bit (bt.FIDX1): bits 0..3 =
         r_i~e0, bits 4..7 = r_i~e1, bit 8 = e0~e1; mod extra swap. 272.
  m=6  : type = 6-vtx labeled rep (edges in meta); flags = 6 cross bits,
         bit i = extra ~ root i. 64.
R blocks (ground 6, multlib.BLOCK_META):
  m'=0 : flags = #edges of the 3-set (0..3). 4.
  m'=2 : type nonedge/edge; flags 5-bit (ml.FIDX_M2): bits 0,1 = r0~e0,r1~e0;
         bits 2,3 = r0~e1,r1~e1; bit 4 = e0~e1; mod extra swap. 20.
  m'=4 : type = bt.TYPES4[t]; flags = 4 cross bits, bit i = extra ~ root i. 16.

At the balanced T_k (0/1 step graphon, k equal blocks), adjacency is
1[different block]; a type sigma is induced iff sigma is complete multipartite
(same part <=> non-adjacent) with #parts <= k, and all valid root assignments
give the SAME evaluation vector (block exchangeability).  W==1 is the k->inf
limit and only induces complete types.
"""
import itertools
from fractions import Fraction

import numpy as np

import common  # sets sys.path
import build_tables as bt
import multlib as ml


def multipartite_parts(m, edges):
    """If the labeled type (vertices 0..m-1, edge list) is complete
    multipartite, return blk: vertex -> part index; else None.
    m=0: returns []."""
    if m == 0:
        return []
    E = set()
    for (a, b) in edges:
        E.add((min(a, b), max(a, b)))
    # union-find on non-adjacency
    parent = list(range(m))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for u in range(m):
        for v in range(u + 1, m):
            if (u, v) not in E:
                parent[find(u)] = find(v)
    lab = {}
    blk = []
    for v in range(m):
        r = find(v)
        if r not in lab:
            lab[r] = len(lab)
        blk.append(lab[r])
    # verify: same part <=> non-adjacent
    for u in range(m):
        for v in range(u + 1, m):
            adj = (u, v) in E
            if adj == (blk[u] == blk[v]):
                return None
    return blk


def _vec(nf):
    return [Fraction(0)] * nf


# ---------------------------------------------------------- Q-block vectors
def qvec_m0(k):
    """k=None means W==1."""
    v = _vec(11)
    if k is None:
        v[bt.FIDX4[63]] = Fraction(1)
        return v
    pairs4 = list(itertools.combinations(range(4), 2))
    den = Fraction(1, k ** 4)
    for c in itertools.product(range(k), repeat=4):
        pat = 0
        for t, (a, b) in enumerate(pairs4):
            if c[a] != c[b]:
                pat |= 1 << t
        v[bt.FIDX4[pat]] += den
    return v


def qvec_m2(edge, k):
    v = _vec(bt.NF2)
    if k is None:
        if not edge:
            return None
        v[bt.FIDX2[511]] = Fraction(1)
        return v
    r = (0, 1) if edge else (0, 0)
    if edge and k < 2:
        return None
    den = Fraction(1, k ** 3)
    inner_pairs = [(0, 1), (0, 2), (1, 2)]
    for c in itertools.product(range(k), repeat=3):
        pat = 0
        for t in range(3):
            if c[t] != r[0]:
                pat |= 1 << (2 * t)
            if c[t] != r[1]:
                pat |= 1 << (2 * t + 1)
        for i, (a, b) in enumerate(inner_pairs):
            if c[a] != c[b]:
                pat |= 1 << (6 + i)
        v[bt.FIDX2[pat]] += den
    return v


def qvec_m4(edges, k):
    blk = multipartite_parts(4, edges)
    if blk is None:
        return None
    j = max(blk) + 1
    v = _vec(bt.NF4)
    if k is None:
        if j < 4:
            return None
        v[bt.FIDX1[511]] = Fraction(1)
        return v
    if k < j:
        return None
    den = Fraction(1, k ** 2)
    for c0 in range(k):
        for c1 in range(k):
            pat = 0
            for i in range(4):
                if c0 != blk[i]:
                    pat |= 1 << i
                if c1 != blk[i]:
                    pat |= 1 << (4 + i)
            if c0 != c1:
                pat |= 1 << 8
            v[bt.FIDX1[pat]] += den
    return v


def qvec_m6(edges, k):
    blk = multipartite_parts(6, edges)
    if blk is None:
        return None
    j = max(blk) + 1
    v = _vec(64)
    if k is None:
        if j < 6:
            return None
        v[63] = Fraction(1)
        return v
    if k < j:
        return None
    den = Fraction(1, k)
    for c in range(k):
        pat = 0
        for i in range(6):
            if c != blk[i]:
                pat |= 1 << i
        v[pat] += den
    return v


# ---------------------------------------------------------- R-block vectors
def rvec_m0(k):
    v = _vec(4)
    if k is None:
        v[3] = Fraction(1)
        return v
    den = Fraction(1, k ** 3)
    for c in itertools.product(range(k), repeat=3):
        e = (c[0] != c[1]) + (c[0] != c[2]) + (c[1] != c[2])
        v[e] += den
    return v


def rvec_m2(edge, k):
    v = _vec(ml.NF_M2)
    if k is None:
        if not edge:
            return None
        v[ml.FIDX_M2[31]] = Fraction(1)
        return v
    r = (0, 1) if edge else (0, 0)
    den = Fraction(1, k ** 2)
    for c0 in range(k):
        for c1 in range(k):
            pat = 0
            if c0 != r[0]:
                pat |= 1
            if c0 != r[1]:
                pat |= 2
            if c1 != r[0]:
                pat |= 4
            if c1 != r[1]:
                pat |= 8
            if c0 != c1:
                pat |= 16
            v[ml.FIDX_M2[pat]] += den
    return v


def rvec_m4(edges, k):
    blk = multipartite_parts(4, edges)
    if blk is None:
        return None
    j = max(blk) + 1
    v = _vec(16)
    if k is None:
        if j < 4:
            return None
        v[15] = Fraction(1)
        return v
    if k < j:
        return None
    den = Fraction(1, k)
    for c in range(k):
        pat = 0
        for i in range(4):
            if c != blk[i]:
                pat |= 1 << i
        v[pat] += den
    return v


# ------------------------------------------------- bipartite derivative vecs
# The unbalanced complete bipartite family W_a (blocks weight a, 1-a,
# adjacency = different blocks) has Delta2(W_a) == 0 for ALL a; expanding the
# averaging identity at a=1/2 forces, for any exact c=0 certificate,
#   Q_b phi'_b(1/2) = 0   (types = complete multipartite with <= 2 parts),
#   R_b w_b(T_2) = 0      (the balanced k=2 vectors, all R blocks),
# in addition to the T_k kernels.  (Verified numerically on the face iterate:
# |R w_T2| ~ 1e-12; Q-side 4th-order scaling of <Q,Gram8(W_a)>.)
def _deriv_weight(c, e):
    """d/da prod_i w_{c_i} at a=1/2, w=(a,1-a): (n0-n1) / 2^(e-1)."""
    n0 = sum(1 for x in c if x == 0)
    return Fraction(n0 - (e - n0), 1 << (e - 1))


def qderiv_vec(blkmeta):
    m = blkmeta["m"]
    if m == 0:
        return None                      # symmetric in a: derivative == 0
    blk = multipartite_parts(m, blkmeta["edges"])
    if blk is None or max(blk) + 1 > 2:
        return None
    if m == 2:
        v = _vec(bt.NF2)
        r = (blk[0], blk[1])
        inner_pairs = [(0, 1), (0, 2), (1, 2)]
        for c in itertools.product((0, 1), repeat=3):
            pat = 0
            for t in range(3):
                if c[t] != r[0]:
                    pat |= 1 << (2 * t)
                if c[t] != r[1]:
                    pat |= 1 << (2 * t + 1)
            for i, (a, b) in enumerate(inner_pairs):
                if c[a] != c[b]:
                    pat |= 1 << (6 + i)
            v[bt.FIDX2[pat]] += _deriv_weight(c, 3)
        return v
    if m == 4:
        v = _vec(bt.NF4)
        for c0 in (0, 1):
            for c1 in (0, 1):
                pat = 0
                for i in range(4):
                    if c0 != blk[i]:
                        pat |= 1 << i
                    if c1 != blk[i]:
                        pat |= 1 << (4 + i)
                if c0 != c1:
                    pat |= 1 << 8
                v[bt.FIDX1[pat]] += _deriv_weight((c0, c1), 2)
        return v
    if m == 6:
        v = _vec(64)
        for c in (0, 1):
            pat = 0
            for i in range(6):
                if c != blk[i]:
                    pat |= 1 << i
            v[pat] += _deriv_weight((c,), 1)
        return v
    raise ValueError(m)


def qblock_vec(blkmeta, k):
    m = blkmeta["m"]
    if m == 0:
        return qvec_m0(k)
    if m == 2:
        return qvec_m2(bool(blkmeta["edges"]), k)
    if m == 4:
        return qvec_m4(blkmeta["edges"], k)
    if m == 6:
        return qvec_m6(blkmeta["edges"], k)
    raise ValueError(m)


def rblock_vec(blkmeta, k):
    m = blkmeta["m"]
    if m == 0:
        return rvec_m0(k)
    if m == 2:
        return rvec_m2(bool(blkmeta["edges"]), k)
    if m == 4:
        return rvec_m4(blkmeta["edges"], k)
    raise ValueError(m)


# --------------------------------------------------- rational span reduction
def rational_span(vecs):
    """Row-reduce a list of Fraction vectors; return a reduced rational basis
    (list of Fraction vectors, pivot-normalized)."""
    basis = []   # list of (pivot, vec)
    for v in vecs:
        v = list(v)
        for (p, b) in basis:
            if v[p] != 0:
                c = v[p]
                v = [x - c * y for x, y in zip(v, b)]
        piv = next((i for i, x in enumerate(v) if x != 0), None)
        if piv is None:
            continue
        c = v[piv]
        v = [x / c for x in v]
        basis.append((piv, v))
    basis.sort()
    return [b for (_, b) in basis]


KS = [2, 3, 4, 5, 6, 7, 8, None]        # None == W=1
# R blocks: k=2 IS forced (via the bipartite-family expansion; verified on
# the face iterate to 1e-12), on top of k>=3 where (2p-1)>0 forces it.
KS_R = [2, 3, 4, 5, 6, 7, 8, None]


def harvest(metaQ, metaR, derivatives=True):
    """Return (Kq, Kr): per block, a reduced rational kernel basis
    (list of Fraction vectors), plus the raw per-k vectors."""
    Kq_raw, Kr_raw = [], []
    for bm in metaQ:
        vs = {}
        for k in KS:
            v = qblock_vec(bm, k)
            if v is not None:
                vs[k] = v
        if derivatives:
            v = qderiv_vec(bm)
            if v is not None:
                vs["d"] = v
        Kq_raw.append(vs)
    for bm in metaR:
        vs = {}
        for k in KS_R:
            v = rblock_vec(bm, k)
            if v is not None:
                vs[k] = v
        Kr_raw.append(vs)
    Kq = [rational_span(list(vs.values())) for vs in Kq_raw]
    Kr = [rational_span(list(vs.values())) for vs in Kr_raw]
    return Kq, Kr, Kq_raw, Kr_raw


def to_float(vecs):
    return np.array([[float(x) for x in v] for v in vecs])
