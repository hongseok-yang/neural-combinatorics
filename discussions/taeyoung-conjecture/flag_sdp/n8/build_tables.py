"""
build_tables.py
===============
Step 3: flag pair-density tables at N=8, stored SPARSE.

Blocks (2*ell - m = 8):
  m=0, ell=4 : 1 type (empty), flags = 11 four-vertex graphs.
  m=2, ell=5 : 2 types (nonedge, edge), flags = 5-vertex graphs w/ 2 roots.
  m=4, ell=6 : 11 types, flags = 6-vertex graphs w/ 4 roots (272 per type).

NORMALIZATION (corrected, UNCONDITIONAL = true Razborov unlabeling):
  M_sigma(H)[i,j] = P[ tuple induces sigma AND flag(s,A)=F_i AND flag(s,B)=F_j ]
over a uniform ordered m-tuple s of distinct vertices of H and a uniform
ordered equal split (A,B) of the rest, i.e. FIXED denominator
(#ordered m-tuples) x (#splits).  This equals q_sigma(H) * M_cond(H) where
M_cond is flagalg.flag_multiplication_tables' conditional table and
q_sigma(H) = P[random ordered m-tuple induces sigma].

WHY: the conditional convention used at N=7 does NOT have the graphon
averaging-PSD property.  Verified exactly at N=8: for 0/1 step graphons,
sum_H p(H,W) M_cond(H) has min eig as low as -4.6e-3 (block m=2 nonedge),
while sum_H p(H,W) q_sigma(H) M_cond(H) is PSD to 1e-16.  Only the
unconditional form is the evaluation of the quantum graph [[F_i F_j]]_sigma,
hence only it gives valid certificates.  (Ordered-permutation and
unordered-subset counting agree because the flag key mods out permutations
of the extra vertices; validated exactly vs flagalg * q_sigma.)

Output per block b: scipy CSR matrix S_b of shape (nH, ntri_b) with
  S_b[h, tri(i,j)] = (M_ij + M_ji)/  (i<j)   [i.e. 2*M_ij by symmetry]
                     M_ii                     (i=j)
so that  sum_sigma <Q, M(H)> = S_b[h] . Qtri  with Qtri = (Q_ij)_{i<=j}.
tri index order: for j in range(nf): for i in range(j+1)  ->  k = j(j+1)/2 + i
(matches Clarabel's upper-triangular column-stacked svec order, unscaled).
"""
import os, sys, time, pickle, itertools
import numpy as np
import scipy.sparse as sp

import n8lib
from n8lib import DATA, N, PAIRS

sys.path.insert(0, n8lib.FLAGSDP)
import flagalg as fa

TRI = lambda i, j: j * (j + 1) // 2 + i     # requires i <= j


# ------------------------------------------------------------- flag luts
def _canon4():
    """m=0,ell=4: 6-bit pattern (pairs of 4 vtx, combinations order) -> canonical."""
    pairs4 = list(itertools.combinations(range(4), 2))
    pidx = {e: k for k, e in enumerate(pairs4)}
    lut = np.zeros(64, dtype=np.int64)
    for pat in range(64):
        best = None
        for perm in itertools.permutations(range(4)):
            q = 0
            for k, (a, b) in enumerate(pairs4):
                if (pat >> k) & 1:
                    x, y = perm[a], perm[b]
                    q |= 1 << pidx[(min(x, y), max(x, y))]
            if best is None or q < best:
                best = q
        lut[pat] = best
    canons = sorted(set(lut.tolist()))
    cidx = {c: i for i, c in enumerate(canons)}
    fidx = np.array([cidx[c] for c in lut.tolist()], dtype=np.int64)
    return fidx, canons


def _canon2():
    """m=2,ell=5: 9-bit pattern -> canonical under S3 on extras.
    bits 2k,2k+1 = r0~ek, r1~ek (k=0,1,2); bits 6,7,8 = e0e1,e0e2,e1e2."""
    inner_pairs = [(0, 1), (0, 2), (1, 2)]
    ipidx = {e: k for k, e in enumerate(inner_pairs)}
    lut = np.zeros(512, dtype=np.int64)
    for pat in range(512):
        f = [(pat >> (2 * k)) & 3 for k in range(3)]
        inn = [(pat >> (6 + k)) & 1 for k in range(3)]
        best = None
        for perm in itertools.permutations(range(3)):
            # new position j holds old extra perm[j]
            q = 0
            for j in range(3):
                q |= f[perm[j]] << (2 * j)
            for (a, b) in inner_pairs:
                oa, ob = perm[a], perm[b]
                if inn[ipidx[(min(oa, ob), max(oa, ob))]]:
                    q |= 1 << (6 + ipidx[(a, b)])
            if best is None or q < best:
                best = q
        lut[pat] = best
    canons = sorted(set(lut.tolist()))
    cidx = {c: i for i, c in enumerate(canons)}
    fidx = np.array([cidx[c] for c in lut.tolist()], dtype=np.int64)
    return fidx, canons


def _canon1():
    """m=4,ell=6: 9-bit pattern -> canonical under swap of the 2 extras.
    bits 0..3 = r_i~e0; bits 4..7 = r_i~e1; bit 8 = e0~e1."""
    lut = np.zeros(512, dtype=np.int64)
    for pat in range(512):
        a = pat & 15
        b = (pat >> 4) & 15
        inn = (pat >> 8) & 1
        sw = b | (a << 4) | (inn << 8)
        lut[pat] = min(pat, sw)
    canons = sorted(set(lut.tolist()))
    cidx = {c: i for i, c in enumerate(canons)}
    fidx = np.array([cidx[c] for c in lut.tolist()], dtype=np.int64)
    return fidx, canons


FIDX4, CANONS4 = _canon4()          # m=0
FIDX2, CANONS2 = _canon2()          # m=2
FIDX1, CANONS1 = _canon1()          # m=4
NF0 = len(CANONS4)                  # 11
NF2 = len(CANONS2)
NF4 = len(CANONS1)                  # 272

# type reps aligned with flagalg
TYPES2 = fa.enumerate_types(2)      # [nonedge, edge] as labeled graphs
TYPES4 = fa.enumerate_types(4)      # 11 labeled reps
PAIRS4 = list(itertools.combinations(range(4), 2))


def _typepat4(sigma):
    pat = 0
    for k, (a, b) in enumerate(PAIRS4):
        if sigma.has_edge(a, b):
            pat |= 1 << k
    return pat


TYPE4_PAT = [_typepat4(s) for s in TYPES4]
TYPE4_LUT = -np.ones(64, dtype=np.int64)
for ti, tp in enumerate(TYPE4_PAT):
    TYPE4_LUT[tp] = ti
TYPE2_EDGEBIT = [1 if s.number_of_edges() else 0 for s in TYPES2]  # [0,1]
T2_OF_BIT = {eb: ti for ti, eb in enumerate(TYPE2_EDGEBIT)}

# global (graph-independent) iteration structures
SUBSETS4 = [(A, tuple(x for x in range(8) if x not in A))
            for A in itertools.combinations(range(8), 4)]           # 70
PAIRS_ORD = [(u, v) for u in range(8) for v in range(8) if u != v]  # 56
SUB3POS = [(A, tuple(x for x in range(6) if x not in A))
           for A in itertools.combinations(range(6), 3)]            # 20
TUPLES4 = list(itertools.permutations(range(8), 4))                 # 1680
REST4 = [tuple(x for x in range(8) if x not in s) for s in TUPLES4]
SUB2POS = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)),
           ((1, 2), (0, 3)), ((1, 3), (0, 2)), ((2, 3), (0, 1))]     # 6 ordered
PAIRS4V = list(itertools.combinations(range(4), 2))                 # rest pairs


# ------------------------------------------------------------- per-graph
def tables_m0(adj):
    """dict (i,j)->weight for the single m=0 block (q_sigma == 1 here, so
    conditional == unconditional; denominator 70)."""
    d = {}
    for (A, B) in SUBSETS4:
        pa = 0
        k = 0
        for x in range(4):
            ax = adj[A[x]]
            for y in range(x + 1, 4):
                if (ax >> A[y]) & 1:
                    pa |= 1 << k
                k += 1
        pb = 0
        k = 0
        for x in range(4):
            ax = adj[B[x]]
            for y in range(x + 1, 4):
                if (ax >> B[y]) & 1:
                    pb |= 1 << k
                k += 1
        key = (FIDX4[pa], FIDX4[pb])
        d[key] = d.get(key, 0.0) + 1.0
    for k in d:
        d[k] /= 70.0
    return [d], [1]


def tables_m2(adj):
    """[dict for type nonedge, dict for type edge], UNCONDITIONAL:
    fixed denominator 56*20; also returns per-type sigma-tuple counts."""
    ds = [{}, {}]
    cnt = [0, 0]
    for (u, v) in PAIRS_ORD:
        eb = (adj[u] >> v) & 1
        ti = T2_OF_BIT[eb]
        cnt[ti] += 1
        rest = [x for x in range(8) if x != u and x != v]
        f = [((adj[u] >> w) & 1) | (((adj[v] >> w) & 1) << 1) for w in rest]
        inner = [[0] * 6 for _ in range(6)]
        for a in range(6):
            ra = adj[rest[a]]
            for b in range(a + 1, 6):
                if (ra >> rest[b]) & 1:
                    inner[a][b] = inner[b][a] = 1
        d = ds[ti]
        for (A, B) in SUB3POS:
            a0, a1, a2 = A
            pa = f[a0] | (f[a1] << 2) | (f[a2] << 4) | \
                (inner[a0][a1] << 6) | (inner[a0][a2] << 7) | (inner[a1][a2] << 8)
            b0, b1, b2 = B
            pb = f[b0] | (f[b1] << 2) | (f[b2] << 4) | \
                (inner[b0][b1] << 6) | (inner[b0][b2] << 7) | (inner[b1][b2] << 8)
            key = (FIDX2[pa], FIDX2[pb])
            d[key] = d.get(key, 0.0) + 1.0
    inv = 1.0 / (56.0 * 20.0)
    for ti in range(2):
        for k in ds[ti]:
            ds[ti][k] *= inv
    return ds, cnt


def tables_m4(adj):
    """11 dicts (per TYPES4 rep), UNCONDITIONAL: fixed denominator 1680*6;
    also returns per-type sigma-tuple counts."""
    ds = [{} for _ in range(11)]
    cnt = [0] * 11
    for tix, s in enumerate(TUPLES4):
        s0, s1, s2, s3 = s
        a0, a1, a2 = adj[s0], adj[s1], adj[s2]
        tpat = ((a0 >> s1) & 1) | (((a0 >> s2) & 1) << 1) | (((a0 >> s3) & 1) << 2) \
            | (((a1 >> s2) & 1) << 3) | (((a1 >> s3) & 1) << 4) | (((a2 >> s3) & 1) << 5)
        ti = TYPE4_LUT[tpat]
        if ti < 0:
            continue
        cnt[ti] += 1
        rest = REST4[tix]
        g = [((a0 >> w) & 1) | (((a1 >> w) & 1) << 1) | (((a2 >> w) & 1) << 2)
             | (((adj[s3] >> w) & 1) << 3) for w in rest]
        e = {}
        for (x, y) in PAIRS4V:
            e[(x, y)] = (adj[rest[x]] >> rest[y]) & 1
        d = ds[ti]
        for (A, B) in SUB2POS:
            xa, ya = A
            pa = g[xa] | (g[ya] << 4) | (e[(min(xa, ya), max(xa, ya))] << 8)
            xb, yb = B
            pb = g[xb] | (g[yb] << 4) | (e[(min(xb, yb), max(xb, yb))] << 8)
            key = (FIDX1[pa], FIDX1[pb])
            d[key] = d.get(key, 0.0) + 1.0
    inv = 1.0 / (1680.0 * 6.0)
    for ti in range(11):
        for k in ds[ti]:
            ds[ti][k] *= inv
    return ds, cnt


# --------------------------------------------------- dict -> sparse row data
def _push(dicts, h, rows, cols, vals):
    """Convert per-graph dicts to tri-indexed COO entries (M_ij+M_ji for i<j)."""
    for b, d in enumerate(dicts):
        acc = {}
        for (i, j), w in d.items():
            i, j = int(i), int(j)
            key = (i, j) if i <= j else (j, i)
            acc[key] = acc.get(key, 0.0) + w
        R, C, V = rows[b], cols[b], vals[b]
        for (i, j), w in acc.items():
            R.append(h)
            C.append(TRI(i, j))
            V.append(w)


# ------------------------------------------------------------- m=6 (ell=7)
# types: all 156 iso classes on 6 vertices; flags: 6 roots + 1 extra vertex,
# pattern = 6 cross bits, 64 flags, no canonicalization (single extra).
_M6 = {}


def _init_m6():
    if _M6:
        return
    types6 = fa.enumerate_types(6)          # 156 labeled reps
    pairs6 = list(itertools.combinations(range(6), 2))
    lut = -np.ones(1 << 15, dtype=np.int64)
    pats = []
    for ti, s in enumerate(types6):
        pat = 0
        for k, (a, b) in enumerate(pairs6):
            if s.has_edge(a, b):
                pat |= 1 << k
        lut[pat] = ti
        pats.append(pat)
    T = np.array(list(itertools.permutations(range(8), 6)), dtype=np.int64)
    R = np.zeros((T.shape[0], 2), dtype=np.int64)     # the 2 leftover vertices
    full = set(range(8))
    for i in range(T.shape[0]):
        a, b = sorted(full - set(T[i].tolist()))
        R[i] = (a, b)
    _M6.update(types6=types6, pairs6=pairs6, lut=lut, T=T, R=R,
               nt=len(types6))


def tables_m6(adj):
    """156 dicts; UNCONDITIONAL, fixed denominator 20160*2."""
    _init_m6()
    T, R, lut, pairs6 = _M6["T"], _M6["R"], _M6["lut"], _M6["pairs6"]
    nt = _M6["nt"]
    A = np.zeros((8, 8), dtype=np.int64)
    for v in range(8):
        for u in range(8):
            A[v, u] = (adj[v] >> u) & 1
    tpat = np.zeros(T.shape[0], dtype=np.int64)
    for k, (a, b) in enumerate(pairs6):
        tpat |= A[T[:, a], T[:, b]] << k
    ti = lut[tpat]
    keep = ti >= 0
    Tk, Rk, tik = T[keep], R[keep], ti[keep]
    # flag pattern of extra w against roots (in tuple order)
    fa_ = np.zeros(Tk.shape[0], dtype=np.int64)
    fb_ = np.zeros(Tk.shape[0], dtype=np.int64)
    for i in range(6):
        fa_ |= A[Rk[:, 0], Tk[:, i]] << i
        fb_ |= A[Rk[:, 1], Tk[:, i]] << i
    ds = [{} for _ in range(nt)]
    cnt = np.zeros(nt, dtype=np.int64)
    inv = 1.0 / (20160.0 * 2.0)
    for t, x, y in zip(tik, fa_, fb_):
        d = ds[t]
        for key in ((int(x), int(y)), (int(y), int(x))):
            d[key] = d.get(key, 0.0) + inv
    np.add.at(cnt, tik, 1)
    return ds, cnt.tolist()


def _perg_m0m2(adj):
    d0, c0 = tables_m0(adj)
    d2, c2 = tables_m2(adj)
    return d0 + d2, c0 + c2


def build(which, cl, chunk=4000, verbose=True):
    """which in {'m0m2','m4'}; builds and caches CSR matrices + metadata.
    Payload: S (list of nH x ntri CSR), meta, nsig (nH x nblocks int array of
    #ordered sigma-tuples per graph; q_sigma(H) = nsig/(#all ordered m-tuples))."""
    nH = len(cl.masks)
    if which == "m0m2":
        nblocks, nfs = 3, [NF0, NF2, NF2]
        fn = os.path.join(DATA, "tables_uncond_m0m2.pkl")
        perg = _perg_m0m2
        meta = dict(blocks=[dict(m=0, edges=[], nf=NF0),
                            dict(m=2, edges=[], nf=NF2),
                            dict(m=2, edges=[(0, 1)], nf=NF2)])
    elif which == "m6":
        _init_m6()
        nblocks, nfs = _M6["nt"], [64] * _M6["nt"]
        fn = os.path.join(DATA, "tables_uncond_m6.pkl")
        perg = tables_m6
        meta = dict(blocks=[dict(m=6, edges=sorted(map(tuple, s.edges())),
                                 nf=64) for s in _M6["types6"]])
    else:
        nblocks, nfs = 11, [NF4] * 11
        fn = os.path.join(DATA, "tables_uncond_m4.pkl")
        perg = tables_m4
        meta = dict(blocks=[dict(m=4, edges=sorted(map(tuple, TYPES4[t].edges())),
                                 nf=NF4) for t in range(11)])
    if os.path.exists(fn):
        with open(fn, "rb") as f:
            return pickle.load(f)
    t0 = time.time()
    rows = [[] for _ in range(nblocks)]
    cols = [[] for _ in range(nblocks)]
    vals = [[] for _ in range(nblocks)]
    nsig = np.zeros((nH, nblocks), dtype=np.int64)
    for h in range(nH):
        adj = n8lib.adjrows_from_mask(cl.masks[h])
        dicts, cnts = perg(adj)
        nsig[h] = cnts
        _push(dicts, h, rows, cols, vals)
        if verbose and (h + 1) % chunk == 0:
            el = time.time() - t0
            print(f"  {which}: {h+1}/{nH} graphs, {el:.0f}s "
                  f"(eta {el/(h+1)*(nH-h-1):.0f}s)", flush=True)
    S = []
    for b in range(nblocks):
        nf = nfs[b]
        ntri = nf * (nf + 1) // 2
        S.append(sp.csr_matrix(
            (np.array(vals[b]), (np.array(rows[b], dtype=np.int64),
                                 np.array(cols[b], dtype=np.int64))),
            shape=(nH, ntri)))
    payload = dict(S=S, meta=meta, which=which, nsig=nsig)
    with open(fn, "wb") as f:
        pickle.dump(payload, f)
    if verbose:
        nnz = [int(x.nnz) for x in S]
        print(f"{which}: built in {time.time()-t0:.0f}s, nnz per block {nnz}")
    return payload


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "m0m2"
    cl = n8lib.enumerate8()
    print(f"flag counts: m0 nf={NF0}, m2 nf={NF2} (x2 types), m4 nf={NF4} (x11 types)")
    build(which, cl)
