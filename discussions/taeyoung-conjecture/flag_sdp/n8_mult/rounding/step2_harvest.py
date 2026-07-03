"""
Step 2: kernel harvest + eigenspectrum inspection.

(a) exact Fraction kernel vectors per block for T_2..T_8 and W==1;
(b) validation: Gram8_b(T_k) computed from exact pvec8 must be rank-1
    proportional to v v^T (same for Gram6 on R blocks);
(c) residuals ||Qproj_b v|| (should be ~1e-8, the iterate scale);
(d) eigenspectra: near-zero eigenvalue counts vs dim K_b;
(e) locate the 22 complete-multipartite 8-vertex graphs and compare with the
    near-active slack set.
"""
import itertools, pickle
from fractions import Fraction
import numpy as np

import common, kernels
import n8lib, multlib as ml

cl, coef, SQ, metaQ, pl, res = common.load_everything()
Qp, Rp = res["Qproj"], res["Rproj"]
slack = np.load(common.os.path.join(common.DATA, "slack_float.npy"))

print("=== harvesting kernel vectors (exact rationals) ===")
Kq, Kr, Kq_raw, Kr_raw = kernels.harvest(metaQ, pl["meta"])
print("Q blocks with nonempty kernel:",
      sum(1 for K in Kq if K), "/", len(Kq))
print("R blocks with nonempty kernel:",
      sum(1 for K in Kr if K), "/", len(Kr))
print("total forced kernel dims: Q", sum(len(K) for K in Kq),
      "R", sum(len(K) for K in Kr))

with open(common.os.path.join(common.DATA, "kernels.pkl"), "wb") as f:
    pickle.dump(dict(Kq=Kq, Kr=Kr, Kq_raw=Kq_raw, Kr_raw=Kr_raw), f)

# ---------------------------------------------------------------- (b) validation
print("\n=== validation: Gram8_b(T_k) == q * v v^T (exact pvec, k=2,3,4) ===")
worst = 0.0
for k in (2, 3, 4):
    w = [1.0 / k] * k
    M01 = 1 - np.eye(k, dtype=int)
    pv8 = n8lib.pvec_01_stepgraphon(w, M01, cl)
    for b, (Sb, bm) in enumerate(zip(SQ, metaQ)):
        tri = pv8 @ Sb
        nf = bm["nf"]
        G = ml.tri_to_mat(np.asarray(tri).ravel(), nf)
        vs = Kq_raw[b].get(k)
        if vs is None:
            err = np.abs(G).max()
        else:
            v = np.array([float(x) for x in vs])
            q = G.trace() / (v @ v)
            err = np.abs(G - q * np.outer(v, v)).max()
        worst = max(worst, err)
    print(f"  k={k}: worst Gram8 rank-1 residual so far {worst:.3e}")
worstR = 0.0
for k in (2, 3, 4, 5):
    w = [1.0 / k] * k
    M01 = 1 - np.eye(k, dtype=int)
    pv6 = ml.pvec6_01_stepgraphon(w, M01, pl["cls_of_pat"])
    for b, (T, bm) in enumerate(zip(pl["T6tri"], pl["meta"])):
        tri = pv6 @ T
        nf = bm["nf"]
        G = ml.tri_to_mat(np.asarray(tri).ravel(), nf)
        vs = Kr_raw[b].get(k)
        if vs is None:
            # type not multipartite -> Gram must vanish? (no: only if type
            # not induced in T_k).  Rank-1 test with dominant eigvec instead:
            lam = np.linalg.eigvalsh(G)
            err = max(0.0, lam[-2] if len(lam) > 1 else 0.0, -lam[0])
        else:
            v = np.array([float(x) for x in vs])
            q = G.trace() / (v @ v)
            err = np.abs(G - q * np.outer(v, v)).max()
        worstR = max(worstR, err)
    print(f"  k={k}: worst Gram6 rank-1 residual so far {worstR:.3e}")

# ---------------------------------------------------------------- (c) residuals
print("\n=== residuals ||Q_b v||_inf on the projected iterate ===")
resid_stats = []
for b, K in enumerate(Kq):
    if not K:
        continue
    V = kernels.to_float(K)
    r = np.abs(Qp[b] @ V.T).max()
    resid_stats.append((r, b, len(K)))
resid_stats.sort(reverse=True)
print("worst 10 Q blocks (residual, block, dimK):")
for r, b, d in resid_stats[:10]:
    print(f"  block {b:3d} (m={metaQ[b]['m']}): resid {r:.3e}, dimK {d}")
residR = []
for b, K in enumerate(Kr):
    if not K:
        continue
    V = kernels.to_float(K)
    residR.append((np.abs(Rp[b] @ V.T).max(), b, len(K)))
residR.sort(reverse=True)
print("worst R blocks:")
for r, b, d in residR[:5]:
    print(f"  block {b:3d} (m'={pl['meta'][b]['m']}): resid {r:.3e}, dimK {d}")

# ---------------------------------------------------------------- (d) spectra
print("\n=== eigenspectra: near-zero eigs vs forced dim ===")
TH = 1e-5
extra_total = 0
rows = []
for b, Q in enumerate(Qp):
    lam = np.linalg.eigvalsh((Q + Q.T) / 2)
    nz = int((lam < TH).sum())
    d = len(Kq[b])
    extra = nz - d
    extra_total += max(extra, 0)
    rows.append((extra, b, nz, d, lam))
rows.sort(reverse=True)
print(f"threshold {TH:g}; total EXTRA near-zero dims over Q blocks: {extra_total}")
print("top 15 blocks by extra near-zero dims:")
for extra, b, nz, d, lam in rows[:15]:
    print(f"  block {b:3d} (m={metaQ[b]['m']}, nf={metaQ[b]['nf']}): "
          f"nearzero {nz}, forced {d}, EXTRA {extra}; "
          f"smallest eigs {np.round(lam[:min(4, len(lam))], 8)}")
print("R blocks:")
for b, R in enumerate(Rp):
    lam = np.linalg.eigvalsh((R + R.T) / 2)
    nz = int((lam < TH).sum())
    print(f"  R block {b:2d} (m'={pl['meta'][b]['m']}): nearzero {nz}, "
          f"forced {len(Kr[b])}, eigs<1e-3: {np.round(lam[lam < 1e-3], 7)}")

# ---------------------------------------------------------------- (e) equality graphs
print("\n=== the 22 complete multipartite graphs and the active set ===")


def partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for p in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - p, p):
            yield (p,) + rest


multi_idx = {}
for lam in partitions(8):
    # complete multipartite with part sizes lam: edge iff different parts
    part_of = []
    for i, s in enumerate(lam):
        part_of += [i] * s
    mask = 0
    for t, (a, b) in enumerate(n8lib.PAIRS):
        if part_of[a] != part_of[b]:
            mask |= 1 << t
    idx = cl.classify(mask)
    multi_idx[lam] = idx
    print(f"  K_{lam}: H={idx:5d}, slack={slack[idx]:.3e}")

with open(common.os.path.join(common.DATA, "multipartite22.pkl"), "wb") as f:
    pickle.dump(multi_idx, f)

act = np.where(slack < 1e-6)[0]
mset = set(multi_idx.values())
print(f"\nnear-active (<1e-6): {len(act)}; of which multipartite: "
      f"{sum(1 for h in act if h in mset)}")
print("non-multipartite near-active graphs (idx, #edges, slack):")
for h in act:
    if h not in mset:
        ec = n8lib.mask_edge_count(cl.masks[h])
        print(f"  H={h:5d} e={ec:2d} slack={slack[h]:.3e}")
