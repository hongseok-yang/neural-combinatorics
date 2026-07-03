"""
dual_ceiling.py
===============
Rigorous UPPER bound (ceiling) on the optimum of the N=8 flag SDP, from the
SCS dual iterate.  The dual of

    max c  s.t. coef - c - sum_b <Q_b, M_b(H)> >= 0, Q_b PSD

is   min_p  p.coef   s.t.  p >= 0, sum p = 1,  G_b(p) := sum_H p_H M_b(H) PSD.

Any FEASIBLE dual p gives: SDP optimum <= p.coef.  We take p = y[:nH] from
the SCS state, clip/normalize, and repair small PSD violations by mixing with
the exactly-feasible dual point p(H, W=const 1/2) (whose Gram blocks are PD):
    p_mix = (1-eps) p + eps p_G(1/2).
G_b is linear in p, so G_b(p_mix) = (1-eps)G_b(p) + eps G_b(p_half); choosing
eps with  eps * lammin_b(half) >= (1-eps) |min(0, lammin_b(p))|  for all b
makes every block PSD, giving the rigorous ceiling  p_mix.coef.

Usage: python3 dual_ceiling.py m0m2m4m6
"""
import os, sys, pickle
import numpy as np

import n8lib
import build_tables as bt
import solve8
from n8lib import DATA


def gram_blocks(pv, S, nfs):
    out = []
    for Sb, nf in zip(S, nfs):
        v = pv @ Sb
        G = np.zeros((nf, nf))
        for j in range(nf):
            for i in range(j + 1):
                k = bt.TRI(i, j)
                if i == j:
                    G[i, i] = v[k]
                else:
                    G[i, j] = G[j, i] = v[k] / 2.0
        out.append(G)
    return out


def main(which="m0m2m4m6"):
    cl, coef, S, meta = solve8.load_blocks(which)
    nfs = [b["nf"] for b in meta]
    nH = len(coef)
    with open(os.path.join(DATA, f"scs_state_{which}.pkl"), "rb") as f:
        st = pickle.load(f)
    y = st["warm"]["y"]
    p = np.clip(np.asarray(y[:nH], dtype=float), 0.0, None)
    print(f"dual iterate: sum y_top = {p.sum():.8f} (should be ~1), "
          f"neg clipped mass = {np.clip(y[:nH], None, 0).sum():.2e}")
    p /= p.sum()
    raw_val = float(p @ coef)
    G = gram_blocks(p, S, nfs)
    lam = np.array([np.linalg.eigvalsh((g + g.T) / 2).min() for g in G])
    print(f"dual value (unrepaired) = {raw_val:.6e}; "
          f"worst block min-eig = {lam.min():.3e}")
    # reference dual point: rich MIXTURE of graphon moment vectors
    lc = n8lib.labeled_counts(cl)
    ph = np.zeros(nH)
    for q_ in [0.3, 0.5, 0.62, 0.8]:
        ph += n8lib.pvec_const(q_, cl, lc)
    rng = np.random.default_rng(11)
    for _ in range(4):
        nb = int(rng.integers(3, 5))
        w = rng.random(nb); w /= w.sum()
        M01 = (rng.random((nb, nb)) < 0.55).astype(float)
        M01 = np.triu(M01) + np.triu(M01, 1).T
        ph += n8lib.pvec_01_stepgraphon(w, M01, cl)
    ph /= ph.sum()
    Gh = gram_blocks(ph, S, nfs)
    lamh = np.array([np.linalg.eigvalsh((g + g.T) / 2).min() for g in Gh])
    print(f"reference mixture: min block eig = {lamh.min():.3e}, "
          f"value = {float(ph @ coef):.6e}")
    if lamh.min() > 0:
        need = np.clip(-lam, 0.0, None)
        ratios = need / (need + lamh)          # eps >= ratio per block
        eps = float(ratios.max())
        p_mix = (1 - eps) * p + eps * ph
        val = float(p_mix @ coef)
        Gm = gram_blocks(p_mix, S, nfs)
        lammix = np.array([np.linalg.eigvalsh((g + g.T) / 2).min()
                           for g in Gm])
        print(f"eps = {eps:.3e};  mixed min block eig = {lammix.min():.3e}")
        print(f"RIGOROUS CEILING on this SDP's certifiable bound: {val:.6e}")
    else:
        # graphon Grams are singular at this level (linear flag relations):
        # no PD reference exists.  Check whether the dual violation lives in
        # the common (reference) kernel; report the honest near-feasible value.
        val = None
        for b in range(len(nfs)):
            Gs = (G[b] + G[b].T) / 2
            w_, V_ = np.linalg.eigh(Gs)
            if w_[0] > -1e-12:
                continue
            v = V_[:, 0]
            # component of v inside the reference kernel
            wh, Vh = np.linalg.eigh((Gh[b] + Gh[b].T) / 2)
            K = Vh[:, wh < 1e-12]
            incomp = np.linalg.norm(v - K @ (K.T @ v))
            print(f"  block {b}: viol eig {w_[0]:.2e}, |v - proj_K v| = "
                  f"{incomp:.3e} (0 => violation inside flag-relation kernel)")
        print(f"NEAR-FEASIBLE dual value (ceiling up to {abs(lam.min()):.1e} "
              f"infeasibility): {raw_val:.6e}")
    # top-mass graphs in the dual measure (the SDP's hardest graphs)
    top = np.argsort(-p)[:12]
    print("top dual-mass graphs (idx, mass, coef, edges):")
    for i in top:
        m = cl.masks[int(i)]
        print(f"  #{i}: p={p[int(i)]:.4f} coef={coef[int(i)]:+.6f} "
              f"e={n8lib.mask_edge_count(m)}")
    return val


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "m0m2m4m6")
