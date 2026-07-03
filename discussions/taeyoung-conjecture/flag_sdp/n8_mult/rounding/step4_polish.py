"""
Step 4: float polish -- project the SCS iterate onto the conjectured optimal
face at c = 0:

    F = { (Q,R) :  Q_b, R_b PSD;   Q_b K_b = 0, R_b K_b = 0 (forced kernels);
                   slack[h] = 0 for h in E  (equality set);
                   slack[h] >= 0 for all other h },

by Dykstra-flavored alternating projections:
  (A) affine set {kernels + slack equalities on the working set W}, projected
      in one shot via the Gram matrix of kernel-projected constraint
      gradients (least-squares, pinv: the T_k averaging identities make the
      multipartite gradients linearly dependent -- that is expected);
  (B) PSD cones per block (eigenvalue clip).
The working set W starts as E (near-active graphs) and absorbs any other
constraint that goes negative.

If F is nonempty this converges (POCS on closed convex sets); the terminal
residual is the DECISIVE DIAGNOSTIC: stalling at ~1e-8 would mean the SDP
optimum is genuinely < 0 and no exact c=0 certificate exists at N=8.
"""
import os, sys, time, pickle, argparse
import numpy as np

import common, kernels
import multlib as ml

cl, coef, SQ, metaQ, pl, res = common.load_everything()
MultS = pl["MultS"]
metaR = pl["meta"]
nH = len(coef)
DATA = common.DATA

with open(os.path.join(DATA, "kernels.pkl"), "rb") as f:
    KK = pickle.load(f)
with open(os.path.join(DATA, "multipartite22.pkl"), "rb") as f:
    multi_idx = pickle.load(f)

nfsQ = [bm["nf"] for bm in metaQ]
nfsR = [bm["nf"] for bm in metaR]
NBQ, NBR = len(nfsQ), len(nfsR)

# ---- orthonormal kernel bases (float) per block
VQ = [None] * NBQ
for b, K in enumerate(KK["Kq"]):
    if K:
        V = kernels.to_float(K).T           # nf x d
        Qb, _ = np.linalg.qr(V)
        VQ[b] = Qb
VR = [None] * NBR
for b, K in enumerate(KK["Kr"]):
    if K:
        V = kernels.to_float(K).T
        Qb, _ = np.linalg.qr(V)
        VR[b] = Qb


def kproj_one(M, V):
    if V is None:
        return (M + M.T) / 2
    M = (M + M.T) / 2
    MV = M @ V
    M = M - MV @ V.T - V @ MV.T + V @ (V.T @ MV) @ V.T
    return (M + M.T) / 2


def kernel_project(Qs, Rs):
    return ([kproj_one(Q, VQ[b]) for b, Q in enumerate(Qs)],
            [kproj_one(R, VR[b]) for b, R in enumerate(Rs)])


def psd_clip(Ms):
    out = []
    for M in Ms:
        lam, U = np.linalg.eigh((M + M.T) / 2)
        out.append((U * np.clip(lam, 0.0, None)) @ U.T)
    return out


# ---- svec <-> mat helpers on our tri convention
def tri_to_mat(v, nf):
    return ml.tri_to_mat(np.asarray(v).ravel(), nf)


def mat_to_tri(M):
    return common.tri_of(M)          # tri[k]=M_ij (we use with S: S.tri gives
                                     # sum M_ij+M_ji off-diag => <Q,M(H)>)


def slacks(Qs, Rs):
    return common.slacks_float(coef, SQ, MultS, Qs, Rs)


# ---- constraint gradient machinery -----------------------------------------
# slack[h] = coef[h] - sum_b <Q_b, M_b(h)> - sum_b <R_b, Mult_b(h)>.
# Gradient wrt Q_b (sym inner product tr(AB)) is -M_b(h); we use the
# KERNEL-PROJECTED gradients so the affine step stays inside the kernel space.
def grad_mats(h):
    """list of (projected) gradient matrices per Q block and R block."""
    gQ = []
    for b in range(NBQ):
        M = tri_to_mat(SQ[b][h].toarray(), nfsQ[b])
        gQ.append(kproj_one(M, VQ[b]))
    gR = []
    for b in range(NBR):
        M = tri_to_mat(MultS[b][h], nfsR[b])
        gR.append(kproj_one(M, VR[b]))
    return gQ, gR


def dot_pair(g1, g2):
    return (sum(np.vdot(a, b) for a, b in zip(g1[0], g2[0]))
            + sum(np.vdot(a, b) for a, b in zip(g1[1], g2[1])))


class EqProjector:
    """Least-squares projection onto {slack[W]=0} within the kernel space."""

    def __init__(self, W):
        self.W = list(W)
        t0 = time.time()
        self.g = [grad_mats(h) for h in self.W]
        n = len(self.W)
        G = np.zeros((n, n))
        for i in range(n):
            for j in range(i + 1):
                G[i, j] = G[j, i] = dot_pair(self.g[i], self.g[j])
        self.G = G
        # pseudo-inverse with generous cutoff (identities => exact rank def.)
        self.Gpinv = np.linalg.pinv(G, rcond=1e-11)
        print(f"    EqProjector: |W|={n}, Gram built {time.time()-t0:.1f}s, "
              f"rank {np.linalg.matrix_rank(G, tol=1e-11 * G.max()):d}")

    def project(self, Qs, Rs, sl=None):
        if sl is None:
            sl = slacks(Qs, Rs)
        r = sl[self.W]                       # want slack -> 0
        mu = self.Gpinv @ r
        # slack changes by -sum_e mu_e <g_e, dQ>: with dQ = -sum mu g:
        # new slack = slack - sum_e' mu_e' G[e,e'] = slack - G mu = slack - r*
        for e, m in enumerate(mu):
            if m == 0.0:
                continue
            for b in range(NBQ):
                Qs[b] = Qs[b] + m * self.g[e][0][b]
            for b in range(NBR):
                Rs[b] = Rs[b] + m * self.g[e][1][b]
        return Qs, Rs


def run(maxit=400, tol=1e-13, eqset_th=1e-6, use_dykstra=True,
        refresh_live=True, save_tag="polished"):
    # start from the freshest checkpoint
    src = os.path.join(ml.DATA, "result_mult_m0m2m4m6_SCSchunk.pkl")
    if refresh_live and os.path.exists(src):
        with open(src, "rb") as f:
            live = pickle.load(f)
        print(f"live checkpoint: c_certified={live['c_certified']:.3e}")
        Qs = [np.array(M) for M in live["Qproj"]]
        Rs = [np.array(M) for M in live["Rproj"]]
    else:
        Qs = [np.array(M) for M in res["Qproj"]]
        Rs = [np.array(M) for M in res["Rproj"]]

    sl = slacks(Qs, Rs)
    W = sorted(set(np.where(sl < eqset_th)[0]).union(multi_idx.values()))
    print(f"working equality set: {len(W)} graphs")
    ep = EqProjector(W)

    # Dykstra corrections for the two "sets": affine (no correction needed --
    # affine projections need no Dykstra correction only for HYPERPLANES;
    # for affine SUBSPACES Dykstra correction is also unnecessary) and PSD
    # (correction needed).
    corrQ = [np.zeros_like(Q) for Q in Qs]
    corrR = [np.zeros_like(R) for R in Rs]

    hist = []
    t0 = time.time()
    for it in range(maxit):
        # ---- affine projection: kernels then equalities (their composition
        # is exact projection onto the intersection because the equality
        # gradients are already kernel-projected: eq-step preserves kernels)
        Qs, Rs = kernel_project(Qs, Rs)
        sl = slacks(Qs, Rs)
        # absorb newly violated constraints into W
        bad = np.where(sl < -1e-12)[0]
        newW = [h for h in bad if h not in set(W)]
        if newW:
            W = sorted(set(W).union(newW))
            print(f"  it{it}: absorbing {len(newW)} newly-violated graphs "
                  f"(|W|={len(W)})")
            ep = EqProjector(W)
        Qs, Rs = ep.project(Qs, Rs, sl)

        # ---- PSD projection with Dykstra correction
        if use_dykstra:
            Yq = [Q + C for Q, C in zip(Qs, corrQ)]
            Yr = [R + C for R, C in zip(Rs, corrR)]
            Pq = psd_clip(Yq)
            Pr = psd_clip(Yr)
            corrQ = [Y - P for Y, P in zip(Yq, Pq)]
            corrR = [Y - P for Y, P in zip(Yr, Pr)]
            Qs, Rs = Pq, Pr
        else:
            Qs = psd_clip(Qs)
            Rs = psd_clip(Rs)

        # ---- diagnostics
        if it % 5 == 0 or it == maxit - 1:
            Qk, Rk = kernel_project(Qs, Rs)
            sl = slacks(Qk, Rk)
            slW = np.abs(sl[W]).max()
            mn = sl.min()
            mev = min(np.linalg.eigvalsh(M).min() for M in Qk + Rk)
            hist.append((it, slW, mn, mev))
            print(f"  it{it:4d}: max|slack[W]|={slW:.3e} min slack={mn:.3e} "
                  f"min eig={mev:.3e}  ({time.time()-t0:.0f}s)", flush=True)
            if slW < tol and mn > -tol and mev > -1e-14:
                print("  CONVERGED")
                break

    Qs, Rs = kernel_project(Qs, Rs)
    Qs = psd_clip(Qs)      # final iterate: exactly PSD, kernels to ~1e-15
    Rs = psd_clip(Rs)
    sl = slacks(Qs, Rs)
    print(f"final: min slack {sl.min():.3e}, max|slack[W]| "
          f"{np.abs(sl[W]).max():.3e}")
    with open(os.path.join(DATA, f"{save_tag}.pkl"), "wb") as f:
        pickle.dump(dict(Q=Qs, R=Rs, W=W, slack=sl, hist=hist), f)
    print(f"saved {save_tag}.pkl")
    return Qs, Rs, W, sl


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--maxit", type=int, default=400)
    ap.add_argument("--tag", default="polished")
    a = ap.parse_args()
    run(maxit=a.maxit, save_tag=a.tag)
