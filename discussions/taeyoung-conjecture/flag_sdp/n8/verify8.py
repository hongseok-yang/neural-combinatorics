"""
verify8.py
==========
Step 5: INDEPENDENT re-verification of a saved N=8 certificate (does not
trust the solver's reported objective).

Checks, for result_N8_<which>_<solver>.pkl:
  1. every projected Q_b is PSD:  min eig >= -1e-12 (they are exact
     eigenvalue-clipped projections, so this is ~0 by construction; we
     re-verify from the saved matrices).
  2. per-graph slacks recomputed from the sparse tables:
        slack[H] = coef[H] - sum_b <Qproj_b, M_b(H)>,
     certified bound  c_cert = min_H slack[H]   (uses sum_H p(H,W) = 1 and the
     exactly-validated Gram-PSD property of the unconditional tables).
  3. spot check on random step graphons via scripts/core.py:
        Delta2(W) >= c_cert - 1e-9.
  4. re-verify the graphon-averaged identity on exact pvecs (0/1 and const-p
     graphons):  Delta2(W) - c_cert = <Q,Gram(W)> + AvgSlack(W) with both
     terms >= -1e-12  (the full averaging-identity check).
"""
import os, sys, pickle
import numpy as np

import n8lib
import build_tables as bt
from n8lib import DATA

sys.path.insert(0, os.path.join(os.path.dirname(n8lib.FLAGSDP), "scripts"))
import core


def tri_of(Q):
    nf = Q.shape[0]
    tri = np.empty(nf * (nf + 1) // 2)
    for j in range(nf):
        for i in range(j + 1):
            tri[bt.TRI(i, j)] = Q[i, j]
    return tri


def gram_of(pv, Sb, nf):
    v = pv @ Sb
    G = np.zeros((nf, nf))
    for j in range(nf):
        for i in range(j + 1):
            k = bt.TRI(i, j)
            if i == j:
                G[i, i] = v[k]
            else:
                G[i, j] = G[j, i] = v[k] / 2.0
    return G


def main(which, solver):
    cl = n8lib.enumerate8(verbose=False)
    coef = np.load(os.path.join(DATA, "coef_delta2_N8.npy"))
    fn = os.path.join(DATA, f"result_N8_{which}_{solver}.pkl")
    with open(fn, "rb") as f:
        res = pickle.load(f)
    S = []
    if which in ("m0m2", "m0m2m4", "m0m2m4m6"):
        S += bt.build("m0m2", cl, verbose=False)["S"]
    if which in ("m4", "m0m2m4", "m0m2m4m6"):
        S += bt.build("m4", cl, verbose=False)["S"]
    if which in ("m6", "m0m2m4m6"):
        S += bt.build("m6", cl, verbose=False)["S"]
    Qp = res["Qproj"]
    assert len(Qp) == len(S)
    # 1. PSD
    mineig = min(np.linalg.eigvalsh((Q + Q.T) / 2).min() for Q in Qp)
    print(f"1. min eig over Q blocks: {mineig:.3e}")
    assert mineig >= -1e-12
    # 2. slacks
    total = np.zeros(len(coef))
    for Sb, Q in zip(S, Qp):
        total += Sb @ tri_of((Q + Q.T) / 2)
    slack = coef - total
    c_cert = float(slack.min())
    nneg = int((slack < -1e-9).sum())
    print(f"2. recomputed per-graph slacks: min = {c_cert:.6e} "
          f"(saved c_certified = {res['c_certified']:.6e}), "
          f"#slacks < -1e-9 relative to it: {nneg}")
    # 3. spot check on random step graphons
    rng = np.random.default_rng(0)
    worst = np.inf
    for _ in range(200):
        nb = int(rng.integers(2, 6))
        w = rng.random(nb); w /= w.sum()
        M = rng.random((nb, nb)); M = (M + M.T) / 2
        worst = min(worst, core.delta2(w, M) - c_cert)
    print(f"3. spot check min over 200 random step graphons of "
          f"Delta2(W) - c_cert = {worst:.6e} (must be >= -1e-9)")
    assert worst >= -1e-9
    # 4. full averaging identity on exact pvecs
    rng = np.random.default_rng(5)
    pvecs = []
    for tr in range(3):
        nb = int(rng.integers(3, 5))
        w = rng.random(nb); w /= w.sum()
        M01 = (rng.random((nb, nb)) < 0.55).astype(float)
        M01 = np.triu(M01) + np.triu(M01, 1).T
        pvecs.append((f"01 nb={nb}", (w, M01), n8lib.pvec_01_stepgraphon(w, M01, cl)))
    lc = n8lib.labeled_counts(cl)
    for p in [0.62, 0.85]:
        pvecs.append((f"const {p}", (np.array([1.0]), np.array([[p]])),
                      n8lib.pvec_const(p, cl, lc)))
    ok = True
    for name, (w, M), pv in pvecs:
        d2 = core.delta2(w, M)
        gram_term = 0.0
        for Sb, Q in zip(S, Qp):
            G = gram_of(pv, Sb, Q.shape[0])
            gram_term += float(np.sum(Q * G))
        avgslack = float(pv @ slack)
        # exact identity: Delta2(W) = <Q,Gram(W)> + AvgSlack(W); the bound
        # follows from <Q,Gram> >= 0 (Gram PSD, Q PSD) and AvgSlack >= c_cert
        # (slack >= c_cert pointwise, sum pv = 1).
        ident = d2 - gram_term - avgslack
        print(f"4. [{name}] Delta2={d2:.8f} <Q,Gram>={gram_term:.3e} "
              f"AvgSlack={avgslack:.3e} identity residual={ident:.2e} "
              f"(need <Q,Gram> >= -1e-12, AvgSlack >= c_cert - 1e-12)")
        ok = ok and gram_term >= -1e-12 and avgslack >= c_cert - 1e-12 \
            and abs(ident) < 1e-9
    assert ok
    print(f"\nVERIFIED: Delta2(W) >= {c_cert:.6e} for ALL graphons "
          f"(numerical certificate; rational rounding still needed for a formal proof)")
    return c_cert


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "m0m2",
         sys.argv[2] if len(sys.argv) > 2 else "CLARABEL")
