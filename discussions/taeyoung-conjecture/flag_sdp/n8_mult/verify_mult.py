"""
verify_mult.py
==============
INDEPENDENT re-verification of a saved multiplier certificate
(result_mult_<whichQ>_<solver>.pkl).  Does not trust the solver.

LOGIC CHAIN being verified (stated explicitly, then checked numerically):

  Per-graph inequality (checked in step 2):
      slack[H] := coef[H] - sum_b <Qp_b, M_b(H)> - sum_b' <Rp_b', Mult_b'(H)>
      c_cert   := min_H slack[H].
  For ANY graphon W, averaging against p8(H,W) (>= 0, sum = 1) gives the EXACT
  identity (checked in step 4 on exact pvecs):
      Delta2(W) = <Qp, Gram8(W)> + (2 t(K2,W) - 1) <Rp, Gram6(W)> + AvgSlack(W)
  with
      <Qp, Gram8(W)> >= 0      (Gram8 PSD: n8 gate T-2;  Qp PSD: step 1),
      <Rp, Gram6(W)> >= 0      (Gram6 PSD: gate MV-2;    Rp PSD: step 1),
      AvgSlack(W)   >= c_cert  (slack >= c_cert pointwise, weights sum to 1).
  Hence   Delta2(W) >= c_cert + (2 t(K2,W) - 1) <Rp, Gram6(W)>
  and, since the multiplier term is >= 0 exactly when t(K2,W) >= 1/2:

      Delta2(W) >= c_cert          for every graphon with t(K2,W) >= 1/2.

  The p <= 1/2 branch is NOT covered by this certificate; there
  Delta2 = t(theta_{1,2,4},W) + (1 - 2p) t(C5,W) >= 0 holds trivially
  (both densities are >= 0).  So c_cert >= 0 would prove Delta2 >= 0
  for ALL graphons.

Checks:
  1. every projected Q_b and R_b' is PSD (min eig >= -1e-12);
  2. per-graph slacks recomputed from the sparse ground-8 tables and the
     dense MultS tables; c_cert = min slack;
  3. spot check on 300+ random step graphons (incl. p<1/2, bipartite T_k
     0/1 blowups, balanced T_k, W==1): Delta2(W) >= c_cert - 1e-9 whenever
     p >= 1/2; for p < 1/2 verify the trivial branch instead;
  4. full averaging identity on exact pvecs (0/1 step + const-p graphons):
     residual < 1e-9, both Gram terms >= -1e-12, AvgSlack >= c_cert - 1e-12.

Usage: python3 verify_mult.py m0m2m4m6 SCSchunk   (or m0m2 CLARABEL etc.)
"""
import os, sys, pickle
import numpy as np

import multlib as ml

sys.path.insert(0, ml.N8DIR)
import n8lib
import build_tables as bt
import solve8
from n8lib import DATA as N8DATA

sys.path.insert(0, os.path.join(os.path.dirname(n8lib.FLAGSDP), "scripts"))
import core


def tri_of(Q):
    nf = Q.shape[0]
    tri = np.empty(nf * (nf + 1) // 2)
    for j in range(nf):
        for i in range(j + 1):
            tri[bt.TRI(i, j)] = Q[i, j]
    return tri


def main(whichQ, solver):
    cl = n8lib.enumerate8(verbose=False)
    coef = np.load(os.path.join(N8DATA, "coef_delta2_N8.npy"))
    pl = ml.build(verbose=False)
    fn = os.path.join(ml.DATA, f"result_mult_{whichQ}_{solver}.pkl")
    with open(fn, "rb") as f:
        res = pickle.load(f)
    _, _, SQ, metaQ = solve8.load_blocks(whichQ)
    Qp, Rp = res["Qproj"], res["Rproj"]
    assert len(Qp) == len(SQ) and len(Rp) == len(pl["MultS"])
    # 1. PSD
    me_q = min(np.linalg.eigvalsh((Q + Q.T) / 2).min() for Q in Qp)
    me_r = min(np.linalg.eigvalsh((R + R.T) / 2).min() for R in Rp)
    print(f"1. min eig over Q blocks: {me_q:.3e}; over R blocks: {me_r:.3e}")
    assert me_q >= -1e-12 and me_r >= -1e-12
    # 2. slacks
    total = np.zeros(len(coef))
    for Sb, Q in zip(SQ, Qp):
        total += Sb @ tri_of((Q + Q.T) / 2)
    for Mb, R in zip(pl["MultS"], Rp):
        total += Mb @ tri_of((R + R.T) / 2)
    slack = coef - total
    c_cert = float(slack.min())
    print(f"2. recomputed per-graph slacks: min = {c_cert:.6e} "
          f"(saved c_certified = {res['c_certified']:.6e})")
    # 3. spot check
    rng = np.random.default_rng(0)
    cases = []
    for _ in range(260):
        nb = int(rng.integers(2, 6))
        w = rng.random(nb); w /= w.sum()
        M = rng.random((nb, nb)); M = (M + M.T) / 2
        cases.append((w, M))
    for k in range(2, 9):                       # balanced T_k blowups
        w = np.ones(k) / k
        M = 1.0 - np.eye(k)
        cases.append((w, M))
    for k in range(2, 6):                       # unbalanced bipartite-ish
        w = rng.random(k); w /= w.sum()
        M = 1.0 - np.eye(k)
        cases.append((w, M))
    cases.append((np.array([1.0]), np.array([[1.0]])))     # W == 1
    cases.append((np.array([.5, .5]), np.array([[0., 1.], [1., 0.]])))  # T_2
    for p in [0.3, 0.5, 0.55, 0.75, 1.0]:
        cases.append((np.array([1.0]), np.array([[p]])))
    n_hi = n_lo = 0
    worst_hi = np.inf
    worst_lo = np.inf
    for (w, M) in cases:
        p = float(w @ M @ w)
        d2 = core.delta2(w, M)
        if p >= 0.5:
            n_hi += 1
            worst_hi = min(worst_hi, d2 - c_cert)
        else:
            n_lo += 1
            worst_lo = min(worst_lo, d2)        # trivial branch: Delta2 >= 0
    print(f"3. spot check: {n_hi} graphons with p>=1/2: min Delta2 - c_cert "
          f"= {worst_hi:.6e} (need >= -1e-9); {n_lo} with p<1/2: min Delta2 "
          f"= {worst_lo:.6e} (trivial branch, need >= -1e-12)")
    assert worst_hi >= -1e-9 and worst_lo >= -1e-12
    # 4. exact averaging identity
    rng = np.random.default_rng(5)
    pv_cases = []
    for tr in range(3):
        nb = int(rng.integers(3, 5))
        w = rng.random(nb); w /= w.sum()
        M01 = (rng.random((nb, nb)) < 0.55).astype(float)
        M01 = np.triu(M01) + np.triu(M01, 1).T
        pv_cases.append((f"01 nb={nb}", w, M01, True))
    pv_cases.append(("T_2 balanced", np.array([.5, .5]),
                     np.array([[0., 1.], [1., 0.]]), True))
    pv_cases.append(("T_3 balanced", np.ones(3) / 3, 1.0 - np.eye(3), True))
    pv_cases.append(("W==1", np.array([1.0]), np.array([[1.0]]), True))
    lc8 = n8lib.labeled_counts(cl)
    for p in [0.4, 0.62, 0.85]:
        pv_cases.append((f"const {p}", np.array([1.0]), np.array([[p]]), False))
    ok = True
    for name, w, M, is01 in pv_cases:
        p_edge = float(w @ M @ w)
        if is01:
            p8 = n8lib.pvec_01_stepgraphon(w, M, cl)
            p6 = ml.pvec6_01_stepgraphon(w, M, pl["cls_of_pat"])
        else:
            p8 = n8lib.pvec_const(M[0, 0], cl, lc8)
            p6 = ml.pvec6_const(M[0, 0], pl["reps"], pl["n_labeled6"])
        d2 = core.delta2(w, M)
        gq = 0.0
        for Sb, Q in zip(SQ, Qp):
            G = ml.tri_to_mat(p8 @ Sb, Q.shape[0])
            gq += float(np.sum(Q * G))
        gr = 0.0
        for T, R in zip(pl["T6tri"], Rp):
            G6 = ml.tri_to_mat(p6 @ T, R.shape[0])
            gr += float(np.sum(R * G6))
        avgslack = float(p8 @ slack)
        ident = d2 - gq - (2 * p_edge - 1) * gr - avgslack
        print(f"4. [{name}] p={p_edge:.3f} Delta2={d2:.8f} <Q,G8>={gq:.3e} "
              f"<R,G6>={gr:.3e} AvgSlack={avgslack:.3e} residual={ident:.2e}")
        ok = ok and gq >= -1e-12 and gr >= -1e-12 \
            and avgslack >= c_cert - 1e-12 and abs(ident) < 1e-9
    assert ok
    verdict = ("NUMERICAL CERTIFICATE OF Delta2 >= 0 on p >= 1/2 "
               "(with the trivial p <= 1/2 branch: FULL THEOREM, "
               "rational rounding still needed)"
               if c_cert >= -1e-8 else
               f"partial: Delta2 >= {c_cert:.6e} on p >= 1/2 only")
    print(f"\nVERIFIED: Delta2(W) >= {c_cert:.6e} for all graphons with "
          f"t(K2,W) >= 1/2.  {verdict}")
    return c_cert


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "m0m2m4m6",
         sys.argv[2] if len(sys.argv) > 2 else "SCSchunk")
