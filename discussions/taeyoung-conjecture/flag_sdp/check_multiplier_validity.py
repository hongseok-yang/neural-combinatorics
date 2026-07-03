"""
check_multiplier_validity.py
============================
CRITICAL CORRECTNESS CHECK on the (2p-1)-multiplier Delta2 certificate.

The multiplier SDP (run_delta2.py --mult) finds PSD Q_sigma, R_sigma and c such
that FOR EVERY 7-vertex graph H:

    slack_H := cvec[H] - c - <Q,M(H)> - (2 p_H - 1) <R,M(H)>  >= 0      (per-H)

where p_H = t_inj(K2,H).  verify_cert.py confirms this is feasible (0 negative
slacks, Q,R PSD to ~1e-11), and the SDP reports c = +3.6e-10.

Averaging the per-H identity against the induced densities p(H,W) (>=0, sum 1)
of ANY graphon W gives the EXACT identity

    Delta2(W) - c = <Q, Gram(W)> + T_mult(W) + AvgSlack(W),                (*)

    <Q,Gram(W)>  = sum_H p(H,W) <Q,M(H)>            >= 0   (Gram PSD, Q PSD)
    AvgSlack(W)  = sum_H p(H,W) slack_H             >= 0   (slacks >=0, weights >=0)
    T_mult(W)    = sum_H p(H,W) (2 p_H - 1) <R,M(H)>          <-- SIGN UNKNOWN

To conclude Delta2(W) >= c from (*) we NEED T_mult(W) >= 0.  The README's
justification "(2p-1)>=0 on p>=1/2 and R>=0 => term >=0" is WRONG: the scalar
(2 p_H - 1) is INSIDE the sum over H and changes sign across graphs H (sparse H
have p_H < 1/2 even when t(K2,W) >= 1/2), so T_mult(W) is NOT (2 t(K2,W)-1)
times a nonneg Gram.  It is the density of a degree-elevated quantum graph whose
sign is not controlled by t(K2,W) >= 1/2.

This script computes T_mult(W) EXACTLY (exact induced densities on step
graphons, sum_H p(H,W)=1 to machine precision) for several p>=1/2 graphons and
shows it is GENUINELY NEGATIVE -- hence the multiplier certificate does NOT
prove Delta2 >= 0.

Run:  python3 check_multiplier_validity.py
"""
import numpy as np, pickle, os
import run_delta2 as R
from fast_pH import precompute, pH_vector
import core

N = 7
graphs = R.cached_graphs(N)
pvec = R.cached_pvec(N, graphs)
out = pickle.load(open(os.path.join(R.DATA, "result_N7_multTrue_CLARABEL.pkl"), "rb"))
c = out["c"]; Qs = out["Q"]; Rs = out["R"]
blocks = [R.cached_block(N, m, edges, graphs) for (m, edges) in R.TYPE_SPECS_N7]

Rvals = np.zeros(len(graphs)); Qvals = np.zeros(len(graphs))
for Rr, blk in zip(Rs, blocks):
    Rvals += np.array([float(np.sum(Rr * blk["Mtabs"][h])) for h in range(len(graphs))])
for Q, blk in zip(Qs, blocks):
    Qvals += np.array([float(np.sum(Q * blk["Mtabs"][h])) for h in range(len(graphs))])
gval = (2 * pvec - 1) * Rvals

print("precomputing exact induced-density orbits (7! x 1044) ...", flush=True)
triu, orbits = precompute(graphs, N)
print("done.\n", flush=True)

rng = np.random.default_rng(2)
worst = np.inf
tested = 0
print(f"solver-reported c = {c:.3e}")
print("EXACT T_mult(W) on p>=1/2 graphons (sum_pH must be 1.0):\n")
for trial in range(60):
    nb = int(rng.integers(2, 5))
    w = rng.random(nb); w /= w.sum()
    M = rng.random((nb, nb)); M = (M + M.T) / 2
    p = core.edge_density(w, M)
    if p < 0.5:
        continue
    tested += 1
    pH = pH_vector(w, M, graphs, triu, orbits)
    Tm = float(np.sum(pH * gval))
    d2 = core.delta2(w, M)
    q = float(np.sum(pH * Qvals))
    worst = min(worst, Tm)
    flag = "  <-- NEGATIVE" if Tm < -1e-9 else ""
    print(f"  nb={nb} p={p:.4f} sum_pH={pH.sum():.6f}  T_mult={Tm:+.6e}  "
          f"Delta2={d2:.6e} <Q,Gram>={q:.6e}{flag}", flush=True)
    if tested >= 8:
        break

print(f"\nWORST EXACT T_mult over tested p>=1/2 graphons = {worst:+.6e}")
if worst < -1e-6:
    print("VERDICT: T_mult(W) < 0 on p>=1/2  =>  the (2p-1)-multiplier certificate")
    print("         does NOT prove Delta2 >= 0.  The SDP's c=+3.6e-10 is an artifact")
    print("         of per-graph feasibility with a sign-varying (2 p_H - 1) weight.")
else:
    print("T_mult stayed nonnegative on the tested set.")
