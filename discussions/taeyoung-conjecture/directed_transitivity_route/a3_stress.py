"""
Stress-test TEST-H:  E_{z,cyc}[min(2|S_z|,5)] <= 10 q   (sufficient for Delta2>=0).

1. exact values on the known counterexample structures (4-block, K7-minus, 5-vertex
   obstruction).
2. second-order local test around balanced T_k (k=3..6): slack(T_k + eps*H) for
   random symmetric H (kernel perturbations, signed where interior, one-sided at
   boundary -> use feasible directions) and mass perturbations; fit eps^2
   coefficient; report min.
3. big adversarial hunt with many restarts incl. near-T_k starts and larger n.
4. exhaustive random-free n=6 (equal blocks, no loops) check of min slack.
"""
import sys
sys.path.insert(0, "/private/tmp/cancel")
import numpy as np
from itertools import combinations
from scipy.optimize import minimize
from a3_tests import covering_stats
from frame import fam_counterexample4, fam_obstruction5

rng = np.random.default_rng(21)

def slack(w, M):
    st = covering_stats(w, M)
    if st is None: return None
    # TEST-H slack = 10q - E[min(2|S|,5)]
    s = np.arange(6)
    Emin = float(np.sum(np.minimum(2*s, 5) * st["P"]))
    return 10*st["q"] - Emin, st

print("=== known structures ===")
for name, (w, M) in [("4-block cex", fam_counterexample4()),
                     ("5-vertex obstruction", fam_obstruction5())]:
    sl, st = slack(w, M)
    print(f"{name}: TEST-H slack = {sl:.6f}, Delta2 = {st['Delta2']:.6f}, 5*Delta2/Z = {5*st['Delta2']/st['Z']:.6f}")
A = np.ones((7,7)) - np.eye(7); A[0,3]=A[3,0]=0
sl, st = slack(np.full(7,1/7), A)
print(f"K7-minus example: TEST-H slack = {sl:.6f}, Delta2 = {st['Delta2']:.6f}")

print("=== second-order at balanced T_k ===")
for k in (3, 4, 5, 6):
    M0 = 1.0 - np.eye(k); w0 = np.full(k, 1.0/k)
    worst = np.inf
    for trial in range(400):
        H = rng.uniform(-1, 1, (k, k)); H = (H + H.T)/2
        # feasible: off-diag at 1 can only decrease; diag at 0 can only increase
        Hoff = -np.abs(H) * (1 - np.eye(k))
        Hd = np.abs(np.diag(np.diag(H)))
        Hfeas = Hoff + Hd
        eta = rng.uniform(-1, 1, k); eta -= eta.mean()
        for eps in (1e-2, 3e-2):
            wp = w0 + eps*eta; wp = np.maximum(wp, 1e-9); wp /= wp.sum()
            Mp = np.clip(M0 + eps*Hfeas, 0, 1)
            out = slack(wp, Mp)
            if out is None: continue
            sl, st = out
            worst = min(worst, sl / eps**2)
    print(f"  k={k}: min slack/eps^2 over 400 feasible perturbations = {worst:.4f}")

print("=== adversarial hunt (near-T_k starts + random, n up to 8) ===")
best = (np.inf, None)
for trial in range(120):
    if trial % 3 == 0:
        k = int(rng.integers(3, 7)); n = k
        M0 = 1.0 - np.eye(k)
        x0m = np.log(M0 + 1e-3) - np.log(1 - M0 + 1e-3)
        iu = np.triu_indices(n)
        x0 = np.concatenate([rng.normal(0, 0.1, n), x0m[iu] + rng.normal(0, 0.5, len(iu[0]))])
    else:
        n = int(rng.integers(3, 9))
        iu = np.triu_indices(n)
        x0 = np.concatenate([rng.normal(0, 1, n), rng.normal(0, 2, (n*(n+1))//2)])
    def unpack(x):
        a = x[:n]; s = np.clip(x[n:], -30, 30)
        ww = np.exp(a - a.max()); ww /= ww.sum()
        Ms = np.zeros((n, n)); Ms[iu] = 1/(1+np.exp(-s))
        return ww, Ms + Ms.T - np.diag(np.diag(Ms))
    def obj(x):
        out = slack(*unpack(x))
        return 1.0 if out is None else out[0]
    res = minimize(obj, x0, method="Nelder-Mead",
                   options=dict(maxiter=4000, fatol=1e-13, xatol=1e-11))
    if res.fun < best[0]:
        best = (res.fun, unpack(res.x))
print(f"adversarial min TEST-H slack = {best[0]:.8f}")
if best[0] < -1e-8:
    w, M = best[1]
    print("VIOLATION:\n w =", np.round(w,4), "\n M =\n", np.round(M,3))

print("=== exhaustive random-free n=6 (no loops) ===")
n = 6
pairs = list(combinations(range(n), 2))
minsl, arg = np.inf, None
for mask in range(1 << len(pairs)):
    A = np.zeros((n, n))
    for e, (i, j) in enumerate(pairs):
        if (mask >> e) & 1: A[i, j] = A[j, i] = 1
    out = slack(np.full(n, 1.0/n), A)
    if out is None: continue
    if out[0] < minsl:
        minsl, arg = out[0], mask
print(f"min TEST-H slack over all n=6 graphs = {minsl:.8f} (mask {arg})")
