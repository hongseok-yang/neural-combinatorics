import sys
sys.path.insert(0, "/private/tmp/cancel")
import numpy as np
from a3_tests import covering_stats

rng = np.random.default_rng(33)
def slack(w, M):
    st = covering_stats(w, M)
    if st is None: return None
    s = np.arange(6)
    Emin = float(np.sum(np.minimum(2*s, 5) * st["P"]))
    return 10*st["q"] - Emin, st

# second-order at larger k
for k in (8, 10, 12):
    M0 = 1.0 - np.eye(k); w0 = np.full(k, 1.0/k)
    worst = np.inf
    for _ in range(200):
        H = rng.uniform(-1,1,(k,k)); H=(H+H.T)/2
        Hf = -np.abs(H)*(1-np.eye(k)) + np.abs(np.diag(np.diag(H)))
        eta = rng.uniform(-1,1,k); eta -= eta.mean()
        eps = 2e-2
        wp = np.maximum(w0+eps*eta,1e-9); wp/=wp.sum()
        Mp = np.clip(M0+eps*Hf,0,1)
        out = slack(wp,Mp)
        if out: worst = min(worst, out[0]/eps**2)
    print(f"k={k}: min slack/eps^2 = {worst:.4f}")

# random-free larger n + loops + weighted with loops
worstv = (np.inf, None)
for trial in range(4000):
    n = int(rng.integers(5, 11))
    A = (rng.random((n,n)) < rng.uniform(0.45, 0.95)).astype(float)
    A = np.triu(A,1); A = A+A.T
    if rng.random()<0.5: A += np.diag((rng.random(n)<0.5).astype(float))
    w = np.full(n,1.0/n)
    out = slack(w,A)
    if out and out[0] < worstv[0]: worstv = (out[0], (w,A))
print(f"random-free n=5..10 (+loops), 4000 samples: min slack = {worstv[0]:.8f}")
worstw = (np.inf, None)
for trial in range(4000):
    n = int(rng.integers(2, 7))
    w = rng.random(n)+0.05; w/=w.sum()
    A = rng.random((n,n)); A=(A+A.T)/2
    out = slack(w,A)
    if out and out[0] < worstw[0]: worstw = (out[0], (w,A))
print(f"weighted random, 4000 samples: min slack = {worstw[0]:.8f}")
# the weighted D>0 example
w = np.array([0.4509,0.4509,0.0982]); w/=w.sum()
M = np.array([[1,0,0.649],[0,1,0.649],[0.649,0.649,0]],float)
out = slack(w,M)
print("weighted D>0 example: slack =", out[0], " p =", out[1]["p"], " D-check bbar-q =", out[1]["bbar"]-out[1]["q"])
