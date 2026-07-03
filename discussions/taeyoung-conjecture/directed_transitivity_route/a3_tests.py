"""
A3: covering-form tests.

Setup (all step-graphon exact linear algebra):
  beta-cycle measure: C5 homs weighted prod W(x_i,x_{i+1}); z uniform.
  S_z = positions i with x_i in complement-neighborhood of z (weight U(z,x_i)).
  h(S) = # covered C5-edges = 2|S| - e(S).
  Target:  E[h(S_z)] <= 10 q   (exactly Delta2 >= 0, verified).

Quantities per graphon:
  Eh      = E[h]                    (needs <= 10q)
  E2S     = 2 E|S| = 10 * bbar,  bbar = int ubar R / Z  (cycle-biased compl.deg)
  Ee      = E[e(S)] = 5 E_cycedge[codeg_U]
  Ehinge  = E[(2|S|-5)^+]           (pointwise e(S) >= (2|S|-5)^+ on C5)
  TEST-H:  Ehinge >= 10(bbar - q)?  (sufficient combinatorial inequality using
           only the distribution of |S_z|; implies target since
           Eh = 2E|S| - Ee <= 2E|S| - Ehinge)
Computation of |S_z| distribution: for fixed z, positions are the 5 cycle
slots; P[|S_z|=s] requires the joint law of (1_{x_i in S_z})_i under the cycle
measure = transfer-matrix computation with generating variable per slot:
  use transfer matrices A_t(x,y) = W(x,y) with slot weights (t*U(z,x) + (1-U(z,x)))
  polynomial in t: coefficient extraction via evaluating at 6 points.
Step graphon: slot weight matrix diag over blocks.
"""
import sys
sys.path.insert(0, "/private/tmp/cancel")
import numpy as np
from itertools import combinations
from scipy.optimize import minimize
from frame import F_data, make_families, Tpow

def S_distribution(w, M, z):
    """Return P[|S_z| = s], s=0..5 under cycle measure (unnormalized by Z^-1),
    i.e. vector of Z_s with sum_s Z_s = Z = t(C5). Uses generating function in t
    evaluated at 6 nodes + Vandermonde solve."""
    n = len(w)
    D = np.diag(w)
    U = 1.0 - M
    uz = U[z]                       # U(z,x) for block x
    ts = np.arange(6, dtype=float)
    vals = []
    for t in ts:
        g = 1.0 + (t - 1.0) * uz    # slot weight: (1-u) + t*u  per unit mass
        # cycle with 5 slots: trace( (G M D)^5 ) with G=diag(g) acting on mass
        GMD = (g[:, None] * M) @ D  # weight attaches to slot vertex x_i
        vals.append(np.trace(np.linalg.matrix_power(GMD, 5)))
    V = np.vander(ts, 6, increasing=True)
    Zs = np.linalg.solve(V, np.array(vals))
    return Zs                        # Z_s, sum = t(C5)

def covering_stats(w, M):
    w = np.asarray(w, float); M = np.asarray(M, float)
    dat = F_data(w, M)
    Z = dat["Z"]
    if Z <= 1e-14:
        return None
    n = len(w)
    D = np.diag(w)
    T5 = Tpow(M, D, 5)
    R = np.diag(T5)                  # R(x) = T5(x,x)
    ubar = 1.0 - dat["d"]
    q = 1.0 - dat["p"]
    bbar = float(np.sum(w * ubar * R)) / Z
    # distribution of |S_z| averaged over z
    Zs_avg = np.zeros(6)
    for z in range(n):
        Zs_avg += w[z] * S_distribution(w, M, z)
    P = Zs_avg / Z                   # P[|S|=s], averaged over z
    s = np.arange(6)
    E2S = float(np.sum(2 * s * P))
    Ehinge = float(np.sum(np.maximum(2 * s - 5, 0) * P))
    # Eh from F: Eh = (2E|S| - Ee) and Delta2 = q*... use F: Eh = 10q - avgF*5/Z?
    # F(z)/Z = 2u(z) - Pr[covered]; Pr[covered] = E_cyc[h]/5. So
    # E_z Pr[covered] = 2q - Delta2/Z; Eh = 5*(2q - Delta2/Z) = 10q - 5 Delta2/Z.
    Eh = 10 * q - 5 * dat["Delta2"] / Z
    Ee = E2S - Eh
    slackH = Ehinge - 10 * (bbar - q)     # want >= 0 (TEST-H)
    # consistency: 2E|S| should equal 10*bbar
    cons = abs(E2S - 10 * bbar)
    return dict(q=q, p=dat["p"], Z=Z, bbar=bbar, Eh=Eh, E2S=E2S, Ee=Ee,
                Ehinge=Ehinge, slackH=slackH, cons=cons, P=P,
                Delta2=dat["Delta2"])

def main():
    rng = np.random.default_rng(9)
    fams = make_families(rng, 300)
    print("=== consistency + TEST-H over families ===")
    worst_cons, min_slackH = 0.0, (np.inf, None)
    for (w, M) in fams:
        st = covering_stats(w, M)
        if st is None: continue
        worst_cons = max(worst_cons, st["cons"])
        if st["slackH"] < min_slackH[0]:
            min_slackH = (st["slackH"], (w, M, st))
    print(f"max |2E|S| - 10 bbar| consistency = {worst_cons:.2e}")
    print(f"min TEST-H slack over families    = {min_slackH[0]:.6f}")
    if min_slackH[1]:
        w, M, st = min_slackH[1]
        print(f"  at p={st['p']:.4f}, Delta2={st['Delta2']:.4e}, bbar-q={st['bbar']-st['q']:.4e}")
        print(f"  P(|S|)={np.round(st['P'],4)}")

    print("=== adversarial: minimize TEST-H slack ===")
    best = (np.inf, None)
    for _ in range(60):
        n = int(rng.integers(3, 7))
        iu = np.triu_indices(n)
        x0 = np.concatenate([rng.normal(0, 1, n), rng.normal(0, 2, (n*(n+1))//2)])
        def unpack(x):
            a = x[:n]; s = np.clip(x[n:], -30, 30)
            ww = np.exp(a - a.max()); ww /= ww.sum()
            Ms = np.zeros((n, n)); Ms[iu] = 1/(1+np.exp(-s))
            return ww, Ms + Ms.T - np.diag(np.diag(Ms))
        def obj(x):
            st = covering_stats(*unpack(x))
            if st is None: return 1.0
            return st["slackH"]
        res = minimize(obj, x0, method="Nelder-Mead",
                       options=dict(maxiter=3000, fatol=1e-12, xatol=1e-10))
        if res.fun < best[0]:
            best = (res.fun, unpack(res.x))
    print(f"adversarial min TEST-H slack = {best[0]:.6f}")
    if best[0] < -1e-9:
        w, M = best[1]
        st = covering_stats(w, M)
        print("VIOLATED. example:")
        print("  w =", np.round(w, 4), "\n  M =\n", np.round(M, 3))
        print("  p =", st["p"], " Delta2 =", st["Delta2"], " P =", np.round(st["P"], 4))

    print("=== random-free D>0 hunt: n<=5 with loops exhaustive; n=7,8 random ===")
    found = []
    for n in (4, 5):
        pairs = list(combinations(range(n), 2))
        nl = len(pairs) + n
        for mask in range(1 << nl):
            A = np.zeros((n, n))
            for e, (i, j) in enumerate(pairs):
                if (mask >> e) & 1: A[i, j] = A[j, i] = 1
            for v in range(n):
                if (mask >> (len(pairs) + v)) & 1: A[v, v] = 1
            if A.sum() * 2 < n * n * 1:  # p<1/2 (note diagonal counts once)
                pass
            w = np.full(n, 1.0 / n)
            p = float(w @ A @ w)
            if p < 0.5: continue
            T5 = Tpow(A, np.diag(w), 5)
            Db = float(np.sum(w * (p - (A @ w)) * np.diag(T5)))
            if Db > 1e-12:
                found.append((n, mask, Db, p))
        print(f"  n={n} with loops: cumulative D>0 count = {len(found)}")
    for trial in range(200000):
        n = 7 if trial % 2 == 0 else 8
        A = (rng.random((n, n)) < rng.uniform(0.5, 0.95)).astype(float)
        A = np.triu(A, 1); A = A + A.T
        if rng.random() < 0.5:
            A += np.diag((rng.random(n) < 0.5).astype(float))
        w = np.full(n, 1.0 / n)
        p = float(w @ A @ w)
        if p < 0.5: continue
        T5 = Tpow(A, np.diag(w), 5)
        Db = float(np.sum(w * (p - (A @ w)) * np.diag(T5)))
        if Db > 1e-12:
            found.append((n, None, Db, p))
            print(f"  RANDOM-FREE D>0 found: n={n}, D={Db:.3e}, p={p:.4f}")
            print(A.astype(int))
            break
    if not any(f[3] >= 0.5 and f[2] > 0 for f in found):
        print("  no random-free D>0 with p>=1/2 found in search space")

if __name__ == "__main__":
    main()
