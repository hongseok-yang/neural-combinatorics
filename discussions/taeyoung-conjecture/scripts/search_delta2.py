"""
Falsification search for Delta_2(W) >= 0  (smoothed Goodman, C3 glued C5 along K2),
over n-block step graphons with p >= 1/2.

Parameterization for the optimizer:
  - block masses w via softmax of free vector u (n params), guarantees simplex.
  - matrix M via sigmoid of free symmetric entries (n(n+1)/2 params) -> in (0,1).
We minimize Delta_2 with a penalty enforcing p >= 1/2.
Also minimize Delta_2 / t(C5) (normalized) to avoid scaling-to-zero.

Many random restarts; SLSQP + L-BFGS-B.
"""
import numpy as np
from scipy.optimize import minimize
from core import densities

SEED0 = 12345


def unpack(theta, n):
    u = theta[:n]
    w = np.exp(u - u.max())
    w = w / w.sum()
    tri = theta[n:]
    M = np.zeros((n, n))
    idx = 0
    for i in range(n):
        for j in range(i, n):
            v = 1.0 / (1.0 + np.exp(-tri[idx]))
            M[i, j] = v
            M[j, i] = v
            idx += 1
    return w, M


def nparams(n):
    return n + n * (n + 1) // 2


def make_obj(n, normalized=False, pmin=0.5, pen=50.0):
    def obj(theta):
        w, M = unpack(theta, n)
        d = densities(w, M)
        p = d["p"]
        val = d["delta2"]
        if normalized:
            c5 = d["c5"]
            val = d["delta2"] / (c5 + 1e-12)
        # penalty for p < pmin (we want to stay on top branch)
        if p < pmin:
            val += pen * (pmin - p) ** 2 + pen * (pmin - p)
        return val
    return obj


def run(n, restarts=400, normalized=False, seed=SEED0, methods=("SLSQP", "L-BFGS-B")):
    rng = np.random.default_rng(seed)
    best = dict(val=np.inf)
    obj = make_obj(n, normalized=normalized)
    npar = nparams(n)
    for r in range(restarts):
        theta0 = rng.normal(0, 2.5, npar)
        for method in methods:
            try:
                res = minimize(obj, theta0, method=method,
                               options=dict(maxiter=500, ftol=1e-14)
                               if method == "SLSQP"
                               else dict(maxiter=500))
            except Exception:
                continue
            w, M = unpack(res.x, n)
            d = densities(w, M)
            if d["p"] < 0.5 - 1e-9:
                continue
            v = d["delta2"] / (d["c5"] + 1e-300) if normalized else d["delta2"]
            if v < best["val"]:
                best = dict(val=v, w=w.copy(), M=M.copy(),
                            p=d["p"], delta2=d["delta2"], c5=d["c5"])
    return best


if __name__ == "__main__":
    import sys
    norm = "--norm" in sys.argv
    label = "Delta_2/t(C5)" if norm else "Delta_2"
    print(f"=== Minimizing {label} over n-block step graphons, p>=1/2 ===")
    overall = dict(val=np.inf)
    for n in [2, 3, 4, 5, 6]:
        restarts = {2: 600, 3: 600, 4: 500, 5: 400, 6: 300}[n]
        b = run(n, restarts=restarts, normalized=norm, seed=SEED0 + n)
        print(f"\nn={n}: min {label} = {b['val']:.3e}")
        print(f"   p={b['p']:.6f}  delta2={b['delta2']:.6e}  t(C5)={b['c5']:.6e}")
        print(f"   w={np.round(b['w'],4)}")
        with np.printoptions(precision=4, suppress=True):
            print(f"   M=\n{b['M']}")
        if b["val"] < overall["val"]:
            overall = dict(b, n=n)
    print("\n========= OVERALL MIN =========")
    print(f"n={overall['n']}  min {label}={overall['val']:.3e}  delta2={overall['delta2']:.3e}  p={overall['p']:.6f}")
