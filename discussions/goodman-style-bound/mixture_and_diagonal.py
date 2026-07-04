#!/usr/bin/env python3
"""1) Verify the mixture-of-diagonals identity:
      Pcal_{m,r}(q; lam_1..lam_r) = E_{Lbar}[ Pcal_{m,r}(q; Lbar,...,Lbar) ]
   where Lbar = sum_j xi_j lam_j with (xi_1..xi_r) ~ Dirichlet(1,...,1).
   Check by exact quadrature for r=2 (xi ~ Uniform on simplex: Lbar = t*lam1+(1-t)*lam2,
   t ~ U[0,1]) and r=3 (density of (t1,t2): uniform on triangle).

2) Map the DIAGONAL landscape: for each (n, r) with n odd, find
      q*(n,r) = sup{ q : min_{l in [-1/2,1/2]} Ptilde(q,l) >= 0 }
   over a wide range including the mid-band r ~ n/2, plus record the minimizing l.

3) Verify the IBP lemma prediction: Ptilde >= 0 whenever l >= q + r/m (all q<=1/2).
"""
import numpy as np
from scipy.integrate import quad, dblquad

def geom(c, N): return c**np.arange(N+1)
def ser_mul(a, b, N): return np.convolve(a, b)[:N+1]
def coeff_prod(cs, n):
    out = np.zeros(n+1); out[0] = 1.0
    for c in cs: out = ser_mul(out, geom(c, n), n)
    return out[n]

def Pcal(m, r, q, lams):
    p = 1 - q; n = m - 2*r
    tW = coeff_prod([p]*r + [-l for l in lams], n)
    tU = coeff_prod([q]*r + list(lams), n)
    tP = coeff_prod([q]*(r+1) + list(lams), n-1) if n >= 1 else 0.0
    return (m/r)*(tW + tU) - tP

def Pdiag(m, r, q, l): return Pcal(m, r, q, [l]*r)

print("== 1) mixture-of-diagonals identity ==")
for (m, r, q, lams) in [(13, 2, 0.4, [0.5, -0.3]), (17, 2, 0.3, [0.11, 0.47]),
                        (11, 3, 0.45, [0.5, -0.5, 0.2]), (19, 3, 0.25, [-0.1, 0.33, 0.5])]:
    if r == 2:
        val, _ = quad(lambda t: Pdiag(m, r, q, t*lams[0] + (1-t)*lams[1]), 0, 1,
                      limit=200, epsabs=1e-13, epsrel=1e-13)
    else:
        # (t1,t2) uniform on {t1,t2>=0, t1+t2<=1}, density 2
        val, _ = dblquad(lambda t2, t1: 2*Pdiag(m, r, q,
                          t1*lams[0] + t2*lams[1] + (1-t1-t2)*lams[2]),
                         0, 1, 0, lambda t1: 1-t1, epsabs=1e-12, epsrel=1e-12)
    direct = Pcal(m, r, q, lams)
    print(f"  m={m} r={r} q={q} lam={lams}: direct={direct:.12e} mixture={val:.12e} "
          f"reldiff={(abs(direct-val)/max(1e-300,abs(direct))):.2e}")

print("== 2) diagonal landscape q*(n,r) (l-grid 4001 pts) ==")
lgrid = np.linspace(-0.5, 0.5, 4001)
def qstar_diag(n, r, tol=1e-4):
    m = n + 2*r
    def minP(q):
        return min(Pdiag(m, r, q, l) for l in lgrid)
    lo, hi = 0.0, 0.5
    if minP(0.5 - 1e-12) >= 0: return 0.5, None
    while hi - lo > tol:
        mid = (lo + hi)/2
        if minP(mid) >= 0: lo = mid
        else: hi = mid
    qs = lo
    # minimizing l just above threshold
    q_probe = min(0.5 - 1e-12, qs + 2*tol)
    vals = [Pdiag(m, r, q_probe, l) for l in lgrid]
    return qs, lgrid[int(np.argmin(vals))]

rows = []
for n in [3, 5, 7, 9, 13, 21, 31, 41, 61]:
    for r in sorted(set([1, 2, 3, max(1, n//6), max(1, n//4), max(1, n//3),
                         max(1, (n-1)//2 - 1), max(1, (n-1)//2), (n+1)//2, n, 2*n])):
        qs, larg = qstar_diag(n, r)
        tag = "PW(2r>=n)" if 2*r >= n else ""
        print(f"  n={n:3d} r={r:3d} (m={n+2*r:3d}): q*={qs:.4f}"
              + (f"  min-l={larg:+.3f}" if larg is not None else "  (>=0 on all q)") + f" {tag}",
              flush=True)

print("== 3) IBP-lemma region check: Ptilde >= 0 for l >= q + r/m ==")
bad = 0
rng = np.random.default_rng(1)
for _ in range(4000):
    n = int(rng.choice([3, 5, 9, 15, 25, 41]))
    r = int(rng.integers(1, n))
    m = n + 2*r
    q = rng.uniform(0, 0.5)
    lmin = q + r/m
    if lmin >= 0.5: continue
    l = rng.uniform(lmin, 0.5)
    v = Pdiag(m, r, q, l)
    if v < -1e-12:
        bad += 1
        print(f"  VIOLATION: n={n} r={r} q={q:.4f} l={l:.4f}: {v:.3e}")
print(f"  violations: {bad}")
