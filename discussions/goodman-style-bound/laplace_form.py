#!/usr/bin/env python3
"""Test the u-line form and the stronger Laplace/exponential-kernel form.

u-line form (EXACT equivalent of the diagonal inequality, l>0):
  I(l,q) = int_0^inf s^(r-1)/(l+s)^m * rho(q+s) ds >= 0,
  rho(u) = (m/n)(u^n + (1-u)^n) - u^(n-1),  n = m-2r odd.

Stronger form (implies I>=0 for ALL l>0 simultaneously):
  J(t) = int_0^inf s^(r-1) e^(-st) rho(q+s) ds >= 0 for all t>0.
Equivalently Phi(y) >= 0 for all y>0 where (y=1/t)
  Phi(y) = sum_j (r)_j y^j [ (m/n) C(n,j)(q^(n-j)+(-1)^j p^(n-j)) - C(n-1,j) q^(n-1-j) ].

1) Sanity: check u-line form against direct Pdiag for random cases.
2) Scan: is Phi(y) >= 0 on y>0 for q <= 1/3? up to which q does it hold ("qJ*")?
   Compare qJ*(n,r) with the true diagonal threshold q*(n,r).
"""
import numpy as np
from math import comb, gamma
from scipy.integrate import quad

def geom(c, N): return c**np.arange(N+1)
def ser_mul(a, b, N): return np.convolve(a, b)[:N+1]
def coeff_prod(cs, n):
    out = np.zeros(n+1); out[0] = 1.0
    for c in cs: out = ser_mul(out, geom(c, n), n)
    return out[n]
def Pdiag(m, r, q, l):
    p = 1 - q; n = m - 2*r
    tW = coeff_prod([p]*r + [-l]*r, n)
    tU = coeff_prod([q]*r + [l]*r, n)
    tP = coeff_prod([q]*(r+1) + [l]*r, n-1) if n >= 1 else 0.0
    return (m/r)*(tW + tU) - tP

def uline(m, r, q, l):
    n = m - 2*r
    rho = lambda u: (m/n)*(u**n + (1-u)**n) - u**(n-1)
    f = lambda s: s**(r-1)/(l+s)**m * rho(q+s)
    v1, _ = quad(f, 0, 5, limit=400)
    v2, _ = quad(f, 5, np.inf, limit=400)
    return v1 + v2

print("== 1) u-line form vs direct (ratio check: Pdiag = const * I) ==")
rng = np.random.default_rng(3)
for _ in range(6):
    r = int(rng.integers(1, 6)); n = int(rng.choice([3,5,9,13])); m = n + 2*r
    q = rng.uniform(0.05, 0.5); l = rng.uniform(0.01, 0.5)
    # constant: Pdiag = binom(n+2r-1,2r-1)*(n/r)* [ (m/n) E(V^n+W^n) - E(Xi V^{n-1}) ]
    # and E-target = (1/B(r,r)) * l^(n+r) * I. So Pdiag = C * I with
    C = comb(n+2*r-1, 2*r-1)*(n/r)*l**(n+r)*gamma(2*r)/gamma(r)**2
    direct = Pdiag(m, r, q, l); via = C*uline(m, r, q, l)
    print(f"  n={n} r={r} q={q:.3f} l={l:.3f}: direct={direct:.8e} via-uline={via:.8e} "
          f"rel={abs(direct-via)/abs(direct):.2e}")

print("== 2) Laplace form Phi(y): threshold qJ*(n,r) vs diagonal q*(n,r) ==")
def Phi_min_positive(n, r, q, ygrid):
    m = n + 2*r; p = 1 - q
    # coefficients
    cs = []
    poch = 1.0
    for j in range(0, n+1):
        if j > 0: poch *= (r + j - 1)
        br = (m/n)*comb(n, j)*(q**(n-j) + (-1)**j * p**(n-j))
        if j <= n-1: br -= comb(n-1, j)*q**(n-1-j)
        cs.append(poch*br)
    cs = np.array(cs)
    vals = np.polyval(cs[::-1], ygrid[:, None]).ravel() if False else None
    # evaluate stably: Horner in y over grid
    out = np.zeros_like(ygrid)
    for c in cs[::-1]:
        out = out*ygrid + c
    return out.min()

ygrid = np.concatenate([np.linspace(1e-6, 2, 4001), np.linspace(2, 50, 2001)])
for (n, r) in [(5,1),(9,1),(13,1),(21,1),(13,2),(21,2),(21,3),(31,5),(41,6),(55,13),(31,7),(61,15)]:
    lo, hi = 0.0, 0.5
    if Phi_min_positive(n, r, 0.5-1e-9, ygrid) >= 0:
        print(f"  n={n:3d} r={r:2d} (m={n+2*r:3d}): qJ*=0.5000")
        continue
    for _ in range(30):
        mid = (lo+hi)/2
        if Phi_min_positive(n, r, mid, ygrid) >= 0: lo = mid
        else: hi = mid
    print(f"  n={n:3d} r={r:2d} (m={n+2*r:3d}): qJ*={lo:.4f}")
