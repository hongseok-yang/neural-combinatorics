#!/usr/bin/env python3
"""Clean checker for cleaned_two_sided_shift_proofs.tex.

The default run uses exact rational arithmetic (fractions.Fraction) for the algebraic checks and for the finite strip certificate.  The optional legacy Bernstein checks are also exact; the legacy floating grid diagnostic is not run by default.

  (1) Two-sided spectral-shift identity  t(C_m,W) + t(C_m,U) = p^m + q^m + S_m
      on random rational block graphons, and Phi_m = q^(m-1) + S_m - x_(m-1)
      = (t(C_m,W) - g_m(p)) - (x_(m-1) - t(C_m,U)).
  (2) Expansion Phi_m = sum_r int Pcal_{m,r} d mu^r for atomic rational mu,
      and Pcal_{m,1} = closed form P_q^(m).
  (3) Mixture-of-diagonals identity for r=2 (exact, via
      int_0^1 (t l1 + (1-t) l2)^k dt = h_k(l1,l2)/(k+1)).
  (4) One-dimensional kernel form (exact via Beta integrals).
  (5) rho-lemma grouping identities (polynomial identities) and reflection.
  (6) Exact rational Bernstein certificates:  Ptilde_{m,r}(q,l) >= 0 on
      (q,l) in [0,1/3] x [-1/2,1/2], all r, odd m <= MAX_M   (default 43).
  (7) Theorem (r=1) arithmetic: 28q^2-40q+13 = 28(q-1/2)(q-13/14);
      c_n bound; final inequality margin on a grid (float, reported).
  (8) Region II: exact algebra of the two-clique family and the
      9s + O(s^2) expansion of the (false) naive forced-coupling ratio.
  (9) [--strip] Strip-criterion interval verification (piecewise Riemann
      bounds, exact rational, adaptive subdivision) for all residual (m,r)
      with 45 <= m <= --strip-max-m (default 61; the recorded full run used
      --strip-max-m 201).
 (10) [--q0-2-5] Bernstein certificates on [0,2/5] x [-1/2,1/2] (p >= 3/5).
 (11) Aggregate forced-coupling lemma, exact on the two-clique family
      (rational parametrisation s = 1-t^2).

Usage:  python3 two_sided_shift_checker.py [--max-m M] [--strip] [--q0-2-5]
"""
from __future__ import annotations

import argparse
import itertools
import random
from fractions import Fraction as F
from math import comb, factorial

OK = 0


def report(name: str, ok: bool, detail: str = "") -> None:
    global OK
    status = "OK " if ok else "FAIL"
    print(f"[{status}] {name}" + (f" -- {detail}" if detail else ""), flush=True)
    if not ok:
        raise SystemExit(f"check failed: {name}")
    OK += 1


# ---------------------------------------------------------------- matrices --

def mat_mul(A, B):
    n, k, m2 = len(A), len(B), len(B[0])
    return [[sum(A[i][t]*B[t][j] for t in range(k)) for j in range(m2)] for i in range(n)]


def mat_pow_trace(M, m):
    P = M
    for _ in range(m - 1):
        P = mat_mul(P, M)
    return sum(P[i][i] for i in range(len(M)))


# ------------------------------------------------- block-graphon quantities --

def graphon_data(w, Uv):
    """w: list of Fractions (sum 1); Uv: rational symmetric matrix in [0,1].
    Returns q, cycle/path functionals and the moment list s_j, j <= jmax."""
    k = len(w)
    q = sum(w[i]*Uv[i][j]*w[j] for i in range(k) for j in range(k))
    # T_U f = Uv * diag(w) f ;  inner product <f,h> = sum w f h
    def T(f):
        return [sum(Uv[i][j]*w[j]*f[j] for j in range(k)) for i in range(k)]
    one = [F(1)]*k
    d = T(one)
    g = [d[i] - q for i in range(k)]
    def ip(f, h):
        return sum(w[i]*f[i]*h[i] for i in range(k))
    def proj(f):
        c = ip(f, one)
        return [f[i] - c for i in range(k)]
    def Aop(f):
        return proj(T(proj(f)))
    # moments s_j = <g, A^j g>
    s = []
    v = g[:]
    for j in range(0, 60):
        s.append(ip(g, v))
        v = Aop(v)
    return q, T, one, g, s, ip


def cycle_density(w, Kv, m):
    k = len(w)
    N = [[Kv[i][j]*w[j] for j in range(k)] for i in range(k)]
    return mat_pow_trace(N, m)


def path_density(w, Kv, j):
    k = len(w)
    f = [F(1)]*k
    for _ in range(j):
        f = [sum(Kv[a][b]*w[b]*f[b] for b in range(k)) for a in range(k)]
    return sum(w[a]*f[a] for a in range(k))


# ----------------------------------------------------------- shift series ---

def ser_mul(a, b, N):
    out = [F(0)]*(N+1)
    for i, ai in enumerate(a):
        if i > N or ai == 0:
            continue
        for j, bj in enumerate(b):
            if i + j > N:
                break
            out[i+j] += ai*bj
    return out


def S_m_from_moments(p, q, s, m):
    """S_m = m [z^m](L_W + L_U) from moments s_j = <g, A^j g>."""
    N = m
    # R_W = sum_j (-1)^j s_j z^j ; R_U = sum_j s_j z^j
    RW = [(F(-1)**j)*s[j] if j < len(s) else F(0) for j in range(N+1)]
    RU = [s[j] if j < len(s) else F(0) for j in range(N+1)]
    geo_p = [p**j for j in range(N+1)]
    geo_q = [q**j for j in range(N+1)]
    z2 = [F(0), F(0), F(1)] + [F(0)]*(N-2)
    YW = ser_mul(ser_mul(z2, RW, N), geo_p, N)
    YU = ser_mul(ser_mul(z2, RU, N), geo_q, N)
    tot = F(0)
    for Y in (YW, YU):
        Yr = [F(1)] + [F(0)]*N
        for r in range(1, N//2 + 1):
            Yr = ser_mul(Yr, Y, N)
            if all(c == 0 for c in Yr):
                break
            tot += Yr[m]/r
    return m*tot


def x_series_from_moments(q, s, jmax):
    """x_j = [z^j] 1/(1 - qz - z^2 R_U(z)), j <= jmax."""
    N = jmax
    denom = [F(0)]*(N+1)
    denom[0] = F(1)
    denom[1] = -q
    for j in range(0, N-1):
        denom[j+2] = -(s[j] if j < len(s) else F(0))
    inv = [F(0)]*(N+1)
    inv[0] = F(1)
    for n_ in range(1, N+1):
        acc = F(0)
        for t in range(1, n_+1):
            acc += denom[t]*inv[n_-t]
        inv[n_] = -acc
    return inv


# --------------------------------------------------------------- P family ---

def h_poly(cs, d):
    """h_d(cs) exactly."""
    out = [F(1)] + [F(0)]*d
    for c in cs:
        geo = [c**j for j in range(d+1)]
        out = ser_mul(out, geo, d)
    return out[d]


def Pcal(m, r, q, lams):
    p = 1 - q
    n = m - 2*r
    tW = h_poly([p]*r + [-l for l in lams], n)
    tU = h_poly([q]*r + list(lams), n)
    tP = h_poly([q]*(r+1) + list(lams), n-1) if n >= 1 else F(0)
    return F(m, r)*(tW + tU) - tP


def Ptilde_coeffs_in_l(m, r, q, degmax=None):
    """Ptilde_{m,r}(q, l) as a polynomial in l (list of Fractions)."""
    p = 1 - q
    n = m - 2*r
    c = lambda i, rr: F(comb(i + rr - 1, rr - 1))
    # [z^n] (1-pz)^-r (1+lz)^-r  = sum_{i+j=n} c(i,r) p^i * c(j,r) (-l)^j
    dW = [F(0)]*(n+1)
    dU = [F(0)]*(n+1)
    for j in range(n+1):
        i = n - j
        dW[j] += c(i, r)*(p**i)*c(j, r)*(F(-1)**j)
        dU[j] += c(i, r)*(q**i)*c(j, r)
    dP = [F(0)]*(n+1)
    for j in range(n):
        i = n - 1 - j
        dP[j] += c(i, r+1)*(q**i)*c(j, r)
    return [F(m, r)*(dW[j] + dU[j]) - dP[j] for j in range(n+1)]


# ================================================================== checks ==

def check1_identity(rng):
    for trial in range(6):
        k = rng.randint(2, 4)
        w_raw = [F(rng.randint(1, 9)) for _ in range(k)]
        tot = sum(w_raw)
        w = [x/tot for x in w_raw]
        Uv = [[F(0)]*k for _ in range(k)]
        for i in range(k):
            for j in range(i, k):
                Uv[i][j] = Uv[j][i] = F(rng.randint(0, 12), 12)
        Wv = [[1 - Uv[i][j] for j in range(k)] for i in range(k)]
        q, T, one, g, s, ip = graphon_data(w, Uv)
        p = 1 - q
        for m in (5, 7, 9, 11):
            cW = cycle_density(w, Wv, m)
            cU = cycle_density(w, Uv, m)
            Sm = S_m_from_moments(p, q, s, m)
            lhs = cW + cU
            rhs = p**m + q**m + Sm
            assert lhs == rhs, (m, lhs - rhs)
            xm1 = path_density(w, Uv, m-1)
            Phi_series = q**(m-1) + Sm - xm1
            Phi_direct = (cW - (p**m - p*q**(m-1))) - (xm1 - cU)
            assert Phi_series == Phi_direct
    report("(1) two-sided identity + Phi identity, exact, 6 random block graphons x m in 5..11", True)


def check2_expansion(rng):
    for trial in range(5):
        q = F(rng.randint(1, 5), 12)
        atoms = [(F(rng.randint(1, 5), 40), F(rng.randint(-6, 6), 12)) for _ in range(2)]
        p = 1 - q
        s = [sum(u*(l**j) for (u, l) in atoms) for j in range(40)]
        for m in (5, 7, 9, 11, 13):
            Sm = S_m_from_moments(p, q, s, m)
            x = x_series_from_moments(q, s, m-1)
            Phi = q**(m-1) + Sm - x[m-1]
            tot = F(0)
            for r in range(1, (m-1)//2 + 1):
                for tup in itertools.product(range(len(atoms)), repeat=r):
                    uu = F(1)
                    for i in tup:
                        uu *= atoms[i][0]
                    tot += uu*Pcal(m, r, q, [atoms[i][1] for i in tup])
            assert tot == Phi, (m, tot - Phi)
    # closed form r=1
    for m in (5, 9, 13, 21):
        q = F(3, 10); lam = F(-2, 5)
        closed = sum(((F(-1)**j)*m*(1-q)**(m-2-j) + m*q**(m-2-j)
                      - (m-2-j)*q**(m-3-j))*(lam**j) for j in range(m-2))
        assert closed == Pcal(m, 1, q, [lam])
    report("(2) expansion Phi = sum_r int Pcal dmu^r (exact, m<=13) + r=1 closed form", True)


def check3_mixture(rng):
    for trial in range(6):
        m = rng.choice([9, 11, 13, 17])
        q = F(rng.randint(0, 6), 13)
        l1 = F(rng.randint(-6, 6), 12)
        l2 = F(rng.randint(-6, 6), 12)
        if l1 == l2:
            l2 += F(1, 12)
        r = 2
        coeffs = Ptilde_coeffs_in_l(m, r, q)
        # E[Ptilde(q, t l1 + (1-t) l2)], t uniform: int l(t)^k dt = h_k(l1,l2)/(k+1)
        mix = sum(coeffs[k_]*h_poly([l1, l2], k_)/(k_+1) for k_ in range(len(coeffs)))
        direct = Pcal(m, r, q, [l1, l2])
        assert mix == direct, (m, q, l1, l2, mix - direct)
    report("(3) mixture-of-diagonals identity, r=2, exact polynomial check", True)


def check4_uline():
    for (m, r, q, l) in [(9, 2, F(1, 4), F(1, 3)), (13, 3, F(1, 3), F(2, 5)),
                         (11, 1, F(2, 7), F(1, 2)), (15, 4, F(1, 5), F(1, 8))]:
        n = m - 2*r
        # rho(q+s) = (m/n)((q+s)^n + (p-s)^n) - (q+s)^(n-1) as poly in s
        p = 1 - q
        rho = [F(0)]*(n+1)
        for k_ in range(n+1):
            rho[k_] += F(m, n)*comb(n, k_)*(q**(n-k_))
            rho[k_] += F(m, n)*comb(n, k_)*(p**(n-k_))*(F(-1)**k_)
            if k_ <= n-1:
                rho[k_] -= comb(n-1, k_)*(q**(n-1-k_))
        # integral: sum_k rho_k * l^(r+k-m) * B(r+k, m-r-k)
        integ = sum(rho[k_]*(l**(r+k_-m))*F(factorial(r+k_-1)*factorial(m-r-k_-1), factorial(m-1))
                    for k_ in range(n+1))
        C = F(comb(n+2*r-1, 2*r-1))*F(n, r)*F(factorial(2*r-1), factorial(r-1)**2)
        val = C*(l**(n+r))*integ
        coeffs = Ptilde_coeffs_in_l(m, r, q)
        direct = sum(coeffs[k_]*(l**k_) for k_ in range(len(coeffs)))
        assert val == direct, (m, r, val - direct)
    report("(4) one-dimensional kernel form, exact via Beta integrals", True)


def check5_rho():
    for n in range(3, 42, 2):
        # identity u^n + (1-u)^n - u^(n-1) = (1-u)[(1-u)^(n-1) - u^(n-1)]
        lhs = [F(0)]*(n+1)
        lhs[n] += 1                       # u^n
        for k_ in range(n+1):
            lhs[k_] += comb(n, k_)*(F(-1)**k_)   # (1-u)^n
        lhs[n-1] -= 1
        rhs = [F(0)]*(n+1)
        for k_ in range(n):
            rhs[k_] += comb(n-1, k_)*(F(-1)**k_)      # (1-u)^(n-1)
            rhs[k_+1] -= comb(n-1, k_)*(F(-1)**k_)    # -u(1-u)^(n-1)
        rhs[n-1] -= 1
        rhs[n] += 1                                   # -(1-u)u^(n-1)
        assert lhs == rhs, n
    # reflection inequality on a rational grid
    for n in (3, 9, 21):
        for r in (1, 3, 10):
            m = n + 2*r
            for num in range(-30, 41):
                u = F(num, 20)
                rho = lambda t: F(m, n)*(t**n + (1-t)**n) - t**(n-1)
                assert rho(u) + rho(1-u) >= 0
                if not (F(1, 2) < u < F(n, m)):
                    assert rho(u) >= 0, (n, r, u)
    report("(5) rho-lemma: grouping identity (n<=41) + window/reflection on grid", True)


# ------------------------------------------------ Bernstein certificates ----

def bernstein_coeffs_2d(poly, d1, d2):
    """poly: dict (i,j)->Fraction on [0,1]^2. Bernstein coefficients."""
    B = [[F(0)]*(d2+1) for _ in range(d1+1)]
    for k_ in range(d1+1):
        for l_ in range(d2+1):
            acc = F(0)
            for (i, j), a in poly.items():
                if i <= k_ and j <= l_:
                    acc += a*F(comb(k_, i)*comb(l_, j), comb(d1, i)*comb(d2, j))
            B[k_][l_] = acc
    return B


def poly_shift_scale(poly, ax, bx, ay, by):
    """substitute x -> ax + bx*x, y -> ay + by*y."""
    out = {}
    for (i, j), a in poly.items():
        for ii in range(i+1):
            cx = a*comb(i, ii)*(ax**(i-ii))*(bx**ii)
            for jj in range(j+1):
                c = cx*comb(j, jj)*(ay**(j-jj))*(by**jj)
                if c:
                    out[(ii, jj)] = out.get((ii, jj), F(0)) + c
    return {k: v for k, v in out.items() if v}


def certify_nonneg(poly, d1, d2, depth=0, maxdepth=9):
    """poly on [0,1]^2; True if certified >= 0 by Bernstein + subdivision."""
    B = bernstein_coeffs_2d(poly, d1, d2)
    if all(B[i][j] >= 0 for i in range(d1+1) for j in range(d2+1)):
        return True
    # quick negativity test at box corners / centre
    def ev(x, y):
        return sum(a*(x**i)*(y**j) for (i, j), a in poly.items())
    for (x, y) in [(F(0), F(0)), (F(1), F(0)), (F(0), F(1)), (F(1), F(1)),
                   (F(1, 2), F(1, 2))]:
        if ev(x, y) < 0:
            return False
    if depth >= maxdepth:
        return False
    h = F(1, 2)
    for (ax, ay) in [(F(0), F(0)), (h, F(0)), (F(0), h), (h, h)]:
        sub = poly_shift_scale(poly, ax, h, ay, h)
        if not certify_nonneg(sub, d1, d2, depth+1, maxdepth):
            return False
    return True


def check6_certificates(max_m):
    for m in range(5, max_m + 1, 2):
        for r in range(1, (m-1)//2 + 1):
            n = m - 2*r
            # build P~(q,l) as 2-var poly (times r to clear denominators)
            c = lambda i, rr: comb(i + rr - 1, rr - 1)
            poly = {}
            def add(i_q, j_l, coeff):
                if coeff:
                    poly[(i_q, j_l)] = poly.get((i_q, j_l), F(0)) + coeff
            for j in range(n+1):
                i = n - j
                # m * c(i,r) (1-q)^i c(j,r) (-1)^j l^j
                base = F(m)*c(i, r)*c(j, r)*(F(-1)**j)
                for t in range(i+1):
                    add(t, j, base*comb(i, t)*(F(-1)**t))
                add(i, j, F(m)*c(i, r)*c(j, r))   # m c(i,r) q^i c(j,r) l^j
            for j in range(n):
                i = n - 1 - j
                add(i, j, -F(r)*c(i, r+1)*c(j, r))
            # substitute q = x/3, l = -1/2 + y  (x,y in [0,1]^2)
            sub = poly_shift_scale(poly, F(0), F(1, 3), F(-1, 2), F(1))
            d1 = max(i for (i, j) in sub) if sub else 0
            d2 = max(j for (i, j) in sub) if sub else 0
            ok = certify_nonneg(sub, d1, d2)
            if not ok:
                report(f"(6) Bernstein certificate m={m} r={r}", False)
        print(f"    m={m}: all r certified on [0,1/3]x[-1/2,1/2]", flush=True)
    report(f"(6) exact Bernstein certificates, odd m <= {max_m}, all r", True)


def check7_r1_arith():
    # factorisation
    import fractions
    qs = [F(k, 97) for k in range(0, 49)]
    for q in qs:
        assert 28*q**2 - 40*q + 13 == 28*(q - F(1, 2))*(q - F(13, 14))
    # final inequality margin on a float grid
    import numpy as np
    worst = float("inf")
    for m in list(range(7, 200, 2)) + [301, 501, 1001]:
        n = m - 2
        for qf in np.linspace(2/m + 1e-9, 1/3, 25):
            if qf <= 2/m:
                continue
            pf = 1 - qf
            for lf in np.linspace(1e-6, min(0.5, qf + 1/m), 25):
                eps = (1 - 2*qf)/4
                cn = 1 - (n/m)*((qf+eps)**(n-1))/((pf-eps)**n)
                lhs = (m*m*eps*cn/((m*qf-2)**2)) * pf \
                    * (((pf-eps)/pf)**n) * (((lf+1-2*qf)/(lf+eps))**m)
                worst = min(worst, lhs)
    report("(7) r=1 arithmetic: factorisation exact; final inequality margin",
           worst >= 1, f"min LHS of (6.4-final) over grid = {worst:.2f} (needs >= 1)")


def check8_region2():
    for s in [F(1, 10), F(1, 100), F(1, 1000), F(1, 10**6)]:
        w = [(1-s)/2, (1-s)/2, s]
        k = 3
        Uv = [[F(0)]*3 for _ in range(3)]
        Uv[0][0] = Uv[1][1] = F(1)
        q, T, one, g, sm, ip = graphon_data(w, Uv)
        p = 1 - q
        assert q == (1-s)**2/2
        alpha = (1-s)/2                       # eigenvalue of A: phi = 1_c1 - 1_c2
        # verify A phi = alpha phi exactly
        phi = [F(1), F(-1), F(0)]
        Tphi = [sum(Uv[i][j]*w[j]*phi[j] for j in range(k)) for i in range(k)]
        c0 = sum(w[i]*Tphi[i] for i in range(k))
        Aphi = [Tphi[i] - c0 for i in range(k)]
        assert all(Aphi[i] == alpha*phi[i] for i in range(k))
        g2 = ip(g, g)
        assert g2 == s*q**2 + (1-s)*(alpha-q)**2
        ratio = g2*(p-alpha)**2/(p*alpha*(alpha-q)**2)
        # 9s + O(s^2)
        assert abs(ratio/s - 9) <= 40*s, (s, float(ratio/s))
    report("(8) Region II two-clique family: exact algebra + ratio = 9s + O(s^2)", True)


# ---------------------------------------------- strip criterion (Thm 6.x) ---

def strip_verify_pair(m, r, maxdepth=14, Jsig=5, Ksub=10, KD=10, KB=12):
    n = m - 2*r
    nu = F(n, m)
    half = F(1, 2)
    third = F(1, 3)
    gamma = F(r, m)

    def cell_ok(q1, q2, l1, l2, depth):
        if l1 >= q2 + gamma:
            return True
        sa_lo, sa_up = half - q2, half - q1
        sb_lo, sb_up = nu - q2, nu - q1
        if 2*(n-1)*(l2 - q1) >= (2*r + 1):
            return subdivide(q1, q2, l1, l2, depth)
        if sb_up <= sa_lo:
            return True
        s_lin_lo = (2*m*sa_lo - (r-1)*l2)/(m + r - 1)
        sigmax = min(2*sa_lo, sb_up)
        # sigma = sa_up is admissible only if the linearised pairing condition
        # holds at sa_up for the whole cell:
        if m*(2*sa_lo - sa_up) >= (r-1)*(l2 + sa_up):
            sigmas = [sa_up]
        else:
            sigmas = []
        auto = len(sigmas)
        if not sigmas and s_lin_lo <= sa_up:
            return subdivide(q1, q2, l1, l2, depth) if depth < maxdepth else False
        if s_lin_lo > sa_up:
            sigmas.append(min(s_lin_lo, sigmax))
            auto = 2
            if sigmax > s_lin_lo:
                gap = sigmax - s_lin_lo
                for j in range(1, Jsig + 1):
                    sigmas.append(s_lin_lo + j*gap/Jsig)
                for dv in (gap/24, gap/96):
                    sigmas.insert(-1, sigmax - dv)
                sigmas.sort()

        def zoneA_exact(s0, s1):
            if s1 <= s0:
                return True
            for i in range(Ksub):
                t0 = s0 + i*(s1 - s0)/Ksub
                t1 = s0 + (i+1)*(s1 - s0)/Ksub
                w_lo = 2*sa_lo - t1
                if w_lo <= 0:
                    return False
                if ((l2 + t0)**m)*(w_lo**(r-1)) < (t1**(r-1))*((l2 + 2*sa_up - t0)**m):
                    return False
            return True

        okA = [True]*auto
        for j in range(auto, len(sigmas)):
            okA.append(okA[-1] and zoneA_exact(sigmas[j-1], sigmas[j]))

        for j in range(len(sigmas) - 1, -1, -1):
            if not okA[j]:
                continue
            sig = sigmas[j]
            if sig >= sb_up:
                return True
            if 1 - F(m, n)*(q1 + sig) <= 0:
                return True
            # deficit: KD-piece upper sum (integrand decreasing in s)
            D = F(0)
            for i in range(KD):
                t0 = sig + i*(sb_up - sig)/KD
                t1 = sig + (i+1)*(sb_up - sig)/KD
                br = 1 - F(m, n)*(q1 + t0)
                if br <= 0:
                    continue
                D += (sb_up**(r-1))*(t1 - t0)*((q2 + t0)**(n-1))*br/((l1 + t0)**m)
            if D == 0:
                return True
            # surplus: piecewise lower sums
            S = F(0)
            WL = min(2*sa_lo - sig, sa_lo)
            if WL > 0:
                for i in range(1, KB):
                    t0 = i*WL/KB
                    t1 = (i+1)*WL/KB
                    pc = 1 - q2 - t1
                    qc = q2 + t1
                    if pc <= qc or pc <= 0:
                        continue
                    cp = 1 - F(n, m)*(qc**(n-1))/(pc**n)
                    if cp <= 0:
                        continue
                    S += F(m, n)*(pc**n)*cp*(t1 - t0)*(t0**(r-1))/((l2 + t1)**m)
                if S >= D:
                    return True
            dmax = 2*gamma - (q2 - q1)
            if dmax > 0:
                for i in range(1, KB):
                    d0 = i*dmax/KB
                    d1 = (i+1)*dmax/KB
                    S += F(m, n)*d0*((nu + d0)**(n-1))*(d1 - d0)*((sb_up + d0)**(r-1)) \
                         / ((l2 + sb_up + d1)**m)
                    if S >= D:
                        return True
            if S >= D:
                return True
        if depth >= maxdepth:
            return False
        return subdivide(q1, q2, l1, l2, depth)

    def subdivide(q1, q2, l1, l2, depth):
        if (q2 - q1)*3 >= (l2 - l1)*2:
            qm = (q1 + q2)/2
            return cell_ok(q1, qm, l1, l2, depth+1) and cell_ok(qm, q2, l1, l2, depth+1)
        lm = (l1 + l2)/2
        return cell_ok(q1, q2, l1, lm, depth+1) and cell_ok(q1, q2, lm, l2, depth+1)

    return cell_ok(F(0), third, F(0), half, 0)


def check9_strip(strip_max_m):
    for m in range(45, strip_max_m + 1, 2):
        rs = [r for r in range(2, (m-1)//4 + 1) if m - 2*r > 2*r]
        for r in rs:
            if not strip_verify_pair(m, r):
                report(f"(9) strip criterion m={m} r={r}", False)
        print(f"    m={m}: strip criterion verified for all {len(rs)} residual r", flush=True)
    report(f"(9) strip-criterion interval verification, 45 <= m <= {strip_max_m}", True)


def check10_certificates_q0(max_m):
    for m in range(5, max_m + 1, 2):
        for r in range(1, (m-1)//2 + 1):
            n = m - 2*r
            c = lambda i, rr: comb(i + rr - 1, rr - 1)
            poly = {}
            def add(iq, jl, coeff):
                if coeff:
                    poly[(iq, jl)] = poly.get((iq, jl), F(0)) + coeff
            for j in range(n+1):
                i = n - j
                base = F(m)*c(i, r)*c(j, r)*(F(-1)**j)
                for t in range(i+1):
                    add(t, j, base*comb(i, t)*(F(-1)**t))
                add(i, j, F(m)*c(i, r)*c(j, r))
            for j in range(n):
                i = n - 1 - j
                add(i, j, -F(r)*c(i, r+1)*c(j, r))
            sub = poly_shift_scale(poly, F(0), F(2, 5), F(-1, 2), F(1))
            d1 = max(i for (i, j) in sub); d2 = max(j for (i, j) in sub)
            if not certify_nonneg(sub, d1, d2, maxdepth=11):
                report(f"(10) q0=2/5 Bernstein certificate m={m} r={r}", False)
        print(f"    m={m}: all r certified on [0,2/5]x[-1/2,1/2]", flush=True)
    report(f"(10) exact Bernstein certificates at q0=2/5, odd m <= {max_m}, all r", True)


def check11_aggregate_fc():
    """Aggregate forced-coupling lemma, exact on the two-clique family.

    Family: blocks (t^2 parts): sizes ((1-s)/2, (1-s)/2, s) with s = 1-t^2,
    U = 1 on the two diagonal clique blocks.  phi = (1/t, -1/t, 0), unit norm,
    A phi = alpha phi with alpha = (1-s)/2.  All quantities rational."""
    for t in (F(9, 10), F(3, 4), F(99, 100), F(999, 1000)):
        s = 1 - t*t
        w = [(1-s)/2, (1-s)/2, s]
        Uv = [[F(0)]*3 for _ in range(3)]
        Uv[0][0] = Uv[1][1] = F(1)
        q, T, one, g, sm, ip = graphon_data(w, Uv)
        alpha = (1-s)/2
        phi = [1/t, -1/t, F(0)]
        # verify eigenfunction exactly: A phi = alpha phi
        Tphi = T(phi)
        c0 = ip(Tphi, one)
        for i in range(3):
            assert Tphi[i] - c0 == alpha*phi[i]
        assert ip(phi, phi) == 1 and ip(phi, one) == 0
        fp = [max(x, F(0)) for x in phi]
        fm = [max(-x, F(0)) for x in phi]
        a = ip(fp, one)
        assert a == ip(fm, one)
        n2p, n2m = ip(fp, fp), ip(fm, fm)
        cp_, cm_ = ip(fp, phi), ip(fm, phi)
        wp = [fp[i] - a - cp_*phi[i] for i in range(3)]
        wm = [fm[i] - a - cm_*phi[i] for i in range(3)]
        # A wm exactly
        Twm = T(wm)
        c1 = ip(Twm, one)
        Awm = [Twm[i] - c1 for i in range(3)]
        # project (A maps 1-perp to 1-perp already after centering)
        wAw = ip(wp, Awm)
        lhs = a*ip(g, [fp[i] + fm[i] for i in range(3)])
        rhs_exact = alpha*n2p*n2m - q*a*a - wAw
        assert lhs >= rhs_exact, (float(t), float(lhs), float(rhs_exact))
        # (L') with ||A|| <= 1/2 needs sqrt: use ||w+||^2||w-||^2 <= (2(rhs-gap))^2 form:
        # verify (L''): a^2 ||g||^2 (1-4a^2) >= (rhs')^2 when rhs' > 0, with
        # rhs' = alpha n2p n2m - q a^2 - (1/2)||w+|| ||w-||; use squared comparison.
        g2 = ip(g, g)
        nwp2, nwm2 = ip(wp, wp), ip(wm, wm)
        # rhs' >= alpha n2p n2m - q a^2 - (1/2) sqrt(nwp2*nwm2); bound the sqrt above
        # rationally: sqrt(xy) <= (x+y)/2
        rhs_prime_lb = alpha*n2p*n2m - q*a*a - (nwp2 + nwm2)/4
        if rhs_prime_lb > 0:
            assert a*a*g2*(1 - 4*a*a) >= rhs_prime_lb**2
    report("(11) aggregate forced-coupling lemma, exact on the two-clique family", True)



def check9_strip_range(strip_start_m, strip_max_m):
    if strip_start_m % 2 == 0:
        strip_start_m += 1
    for m in range(strip_start_m, strip_max_m + 1, 2):
        rs = [r for r in range(2, (m-1)//4 + 1) if m - 2*r > 2*r]
        for r in rs:
            if not strip_verify_pair(m, r):
                report(f"strip criterion m={m} r={r}", False)
        print(f"    m={m}: strip criterion verified for all {len(rs)} residual r", flush=True)
    report(f"exact strip-criterion interval verification, {strip_start_m} <= m <= {strip_max_m}", True)


def check_r1_constants_exact():
    # Exact rational inequalities used in the repaired r=1 proof.
    assert F(7, 288) * F(61, 47)**7 > F(11, 84)**2
    assert F(7, 288) * F(61, 47)**9 > F(5, 12)**2
    assert 1 - F(12, 7) * F(5, 7)**4 > F(1, 2)
    report("repaired r=1 proof constants, exact", True)


def main():
    ap = argparse.ArgumentParser(description="Clean exact checker for the cleaned two-sided shift note")
    ap.add_argument("--strip-start-m", type=int, default=5)
    ap.add_argument("--strip-max-m", type=int, default=61)
    ap.add_argument("--skip-strip", action="store_true")
    ap.add_argument("--bernstein-max-m", type=int, default=0,
                    help="Optional slow Bernstein check on [0,1/3] up to this odd m")
    ap.add_argument("--q0-2-5", action="store_true",
                    help="With --bernstein-max-m, also run q0=2/5 Bernstein checks")
    rng = random.Random(20260704)
    args = ap.parse_args()
    check1_identity(rng)
    check2_expansion(rng)
    check3_mixture(rng)
    check4_uline()
    check5_rho()
    check_r1_constants_exact()
    check8_region2()
    check11_aggregate_fc()
    if args.bernstein_max_m:
        check6_certificates(args.bernstein_max_m)
        if args.q0_2_5:
            check10_certificates_q0(args.bernstein_max_m)
    if not args.skip_strip:
        check9_strip_range(args.strip_start_m, args.strip_max_m)
    print(f"\nAll {OK} checks passed.")


if __name__ == "__main__":
    main()
