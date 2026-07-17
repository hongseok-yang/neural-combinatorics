#!/usr/bin/env python3
"""Validation script for the analytic proof of the Zone-B battle
(replacement of Lemma zoneB-battle, eq:B-battle, in paper_region2_v2.tex).

Checks, in order:
  [1] Exact rational verification of every table row and every surrogate
      (sqrt/exp safe brackets) displayed in zoneB_analytic.tex.
  [2] Exact rational verification of the Lambda lemma (Z1) and of the
      auxiliary rational comparisons quoted in the proofs.
  [3] Dense float-grid verification of every monotonicity claim (M1-M12)
      on its exact stated domain.
  [4] Dense float-grid end-to-end assembly: at every strip point the
      case chain (S / L-gamma / L-xi) is followed step by step and each
      intermediate inequality is verified pointwise; finally the battle
      inequality eq:B-battle itself (with the paper's rho-term) is verified.
  [5] Exact Fraction spot checks of the battle at corner/extreme rational
      points via safe-direction brackets (independent of the tables).

Exit code 0 iff everything passes.
"""
import sys
import numpy as np
from fractions import Fraction as F
from math import isqrt

FAILS = []


def check(name, ok, detail=""):
    tag = "PASS" if ok else "FAIL"
    print(f"[{tag}] {name}" + (f"  ({detail})" if detail else ""))
    if not ok:
        FAILS.append(name)


# ----------------------------------------------------------------------
# exact rational primitives
# ----------------------------------------------------------------------
E_LO, E_MID, E_HI = F(1, 60), F(1, 8), F(2033, 10000)
LAMHAT = F(13, 10 ** 6)
DIG = 5


def sqrt_lo(t, d=DIG):
    D = 10 ** d
    k = isqrt(t.numerator * D * D // t.denominator)
    while F(k, D) ** 2 > t:
        k -= 1
    while F(k + 1, D) ** 2 <= t:
        k += 1
    return F(k, D)


def sqrt_up(t, d=DIG):
    lo = sqrt_lo(t, d)
    return lo if lo * lo == t else lo + F(1, 10 ** d)


gamma = lambda e: F(7, 25) - e
kxi = lambda e: e / (1 - e) ** 2
kq = lambda e: (1 - 3 * e) / (6 * e)
kmax = lambda e: (1 - e) / (1 + e)
kbar = lambda e: min(kmax(e), kq(e))
x_ = lambda e, k: (1 - e) / (1 + e + 2 * k * e)
A_ = lambda e, k: x_(e, k) * (1 + k) / k
u_ = lambda e, k: 2 * e * (1 + k) / (1 + e + 2 * k * e)
Phi = lambda e, k: 2 * e * (1 - e) * (1 + k) ** 2 / (k * (1 + e + 2 * k * e) ** 2)
s_ = lambda e: 2 * e / (1 - e)


def G_lo(b):
    cl = sqrt_up(s_(b))
    cs = sqrt_lo(1 - b)
    return cs * (1 - cl) * (1 - s_(b) ** 7) / (1 + cl), cl, cs


def Kup_at(a, k):
    P = Phi(a, k)
    r = sqrt_lo(P * P + 4 * P)
    return 1 / (1 + r + r * r / 2 + r ** 3 / 6), r


# ----------------------------------------------------------------------
# the tables (breakpoints as displayed in the .tex file)
# ----------------------------------------------------------------------
T3G = [F(1, 60), F(21, 1000), F(8, 125), F(1, 8)]
T3X = [F(1, 8), F(2033, 10000)]
T4 = [F(1, 60), F(23, 1000), F(33, 1000), F(6, 125), F(67, 1000),
      F(89, 1000), F(111, 1000), F(1, 8)]
T5G = [F(1, 60), F(29, 1000), F(13, 200), F(1, 8)]
T5X = [F(1, 8), F(2033, 10000)]


def rows(bps):
    return list(zip(bps[:-1], bps[1:]))


# ----------------------------------------------------------------------
# [1] exact row verification
# ----------------------------------------------------------------------
def sec1():
    print("\n=== [1] exact rational verification of all table rows ===")
    # tiling
    check("tables tile [1/60,1/8] and [1/8,2033/10000]",
          T3G[0] == T4[0] == T5G[0] == E_LO and T3G[-1] == T4[-1] == T5G[-1] == E_MID
          and T3X == [E_MID, E_HI] and T5X == [E_MID, E_HI]
          and all(b > a for a, b in rows(T3G) + rows(T4) + rows(T5G)))

    ok = True
    for a, b in rows(T3G):
        Ab = x_(a, gamma(b)) * (1 + 1 / gamma(b))
        m = 15 * (14 - Ab) * u_(a, gamma(b)) - (Ab + 1)
        ok &= (Ab < 14) and m > 0
        print(f"    Z3-g [{a},{b}]  Abar={float(Ab):.4f}  slack={float(m):+.5f}")
    check("(Z3-g) gate rows on gamma-curve", ok)

    ok = True
    for a, b in rows(T3X):
        Ab = A_(a, kxi(a))
        m = 15 * (14 - Ab) * u_(a, kxi(a)) - (Ab + 1)
        ok &= (Ab < 14) and m > 0
        print(f"    Z3-x [{a},{b}]  Abar={float(Ab):.4f}  slack={float(m):+.5f}")
    check("(Z3-x) gate rows on kxi-curve", ok)

    ok = True
    for a, b in rows(T4):
        g, cl, cs = G_lo(b)
        K, r = Kup_at(a, gamma(a))
        P = Phi(a, gamma(a))
        # surrogate defining comparisons
        ok &= cl * cl >= s_(b) and cs * cs <= 1 - b and r * r <= P * P + 4 * P
        m = F(3, 4) * g - K / x_(b, gamma(b)) ** 2 - LAMHAT
        ok &= m > 0
        print(f"    Z4   [{a},{b}]  margin={float(m):+.5f}")
    check("(Z4) Case-S rows (incl. surrogate comparisons)", ok)

    ok = True
    for a, b in rows(T5G):
        g, cl, cs = G_lo(b)
        ok &= cl * cl >= s_(b) and cs * cs <= 1 - b
        m = g * (1 - kxi(b) / (4 * gamma(b))) - F(14, 15) * x_(a, gamma(a)) ** 12 - LAMHAT
        ok &= m > 0
        print(f"    Z5-g [{a},{b}]  margin={float(m):+.5f}")
    check("(Z5-g) Case-L rows on gamma-curve", ok)

    ok = True
    for a, b in rows(T5X):
        g, cl, cs = G_lo(b)
        ok &= cl * cl >= s_(b) and cs * cs <= 1 - b
        m = F(3, 4) * g - F(14, 15) * x_(a, kxi(a)) ** 12 - LAMHAT
        ok &= m > 0
        print(f"    Z5-x [{a},{b}]  margin={float(m):+.5f}")
    check("(Z5-x) Case-L rows on kxi-curve", ok)


# ----------------------------------------------------------------------
# [2] Lambda lemma and auxiliary rational comparisons
# ----------------------------------------------------------------------
def sec2():
    print("\n=== [2] Lambda lemma (Z1) and auxiliary comparisons ===")
    # (i) log-derivative positivity: 11/(2e) - 17/(2(1-e)) - 13/(1+e) > 0
    # via uniform bound at e = E_HI:
    lhs = F(11, 2) / E_HI - F(17, 2) / (1 - E_HI) - 13 / (1 + E_HI)
    check("Lambda1 log-derivative uniform bound  11/(2e)-17/(2(1-e))-13/(1+e) >= "
          f"{float(lhs):.4f} > 0 at e=E_HI", lhs > 0)
    # (ii) endpoint value: Lambda1(E_HI) = (2^6/15) sqrt(2e(1-e)) e^5(1-e)^8/(1+e)^13
    c = sqrt_up(2 * E_HI * (1 - E_HI))
    lam_end = F(64, 15) * c * E_HI ** 5 * (1 - E_HI) ** 8 / (1 + E_HI) ** 13
    check(f"Lambda1(E_HI) <= {float(lam_end):.4e} <= 13e-6 (c=14229/25000)",
          c == F(14229, 25000) and c * c >= 2 * E_HI * (1 - E_HI) and lam_end <= LAMHAT)
    # (iii) identity Lambda1 = (2^13/2 /15) e^{11/2}(1-e)^{17/2}/(1+e)^13, checked
    #       numerically in sec3 grid; here: the two aux comparisons in the tex
    # gate slack: kxi(1/8)=8/49 > gamma(1/8)=31/200
    check("kxi(1/8) > gamma(1/8)  (8*200 > 49*31)", 8 * 200 > 49 * 31)
    # Phi e-monotonicity constant: 8 - 8/7 - 229/75 > 0
    check("8 - 8/7 - 2(1+2*79/300) = 1997/525 > 0",
          8 - F(8, 7) - 2 * (1 + 2 * F(79, 300)) == F(1997, 525) and F(1997, 525) > 0)
    # kappa <= kmax < 1 on strip
    check("kmax(e) < 1 for e in (0,1)", kmax(F(1, 1000)) < 1 and kmax(E_HI) < 1)
    # 1 - kxi(b)/(4 gamma(b)) >= 0 at b = 1/8 (worst case, monotone)
    v = 1 - kxi(F(1, 8)) / (4 * gamma(F(1, 8)))
    check(f"1 - kxi/(4 gamma) at e=1/8 = {float(v):.4f} > 0", v > 0)


# ----------------------------------------------------------------------
# float versions for grids
# ----------------------------------------------------------------------
def f_kxi(e): return e / (1 - e) ** 2
def f_kbar(e): return np.minimum((1 - e) / (1 + e), (1 - 3 * e) / (6 * e))
def f_gam(e): return 0.28 - e
def f_x(e, k): return (1 - e) / (1 + e + 2 * k * e)
def f_A(e, k): return f_x(e, k) * (1 + k) / k
def f_u(e, k): return 2 * e * (1 + k) / (1 + e + 2 * k * e)
def f_Phi(e, k): return 2 * e * (1 - e) * (1 + k) ** 2 / (k * (1 + e + 2 * k * e) ** 2)
def f_Kstar(e, k):
    P = f_Phi(e, k)
    return np.exp(-np.sqrt(P * P + 4 * P))
def f_G(e):
    lb = np.sqrt(2 * e / (1 - e))
    return np.sqrt(1 - e) * (1 - lb) * (1 - lb ** 14) / (1 + lb)
def f_Lam1(e):
    return 2 ** 6.5 / 15 * e ** 5.5 * (1 - e) ** 8.5 / (1 + e) ** 13
def f_Lambar(e, k):
    return f_x(e, k) ** 13 * (2 * e / (1 - e)) ** 6.5 * (1 - e) ** 2 / (15 * e)


def mono(name, f, lo, hi, sign, n=20000, tol=1e-13):
    t = np.linspace(lo, hi, n)
    v = f(t)
    d = np.diff(v)
    ok = np.all(sign * d >= -tol * np.maximum(1, np.abs(v[:-1])))
    check(f"M: {name} {'increasing' if sign > 0 else 'decreasing'} on [{lo:.5f},{hi:.5f}]", bool(ok))


# ----------------------------------------------------------------------
# [3] monotonicity claims
# ----------------------------------------------------------------------
def sec3():
    print("\n=== [3] monotonicity claims (dense float grids) ===")
    ks = [0.01, 0.05, 0.15, 0.2633, 0.5, 0.99]
    for k in ks:
        mono(f"x(.,k={k})", lambda e, k=k: f_x(e, k), 1e-4, 0.21, -1)
        mono(f"u(.,k={k})", lambda e, k=k: f_u(e, k), 1e-4, 0.21, +1)
        mono(f"A(.,k={k})", lambda e, k=k: f_A(e, k), 1e-4, 0.21, -1)
    es = [1 / 60, 0.05, 1 / 8, 0.2033]
    for e in es:
        mono(f"x({e:.4f},.)", lambda k, e=e: f_x(e, k), 1e-3, 0.999, -1)
        mono(f"u({e:.4f},.)", lambda k, e=e: f_u(e, k), 1e-3, 0.999, +1)
        mono(f"A({e:.4f},.)", lambda k, e=e: f_A(e, k), 1e-3, 0.999, -1)
        mono(f"Phi({e:.4f},.) (kappa<=1)", lambda k, e=e: f_Phi(e, k), 1e-3, 1.0, -1)
    for k in [0.05, 0.155, 0.2633]:
        mono(f"Phi(.,k={k}) (e<=1/8)", lambda e, k=k: f_Phi(e, k), 1 / 60, 0.125, +1)
    mono("t -> exp(-sqrt(t^2+4t))", lambda t: np.exp(-np.sqrt(t * t + 4 * t)), 0.0, 10.0, -1)
    mono("G", f_G, 1 / 60, 0.21, -1)
    mono("kxi", f_kxi, 1e-4, 0.21, +1)
    mono("kxi/(4 gamma)", lambda e: f_kxi(e) / (4 * f_gam(e)), 1 / 60, 0.125, +1)
    mono("x(e,gamma(e))", lambda e: f_x(e, f_gam(e)), 1 / 60, 0.125, -1)
    mono("x(e,kxi(e))", lambda e: f_x(e, f_kxi(e)), 0.125, 0.2033, -1)
    mono("Lambda1", f_Lam1, 1 / 60, 0.2033, +1)
    mono("lambda>=u: min over e of ln(1/x)-(1-x)",
         lambda t: -np.log(1 - t) - t, 1e-6, 0.6, +1)  # ln(1/x)-(1-x) with u=1-x=t: >=0, incr
    # Lambda1 closed form == defining form (identity sanity)
    e = np.linspace(1 / 60, 0.2033, 5000)
    lhs = ((1 - e) / (1 + e)) ** 13 * (2 * e / (1 - e)) ** 6.5 * (1 - e) ** 2 / (15 * e)
    check("Lambda1 closed form identity", bool(np.allclose(lhs, f_Lam1(e), rtol=1e-12)))


# ----------------------------------------------------------------------
# [4] dense end-to-end assembly over the strip
# ----------------------------------------------------------------------
def bisect_row(bps, e):
    for a, b in zip(bps[:-1], bps[1:]):
        if float(a) <= e <= float(b):
            return a, b
    return None


def sec4(NE=1201, NK=1201):
    print("\n=== [4] dense end-to-end assembly over the strip ===")
    # precompute rational row constants as floats
    z3g = [(float(a), float(b),
            float(x_(a, gamma(b)) * (1 + 1 / gamma(b))), float(u_(a, gamma(b))))
           for a, b in rows(T3G)]
    z3x = [(float(a), float(b), float(A_(a, kxi(a))), float(u_(a, kxi(a))))
           for a, b in rows(T3X)]
    z4 = [(float(a), float(b), float(F(3, 4) * G_lo(b)[0]),
           float(Kup_at(a, gamma(a))[0] / x_(b, gamma(b)) ** 2))
          for a, b in rows(T4)]
    z5g = [(float(a), float(b), float(G_lo(b)[0] * (1 - kxi(b) / (4 * gamma(b)))),
            float(F(14, 15) * x_(a, gamma(a)) ** 12))
           for a, b in rows(T5G)]
    z5x = [(float(a), float(b), float(F(3, 4) * G_lo(b)[0]),
            float(F(14, 15) * x_(a, kxi(a)) ** 12))
           for a, b in rows(T5X)]

    bad = {k: 0 for k in ["battle", "S1", "S2", "S3", "S4", "Lg1", "Lg2", "Lg3", "Lg4",
                          "Lx1", "Lx2", "Lx3", "cover", "Kfrak<=Kstar", "Lam"]}
    nS = nLg = nLx = 0
    worst_battle = 1e9
    ee = np.linspace(1 / 60, 2033 / 10000, NE)
    for e in ee:
        klo, khi = f_kxi(e), f_kbar(e)
        if khi <= klo:
            continue
        kk = np.linspace(klo, khi, NK)
        x = f_x(e, kk); A = f_A(e, kk); u = f_u(e, kk); lam = np.log(1 / x)
        K14 = x ** 14 * np.maximum(0.0, 14 - A) / 15
        gate = (A < 14) & (15 * (14 - A) * lam >= A + 1)
        Kst = f_Kstar(e, kk)
        Kfrak = np.where(gate, K14, np.maximum(K14, Kst))
        rho = (1 - np.exp(-17.37 * (1 + kk) * e)) / 4
        epsb = np.minimum(0.25, e / (4 * (1 - e) ** 2 * kk * (1 + rho)))
        lb = np.sqrt(2 * e / (1 - e))
        Pi = np.sqrt(1 - e) * (1 - lb) * (1 - lb ** 14) * (1 - epsb) / (1 + lb)
        Lam = f_Lambar(e, kk)
        M = Pi - Kfrak / x ** 2 - Lam
        worst_battle = min(worst_battle, M.min())
        if np.any(M < 0):
            bad["battle"] += int(np.sum(M < 0))
        if np.any(Kfrak > Kst * (1 + 1e-12)):
            bad["Kfrak<=Kstar"] += int(np.sum(Kfrak > Kst * (1 + 1e-12)))
        if np.any(Lam > 13e-6):
            bad["Lam"] += int(np.sum(Lam > 13e-6))
        G = f_G(e)
        tol = 1e-12
        if e <= 0.125:
            g = f_gam(e)
            mS = kk <= g
            mL = ~mS
            r4 = bisect_row(T4, e); r5 = bisect_row(T5G, e); r3 = bisect_row(T3G, e)
            if r4 is None or r5 is None or r3 is None:
                bad["cover"] += 1
                continue
            # --- Case S chain ---
            if np.any(mS):
                nS += int(np.sum(mS))
                a4, b4 = r4
                LHSrow = float(F(3, 4) * G_lo(b4)[0])
                RHSrow = float(Kup_at(a4, gamma(a4))[0] / x_(b4, gamma(b4)) ** 2) + 13e-6
                # S1: Kfrak/x^2 <= Kstar(e,gamma)/x(e,gamma)^2 on mS
                lhs = (Kfrak / x ** 2)[mS]
                cap = f_Kstar(e, g) / f_x(e, g) ** 2
                bad["S1"] += int(np.sum(lhs > cap + tol))
                # S2: Kstar(e,gamma)/x(e,gamma)^2 + Lamhat <= RHSrow
                bad["S2"] += int(cap + 13e-6 > RHSrow + tol)
                # S3: (3/4) G(e) >= LHSrow
                bad["S3"] += int(0.75 * G < LHSrow - tol)
                # S4: Pi >= (3/4) G(e) on mS  (eps<=1/4)
                bad["S4"] += int(np.sum(Pi[mS] < 0.75 * G - tol))
                # row itself already exact
            # --- Case L-gamma chain ---
            if np.any(mL):
                nLg += int(np.sum(mL))
                a3, b3, Ab, ul = [v for v in z3g if v[0] <= e <= v[1]][0]
                # Lg1: gate ingredients at curve dominated by row constants
                bad["Lg1"] += int((f_A(e, g) > Ab + tol) or (f_u(e, g) < ul - tol)
                                  or not (Ab < 14 and 15 * (14 - Ab) * ul >= Ab + 1))
                # Lg2: true gate holds at all points of mL
                bad["Lg2"] += int(np.sum(~gate[mL]))
                # Lg3: Kfrak/x^2 <= (14/15) x(e,gamma)^12 <= row RHS
                a5, b5, L5, R5 = [v for v in z5g if v[0] <= e <= v[1]][0]
                lhs = (Kfrak / x ** 2)[mL]
                bad["Lg3"] += int(np.sum(lhs > (14 / 15) * f_x(e, g) ** 12 + tol)) \
                    + int((14 / 15) * f_x(e, g) ** 12 > R5 + tol)
                # Lg4: Pi >= G(1-kxi/(4gamma)) >= row LHS on mL
                lb_pi = G * (1 - f_kxi(e) / (4 * g))
                bad["Lg4"] += int(np.sum(Pi[mL] < lb_pi - tol)) + int(lb_pi < L5 - tol)
                bad["cover"] += int(R5 + 13e-6 > L5 + tol)
        if e >= 0.125:
            nLx += NK
            a3, b3, Ab, ul = z3x[0]
            a5, b5, L5, R5 = z5x[0]
            # Lx1: gate row dominates curve + extension: gate everywhere
            bad["Lx1"] += int((f_A(e, f_kxi(e)) > Ab + tol) or (f_u(e, f_kxi(e)) < ul - tol))
            bad["Lx1"] += int(np.sum(~gate))
            # Lx2: Kfrak/x^2 <= (14/15) x(e,kxi)^12 <= R5
            bad["Lx2"] += int(np.sum(Kfrak / x ** 2 > (14 / 15) * f_x(e, f_kxi(e)) ** 12 + tol))
            bad["Lx2"] += int((14 / 15) * f_x(e, f_kxi(e)) ** 12 > R5 + tol)
            # Lx3: Pi >= (3/4) G >= L5, and row margin
            bad["Lx3"] += int(np.sum(Pi < 0.75 * G - tol)) + int(0.75 * G < L5 - tol)
            bad["cover"] += int(R5 + 13e-6 > L5 + tol)

    print(f"    strip points: Case S {nS}, Case L-gamma {nLg}, Case L-xi {nLx}")
    print(f"    direct battle margin min over grid: {worst_battle:+.6f}")
    for k, v in bad.items():
        check(f"assembly: {k} violations = 0", v == 0, f"count {v}")


# ----------------------------------------------------------------------
# [5] exact Fraction spot checks of the battle at corners/extremes
# ----------------------------------------------------------------------
def battle_lo_exact(e, k):
    """Exact rational LOWER bound for  Pi_lower - Kfrak/x^2 - Lambda_upper  at (e,k)."""
    x = x_(e, k); A = A_(e, k); u = u_(e, k); s = s_(e)
    cl = sqrt_up(s); cs = sqrt_lo(1 - e)
    epsb = min(F(1, 4), kxi(e) / (4 * k))          # >= paper's eps-bar
    Pi_lo = cs * (1 - cl) * (1 - s ** 7) * (1 - epsb) / (1 + cl)
    K14 = x ** 14 * max(F(0), 14 - A) / 15
    ugate = (A < 14) and (15 * (14 - A) * u >= A + 1)
    if ugate:
        Kfrak_up = K14                               # u-gate => gate => Kfrak=K14
    else:
        Kst_up, _ = Kup_at(e, k)
        Kfrak_up = max(K14, Kst_up)
    Lam_up = x ** 13 * s ** 6 * cl * (1 - e) ** 2 / (15 * e)   # s^{6.5} <= s^6 * cl
    return Pi_lo - Kfrak_up / x ** 2 - Lam_up


def sec5():
    print("\n=== [5] exact Fraction spot checks at corners/extremes ===")
    pts = []
    for e in [F(1, 60), F(21, 1000), F(1, 30), F(8, 125), F(1, 10), F(1, 8),
              F(3, 20), F(19, 100), F(2029, 10000)]:
        cands = [kxi(e), kbar(e)]
        if e <= F(1, 8):
            cands.append(gamma(e))
        for k in cands:
            if kxi(e) <= k <= kbar(e):
                pts.append((e, k))
    # midpoints of S-band and L-band at a gate-fail e
    e = F(1, 30)
    pts.append((e, (kxi(e) + gamma(e)) / 2))
    pts.append((e, (gamma(e) + kbar(e)) / 2))
    ok = True
    for e, k in pts:
        m = battle_lo_exact(e, k)
        ok &= m > 0
        print(f"    e={str(e):>10}  kappa={float(k):.5f}  exact battle margin >= {float(m):+.5f}")
    check("exact spot checks all positive", ok, f"{len(pts)} points")


if __name__ == "__main__":
    sec1(); sec2(); sec3(); sec4(); sec5()
    print()
    if FAILS:
        print("FAILED checks:", FAILS)
        sys.exit(1)
    print("ALL CHECKS PASSED")
    sys.exit(0)
