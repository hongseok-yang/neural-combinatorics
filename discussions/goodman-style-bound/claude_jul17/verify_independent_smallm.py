#!/usr/bin/env python3
"""INDEPENDENT verifier for smallm_regionII_proof_v2.tex.

Stages (run: python3 verify_independent_smallm.py [stage...]):
  grid      - dense float grid checks of every displayed inequality
  consts    - exact Fraction checks of every decimal constant / table
  corners   - Fraction interval spot checks at domain extremes
  bern      - INDEPENDENT re-derivation of Prop 4.4 Bernstein certificates
  moderate  - INDEPENDENT exact-rational subdivision for Prop 5.1
All polynomial/interval code here is written from the formulas STATED in the
tex, not imported from author code.
"""
import sys, math
from fractions import Fraction as F
from math import isqrt, comb
import numpy as np

MS = [3, 5, 7, 9, 11, 13]
DELTA = {3: F(1, 40), 5: F(1, 40), 7: F(1, 40), 9: F(1, 40),
         11: F(1, 80), 13: F(1, 80)}
TSTAR = {3: F(31, 100), 5: F(42, 100), 7: F(41, 100), 9: F(39, 100),
         11: F(49, 100), 13: F(48, 100)}

FAIL = []
def check(name, ok, detail=""):
    tag = "ok " if ok else "FAIL"
    print(f"[{tag}] {name} {detail}")
    if not ok:
        FAIL.append(f"{name}: {detail}")

# ---------- float model ----------
def model(m, e, k):
    """All quantities from (e,kappa). Returns dict or None if inadmissible."""
    al = (1 - e) / 2
    d = k * e
    q = al - d
    p = 1 - q
    if not (1/3 < q < 1/2):
        return None
    rq = (math.sqrt(q * q + 4 * q) - q) / 2
    if not (q < al <= rq + 1e-15):
        return None
    L2 = p * q - al * al
    if L2 < 0:
        return None
    L = math.sqrt(L2)
    f = al - L
    km = lambda lam: (p ** (m - 1) - lam ** (m - 1)) / (p + lam)
    A = 2 * L ** (m - 2) + m * km(al)
    B = 2 * L ** (m - 2) + m * km(L)
    R = al ** m + L ** m - p * q ** (m - 1)
    C = B * f * math.sqrt(2 * al) * e * e / (4 * al * al)
    xi = 4 * al * al * d / (e * e)
    rho = (A / B) * math.sqrt(al) / (2 * math.sqrt(2) * f)
    # psi closed form (R2 Prop psi-forms), cross-checked below
    xic = (2 * rho + 1) / (4 * (rho + 1) ** 2)
    if xi >= xic:
        psi = xi - 1 / (4 * (1 + rho))
    else:
        vm = (1 - math.sqrt(1 - 4 * xi)) / 2
        psi = rho * vm * vm
    return dict(al=al, d=d, q=q, p=p, L=L, f=f, A=A, B=B, R=R, C=C,
                xi=xi, rho=rho, psi=psi, e=e, k=k,
                x=al / p, ell=L / al, y=L / p, u=1 - al / p,
                delta=al - 1/3)

def psi_brute(xi, rho):
    vs = np.linspace(0, 1, 4001)
    return np.min(rho * vs**2 + np.maximum(xi - vs + vs**2, 0.0))

def Tm_holds(m, M):
    al, A, B, R, f, d, e = (M[k] for k in ("al", "A", "B", "R", "f", "d", "e"))
    lhs = 4 * al**2 * A * R
    rhs = 4 * al**2 * A * math.sqrt(2 * al) * B * f * d - e**2 * B**2 * f**2
    return lhs <= rhs + 1e-15 * abs(rhs), (rhs - lhs)

def stage_grid():
    print("== stage grid ==")
    NE, NK = 400, 400
    for m in MS:
        worst = {"target": 1e9, "relax1": 1e9, "relax2": 1e9}
        bad = {k: 0 for k in ("target", "psi", "gate", "cor", "smalle_first",
                              "red", "F", "tail", "band_Tm", "mod_Tm",
                              "AB", "chord", "geom")}
        npts = 0
        for e in np.linspace(1e-5, 1/3 - 1e-5, NE):
            kmax = (1 - e) / (1 + e)
            kq = (1 - 3 * e) / (6 * e)
            khi = min(kmax, kq)
            for k in np.linspace(1e-6, khi * (1 - 1e-9), NK):
                M = model(m, e, k)
                if M is None:
                    continue
                npts += 1
                al, d, q, p, L, f, A, B, R, C, xi, rho, psi = (
                    M[t] for t in ("al", "d", "q", "p", "L", "f", "A", "B",
                                    "R", "C", "xi", "rho", "psi"))
                x, ell = M["x"], M["ell"]
                # structural
                if not (0 < A < B and L < q < al < p and ell**2 <= e/al + 1e-12):
                    bad["AB"] += 1
                # main target
                marg = C * psi - R
                worst["target"] = min(worst["target"], marg / max(abs(R), 1e-300))
                if marg < -1e-13:
                    bad["target"] += 1
                # relax chain eq (2.2)
                r1 = math.sqrt(2*al) * B * f * (d - e*e/(16*al*al*(1+rho)))
                r2 = math.sqrt(2*al) * B * f * d - e*e*B*B*f*f/(4*al*al*A)
                if C * psi < r1 - 1e-13 or r1 < r2 - 1e-13:
                    bad["psi"] += 1
                # gate
                if R > 0 and not ((m-1)*k > x*(1 + k - ell**(m-2)) - 1e-13):
                    bad["gate"] += 1
                if R > 0 and e <= 1/60:
                    kmin = 0.7183 if m == 3 else 0.763/(m-1)
                    eps = e*e/(16*al*al*(1+rho)*d)
                    if not (k > kmin and xi >= 3.68 - 1e-9 and eps <= 0.068
                            and eps <= e/(4*(1-e)**2*k) + 1e-15):
                        bad["cor"] += 1
                    # Prop 3.1 first inequality
                    if R > math.sqrt(2*al)*B*f*(d - e*e/(16*al*al*(1+rho))) + 1e-15:
                        bad["smalle_first"] += 1
                    # eq:red
                    y = M["y"]
                    eps_red = eps
                    lhs = math.sqrt(1-e)*(1-ell)*(1-y**(m-1))*(1-eps_red)/(1+y)
                    Lam = x**(m-2)*(e/al)**(m/2-1)/(m*k)
                    rhs = x**(m-2)*((m-1)/(m*x) - (1+1/k)/m) + Lam
                    if lhs < rhs - 1e-13:
                        bad["red"] += 1
                    # eq:F for m>=5
                    if m >= 5:
                        z = (m-2)*M["u"]
                        cm = (m-3)/(2*(m-2))
                        G0 = 2.8524*math.sqrt(e)+0.51*e+(2.04*e)**2
                        sig = 1.21*(2.04*e)**((m-2)/2)
                        Fv = (1-G0-eps)*(1+z+cm*z*z)-1/x+(2+1/k)/m-sig
                        if Fv < -1e-13:
                            bad["F"] += 1
                # band
                dl = M["delta"]
                if R > 0 and dl <= float(DELTA[m]):
                    if not (d/dl > float(TSTAR[m])):
                        bad["tail"] += 1
                    ok, _ = Tm_holds(m, M)
                    if not ok:
                        bad["band_Tm"] += 1
                # moderate
                if R > 0 and 1/60 <= e <= float(F(1,3) - 2*DELTA[m]):
                    ok, _ = Tm_holds(m, M)
                    if not ok:
                        bad["mod_Tm"] += 1
        allok = all(v == 0 for v in bad.values())
        check(f"grid m={m}", allok,
              f"pts={npts} worst_rel_target={worst['target']:.2e} bad={ {k:v for k,v in bad.items() if v} }")
    # psi closed form vs brute, random
    rng = np.random.default_rng(0)
    ok1 = ok2 = True; mx = 0
    for _ in range(300):
        xi = rng.uniform(0, 3); rho = rng.uniform(0, 50)
        xic = (2*rho+1)/(4*(rho+1)**2)
        psi = xi - 1/(4*(1+rho)) if xi >= xic else rho*((1-math.sqrt(1-4*xi))/2)**2
        pb = psi_brute(xi, rho)
        ok1 &= psi <= pb + 1e-11              # true min <= grid min, sharp side
        ok2 &= psi >= pb - 103 * (1/4000) / 2  # grid resolution slack (|f'|<=103)
        mx = max(mx, abs(psi - pb))
    check("psi closed form vs brute min", ok1 and ok2, f"maxdiff={mx:.1e}")
    # chord lemma on [0,1/40]
    ds = np.linspace(0, 1/40, 20001)
    ok = np.all((0.8164 + 1.2*ds)**2 <= 2/3 + 2*ds)
    check("chord w_l(d)<=sqrt(2a)", bool(ok))

# ---------- stage consts: exact Fraction verification of decimals ----------
def frac_sqrt_lt(a: F, b: F) -> bool:
    """sqrt(a) < b exactly (a,b>=0)."""
    return a < b * b

def stage_consts():
    print("== stage consts ==")
    check("59/63 > 0.9365", F(59, 63) > F(9365, 10000))
    check("1.4262^2 > 120/59", F(14262, 10000)**2 > F(120, 59))
    check("1.4262/sqrt60 < 0.1842", F(14262, 10000)**2 < F(1842, 10000)**2 * 60)
    check("(1-.51e)^2<=1-e on (0,1/60]", F(2, 100) / F(2601, 10000) >= F(1, 60) and True,
          "-0.02e+0.2601e^2<=0 iff e<=0.02/0.2601=0.0768>1/60")
    check("40/21 >= 1.9047", F(40, 21) >= F(19047, 10000))
    check("0.9365*0.8158 > 0.763", F(9365, 10000)*F(8158, 10000) > F(763, 1000))
    check("0.9365*0.8158/1.0635 > 0.7183",
          F(9365, 10000)*F(8158, 10000) > F(7183, 10000)*F(10635, 10000))
    check("(59/60)^2*0.763*5 > 3.68", F(59, 60)**2*F(763, 1000)*5 > F(368, 100))
    check("1/(4*3.68) < 0.068", F(1, 1) < F(68, 1000)*4*F(368, 100))
    # m=3 case numbers
    check("2.04/60 = 0.034", F(204, 100)/60 == F(34, 1000))
    check("1-0.3684-0.034-0.068-0.0085 > 0.52",
          1 - F(3684,10000) - F(34,1000) - F(68,1000) - F(85,10000) > F(52,100))
    check("1.4262/(3*0.7183) <= 0.662", F(14262,10000) <= F(662,1000)*3*F(7183,10000))
    check("0.9365*2/3 >= 0.6243", F(9365,10000)*2 >= F(6243,10000)*3)
    check("0.1291^2 > 1/60", F(1291, 10000)**2 > F(1, 60))
    check("2/3-0.6243+0.662*0.1291 < 0.128",
          F(2,3) - F(6243,10000) + F(662,1000)*F(1291,10000) < F(128,1000))
    # 5<=m<=13 constants
    check("1.0711*1.9047 >= 2.04", F(10711,10000)*F(19047,10000) >= F(204,100))
    check("2.8524/7.7459<0.36825 & 7.7459^2<60",
          F(77459, 10000)**2 < 60 and F(28524, 10000) < F(36825, 100000)*F(77459, 10000))
    check("0.51/60 = 0.0085", F(51, 100)/60 == F(85, 10000))
    check("(2.04/60)^2 = 0.001156", (F(204, 100)/60)**2 == F(1156, 1000000))
    check("Gamma0(1/60) < 0.378",
          F(36825, 100000) + F(85, 10000) + F(1156, 1000000) < F(378, 1000))
    check("5/4*(60/59)^2 <= 1.293", F(5, 4)*F(60, 59)**2 <= F(1293, 1000))
    check("1.293/60 = 0.02155", F(1293, 1000)/60 == F(2155, 100000))
    check("Gamma1(1/60) < 0.3995",
          F(36825, 100000) + F(85, 10000) + F(1156, 1000000) + F(2155, 100000) < F(3995, 10000))
    check("1-0.378-0.068-1.0711/3 > 0.19",
          1 - F(378, 1000) - F(68, 1000) - F(10711, 30000) > F(19, 100))
    check("7/13-0.378-0.068-0.0076 > 0.084",
          F(7, 13) - F(378, 1000) - F(68, 1000) - F(76, 10000) > F(84, 1000))
    check("1-0.3995-1.0711/3 > 0.24", 1 - F(3995, 10000) - F(10711, 30000) > F(24, 100))
    check("1.9047*1.2 >= 2.2856", F(19047, 10000)*F(12, 10) >= F(22856, 10000))
    check("2.2856*0.6005 = 1.3725028", F(22856, 10000)*F(6005, 10000) == F(13725028, 10**7))
    check("2.2856*1.0711+1.803 = 4.25110616",
          F(22856, 10000)*F(10711, 10000) + F(1803, 1000) == F(425110616, 10**8))
    check("(2.04)^2 = 4.1616 & 0.51+1.293 = 1.803",
          F(204, 100)**2 == F(41616, 10000) and F(51, 100)+F(1293, 1000) == F(1803, 1000))
    c1 = lambda m: F(13725028, 10**7)*(m-2) - F(425110616, 10**8)
    check("c1_13 < 10.847", c1(13) < F(10847, 1000), f"c1_13={float(c1(13))}")
    check("1.4262*7.745 > 11.045 & 7.745^2 < 60",
          F(14262, 10000)*F(7745, 1000) > F(11045, 1000) and F(7745, 1000)**2 < 60)
    # Table tab:smalle
    tab_c1 = {5: F(-13360, 10**5), 7: F(261140, 10**5), 9: F(535641, 10**5),
              11: F(810141, 10**5), 13: F(1084642, 10**5)}
    tab_sig = {5: F(76, 10**4), 7: F(258, 10**6), 9: F(88, 10**7),
               11: F(3, 10**7), 13: F(2, 10**8)}
    tab_G = {5: F(2207, 10**4), 7: F(1024, 10**4), 9: F(531, 10**4),
             11: F(383, 10**4), 13: F(421, 10**4)}
    tab_beta = {5: F(35704, 10**5), 7: F(21422, 10**5), 9: F(15302, 10**5),
                11: F(11902, 10**5), 13: F(9738, 10**5)}
    for m in [5, 7, 9, 11, 13]:
        check(f"c1 underbar m={m} (truncated down, within 1e-5)",
              tab_c1[m] <= c1(m) < tab_c1[m] + F(1, 10**5), f"exact={c1(m)}")
        check(f"beta_m m={m} rounded up",
              tab_beta[m] >= F(10711, 10000)/(m-2) > tab_beta[m] - F(1, 10**5))
        # sigma_m(1/60)=1.21*(0.034)^{(m-2)/2} <= tab_sig  (odd power of sqrt)
        n = m - 2
        v = F(121, 100) * F(34, 1000)**((n - 1)//2)  # * sqrt(0.034)
        # need v * sqrt(0.034) <= tab_sig  <=> v^2*0.034 <= tab_sig^2
        check(f"sigma bound m={m}", v*v*F(34, 1000) <= tab_sig[m]**2)
        Gb = F(3, m) + tab_c1[m]/60 - F(36825, 10**5) - F(11561, 10**7) - tab_sig[m]
        check(f"Ghat_flat m={m} (>= table, table>0)",
              Gb >= tab_G[m] and tab_G[m] > 0, f"exact={float(Gb):.6f} table={float(tab_G[m])}")
    check("4.1616/3600 < 0.0011561", F(41616, 10000)/3600 < F(11561, 10**7))
    # chord endpoints
    check("0.8164^2 < 2/3", F(8164, 10000)**2 < F(2, 3))
    check("(0.8164+0.03)^2 < 2/3+1/20", (F(8164, 10000)+F(3, 100))**2 < F(2, 3)+F(1, 20))
    # tail table: c_m, w_m, r_m and integer comparisons
    for m in MS:
        Dm, ts = DELTA[m], TSTAR[m]
        e = F(1, 3) - 2*Dm
        cm = e / (2*(m-1)*Dm)
        wm = (1 - 6*Dm)/(1 + 3*Dm)
        rm = 1 - ts/cm
        tab = {3: (F(34,43), F(17,6), F(757,850)), 5: (F(34,43), F(17,12), F(299,425)),
               7: (F(34,43), F(17,18), F(481,850)), 9: (F(34,43), F(17,24), F(191,425)),
               11: (F(74,83), F(37,30), F(223,370)), 13: (F(74,83), F(37,36), F(493,925))}
        check(f"tail table m={m}", (wm, cm, rm) == tab[m], f"{wm},{cm},{rm}")
        check(f"tail ineq m={m}: w^(m-2) < r^2", wm**(m-2) < rm**2)
        check(f"tail r_m in (0,1) m={m}", 0 < rm < 1)
    # tail Step 2: phi_m(dl) >= phi_m(Delta_m) on (0,Delta_m], and h concave
    for m in MS:
        Dm = float(DELTA[m]); nu = (m - 2)/2
        ds = np.linspace(1e-9, Dm, 20001)
        w = (1 - 6*ds)/(1 + 3*ds)
        h = 1 - w**nu
        phi = (1/3 - 2*ds)/(2*(m-1)*ds)*h
        wD = (1 - 6*Dm)/(1 + 3*Dm)
        phiD = (1/3 - 2*Dm)/(2*(m-1)*Dm)*(1 - wD**nu)
        ok = np.all(phi >= phiD - 1e-12)
        hh = 1 - ((1 - 6*ds)/(1 + 3*ds))**nu
        conc = np.all(np.diff(np.diff(hh)) <= 1e-15)
        check(f"tail step2 m={m}: phi>=phi(Delta), h concave", bool(ok and conc))
    # displayed big integers
    check("34*850^2=24565000<24641107=43*757^2",
          34*850**2 == 24565000 and 43*757**2 == 24641107 and 24565000 < 24641107)
    check("m=5 ints", 34**3*425**2 == 7099285000 and 43**3*299**2 == 7108005307)
    check("m=7 ints", 34**5*850**2 == 32827093840000 and 43**5*481**2 == 34012020380923)
    check("m=9 ints", 34**7*425**2 == 9487030119760000 and 43**7*191**2 == 9916214751794467)
    check("m=11 ints", 74**9*370**2 == 9109382235108373145600
          and 83**9*223**2 == 9296351954199516700787)
    check("m=13 ints", 74**11*925**2 == 311768606996584070908160000
          and 83**11*493**2 == 313006138444263224418858083)

# ---------- stage bern: independent Prop 4.4 certificate ----------
# Polynomials in (delta, s) as dicts {(i,j): Fraction}.
def padd(a, b):
    r = dict(a)
    for k, v in b.items():
        r[k] = r.get(k, F(0)) + v
        if r[k] == 0: del r[k]
    return r
def pscal(c, a):
    return {k: c * v for k, v in a.items()} if c else {}
def pmul(a, b):
    r = {}
    for (i1, j1), v1 in a.items():
        for (i2, j2), v2 in b.items():
            k = (i1 + i2, j1 + j2)
            r[k] = r.get(k, F(0)) + v1 * v2
    return {k: v for k, v in r.items() if v != 0}
def ppow(a, n):
    r = {(0, 0): F(1)}
    for _ in range(n): r = pmul(r, a)
    return r
def peval(a, dv, sv):
    return sum(v * dv**i * sv**j for (i, j), v in a.items())

def build_PQ(m):
    one = {(0, 0): F(1)}
    AL = {(0, 0): F(1, 3), (1, 0): F(1)}          # alpha = 1/3 + delta
    E  = {(0, 0): F(1, 3), (1, 0): F(-2)}         # e = 1/3 - 2 delta
    D  = {(1, 0): F(1), (1, 1): F(-1)}            # d = (1-s) delta
    Qq = {(0, 0): F(1, 3), (1, 1): F(1)}          # q = 1/3 + s delta
    Pp = {(0, 0): F(2, 3), (1, 1): F(-1)}         # p = 2/3 - s delta
    L2 = padd(pmul(Pp, Qq), pscal(F(-1), pmul(AL, AL)))
    # check stated L2 formula
    L2stated = {(0, 0): F(1, 9), (1, 0): F(-2, 3), (1, 1): F(1, 3),
                (2, 0): F(-1), (2, 2): F(-1)}
    assert L2 == {k: v for k, v in L2stated.items() if v != 0}, "L2 formula mismatch"
    # k_m(alpha) = sum_{j=0}^{m-2} (-1)^j p^{m-2-j} alpha^j
    kma = {}
    for j in range(m - 1):
        kma = padd(kma, pscal(F((-1)**j), pmul(ppow(Pp, m-2-j), ppow(AL, j))))
    Ae = pscal(F(m), kma)
    Ao = pscal(F(2), ppow(L2, (m - 3)//2))
    # k_m(L) = (p-L) * S,  S = sum_{i=0}^{(m-3)/2} p^{m-3-2i} L2^i
    S = {}
    for i in range((m - 3)//2 + 1):
        S = padd(S, pmul(ppow(Pp, m - 3 - 2*i), ppow(L2, i)))
    Be = padd(pscal(F(2), {}), pscal(F(m), pmul(Pp, S)))
    Bo = padd(pscal(F(2), ppow(L2, (m - 3)//2)), pscal(F(-m), S))
    Re = padd(ppow(AL, m), pscal(F(-1), pmul(Pp, ppow(Qq, m - 1))))
    Ro = ppow(L2, (m - 1)//2)
    fe, fo = AL, pscal(F(-1), one)
    def pairmul(x, y):
        return (padd(pmul(x[0], y[0]), pmul(L2, pmul(x[1], y[1]))),
                padd(pmul(x[0], y[1]), pmul(x[1], y[0])))
    ABf = pairmul(pairmul((Ae, Ao), (Be, Bo)), (fe, fo))
    Bf = pairmul((Be, Bo), (fe, fo))
    Bf2 = pairmul(Bf, Bf)
    AR = pairmul((Ae, Ao), (Re, Ro))
    wl = {(0, 0): F(2041, 2500), (1, 0): F(6, 5)}
    c4a2d = pmul(wl, pscal(F(4), pmul(pmul(AL, AL), D)))
    E2 = pmul(E, E); a24 = pscal(F(4), pmul(AL, AL))
    P = padd(padd(pmul(c4a2d, ABf[0]), pscal(F(-1), pmul(E2, Bf2[0]))),
             pscal(F(-1), pmul(a24, AR[0])))
    Qp = padd(padd(pmul(c4a2d, ABf[1]), pscal(F(-1), pmul(E2, Bf2[1]))),
              pscal(F(-1), pmul(a24, AR[1])))
    return P, Qp, L2

def bern_nonneg(poly, Dm, smax, name):
    """Check all 2-d Bernstein coefficients of poly on [0,Dm]x[0,smax] >= 0.
    Uses integer form c_ij = sum_{k<=i,l<=j} C(n1-k,i-k) C(n2-l,j-l) a_kl."""
    # rescale to unit box
    a = {(i, j): v * Dm**i * smax**j for (i, j), v in poly.items()}
    if not a:
        return True, 0
    n1 = max(i for i, _ in a); n2 = max(j for _, j in a)
    den = 1
    for v in a.values(): den = den * v.denominator // math.gcd(den, v.denominator)
    ai = {k: int(v * den) for k, v in a.items()}
    neg = 0; mn = None
    for i in range(n1 + 1):
        for j in range(n2 + 1):
            c = 0
            for (k, l), v in ai.items():
                if k <= i and l <= j:
                    c += comb(n1 - k, i - k) * comb(n2 - l, j - l) * v
            if mn is None or c < mn: mn = c
            if c < 0: neg += 1
    return neg == 0, (n1, n2, neg, "min_coeff_sign=" + ("0" if mn == 0 else ("+" if mn > 0 else "-")))

def stage_bern():
    print("== stage bern ==")
    for m in MS:
        P, Qp, L2 = build_PQ(m)
        # sanity: P + L*Q == G at random rational points (float compare)
        rng = np.random.default_rng(m)
        okG = True
        for _ in range(25):
            dv = F(int(rng.integers(1, 1000)), 40 * 1000)   # delta in (0, 1/40)
            sv = F(int(rng.integers(0, 1000)), 1000)
            al = F(1,3) + dv; e = F(1,3) - 2*dv; d = (1 - sv)*dv
            q = F(1,3) + sv*dv; p = 1 - q
            L2v = p*q - al*al; L = math.sqrt(L2v)
            f = float(al) - L
            km = lambda lam: (float(p)**(m-1) - lam**(m-1)) / (float(p) + lam)
            A = 2*L**(m-2) + m*km(float(al)); B = 2*L**(m-2) + m*km(L)
            R = float(al)**m + L**m - float(p)*float(q)**(m-1)
            wl = float(F(2041,2500) + F(6,5)*dv)
            G = wl*4*float(al)**2*float(d)*A*B*f - float(e)**2*(B*f)**2 - 4*float(al)**2*A*R
            G2 = float(peval(P, dv, sv)) + L*float(peval(Qp, dv, sv))
            if abs(G - G2) > 1e-9 * max(1, abs(G)):
                okG = False
        check(f"bern m={m}: P+LQ == G (random rational pts)", okG)
        # H = L2*Q^2 - P^2, delta | H
        H = padd(pmul(L2, pmul(Qp, Qp)), pscal(F(-1), pmul(P, P)))
        divis = all(i >= 1 for (i, j) in H)
        check(f"bern m={m}: delta | H", divis)
        K = {(i - 1, j): v for (i, j), v in H.items()}
        okQ, infoQ = bern_nonneg(Qp, DELTA[m], 1 - TSTAR[m], "Q")
        okK, infoK = bern_nonneg(K, DELTA[m], 1 - TSTAR[m], "K")
        check(f"bern m={m}: Bernstein(Q)>=0 on box", okQ, str(infoQ))
        check(f"bern m={m}: Bernstein(H/delta)>=0 on box", okK, str(infoK))

# ---------- interval arithmetic over Fractions ----------
SC = 1 << 80
def rnd(iv):
    lo, hi = iv
    return (F(math.floor(lo * SC), SC), F(math.ceil(hi * SC), SC))
def iadd(a, b): return (a[0] + b[0], a[1] + b[1])
def isub(a, b): return (a[0] - b[1], a[1] - b[0])
def imul(a, b):
    c = [a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1]]
    return rnd((min(c), max(c)))
def idivpos(a, b):
    assert b[0] > 0
    c = [a[0]/b[0], a[0]/b[1], a[1]/b[0], a[1]/b[1]]
    return rnd((min(c), max(c)))
def ipow_nonneg(a, n):  # a.lo >= 0
    return rnd((a[0]**n, a[1]**n))
def isqrt_iv(a):  # a.lo >= 0
    k = 1 << 40
    lo = a[0]; hi = a[1]
    slo = F(isqrt((lo.numerator * k * k) // lo.denominator), k) if lo > 0 else F(0)
    shi = F(isqrt((hi.numerator * k * k) // hi.denominator) + 1, k)
    return (slo, shi)
def iconst(c): return (F(c), F(c))

def certify_box(m, e1, e2, k1, k2, depth, stats, maxdepth=42):
    stats["boxes"] += 1
    # discard if wholly inadmissible
    if k1 * e1 >= (1 - 3*e1)/6:            # q <= 1/3 everywhere
        stats["discard"] += 1; return True
    if k1 > (1 - e1)/(1 + e1):             # kappa > kappa_max everywhere
        stats["discard"] += 1; return True
    e = (e1, e2); kp = (k1, k2)
    al = ((1 - e2)/2, (1 - e1)/2)
    dmax = min(k2 * e2, (1 - 3*e1)/6)      # admissible: d < delta
    d = (k1 * e1, dmax)
    q = (max(al[0] - d[1], F(1, 3)), al[1] - d[0])
    p = (1 - q[1], 1 - q[0])
    L2 = isub(imul(p, q), imul(al, al))
    L2 = (max(L2[0], F(0)), max(L2[1], F(0)))
    L = isqrt_iv(L2)
    f = (max(al[0] - L[1], F(0)), al[1] - L[0])
    # k_m at alpha and L (num >= 0 pointwise on admissible; keep general)
    def km_iv(lam):
        num = (p[0]**(m-1) - lam[1]**(m-1), p[1]**(m-1) - lam[0]**(m-1))
        den = iadd(p, lam)
        return idivpos(num, den)
    Lm2 = imul(ipow_nonneg(L2, (m-3)//2), L)      # L^{m-2}
    A = iadd((2*Lm2[0], 2*Lm2[1]), imul(iconst(m), km_iv(al)))
    B = iadd((2*Lm2[0], 2*Lm2[1]), imul(iconst(m), km_iv(L)))
    A = (max(A[0], F(0)), A[1]); B = (max(B[0], F(0)), B[1])
    Lm = imul(ipow_nonneg(L2, (m-1)//2), L)
    R = isub(iadd(ipow_nonneg(al, m), Lm), imul(p, ipow_nonneg(q, m-1)))
    if R[1] <= 0:
        stats["Rneg"] += 1; return True
    s2a = isqrt_iv((2*al[0], 2*al[1]))
    a2 = imul(al, al)
    lhs_hi = 4 * a2[1] * A[1] * R[1]
    rhs_lo = 4 * a2[0] * A[0] * s2a[0] * B[0] * f[0] * d[0] \
             - e[1]**2 * B[1]**2 * f[1]**2
    if lhs_hi <= rhs_lo:
        stats["Tm"] += 1; return True
    if depth >= maxdepth or stats["boxes"] > 400000:
        stats["stuck"].append((float(e1), float(e2), float(k1), float(k2)))
        return False
    # bisect longest relative side
    if (e2 - e1) * 3 > (k2 - k1):
        emid = (e1 + e2)/2
        return (certify_box(m, e1, emid, k1, k2, depth+1, stats, maxdepth)
                & certify_box(m, emid, e2, k1, k2, depth+1, stats, maxdepth))
    kmid = (k1 + k2)/2
    return (certify_box(m, e1, e2, k1, kmid, depth+1, stats, maxdepth)
            & certify_box(m, e1, e2, kmid, k2, depth+1, stats, maxdepth))

def stage_moderate():
    print("== stage moderate ==")
    sys.setrecursionlimit(100000)
    for m in MS:
        ehi = F(1, 3) - 2*DELTA[m]
        stats = {"boxes": 0, "discard": 0, "Rneg": 0, "Tm": 0, "stuck": []}
        ok = certify_box(m, F(1, 60), ehi, F(0), F(1), 0, stats)
        check(f"moderate m={m} certified", ok and not stats["stuck"],
              f"boxes={stats['boxes']} discard={stats['discard']} "
              f"Rneg={stats['Rneg']} Tm={stats['Tm']} stuck={stats['stuck'][:3]}")

def stage_corners():
    print("== stage corners ==")
    # exact-rational spot points; verify target R <= C*psi via dual certificates
    # psi >= max(0, xi - 1/(4(1+rho)), lam*xi - lam^2/(4(rho+lam)) at lam=2*rho*xi if <=1)
    pts = []
    for m in MS:
        ehi = F(1, 3) - 2*DELTA[m]
        cand = [
            (F(1, 60), None), (F(1, 1000), None), (F(1, 100000), None),
            (ehi, None), (F(1, 3) - F(1, 10**6), None), (F(1, 6), None),
            (F(1, 4), None), (F(29, 100), None),
        ]
        for e, _ in cand:
            kmax = (1 - e)/(1 + e); kq = (1 - 3*e)/(6*e)
            khi = min(kmax, kq)
            for k in [khi * F(999999, 10**6), khi * F(9, 10), khi/2,
                      F(1, 10**6), khi * F(99, 100)]:
                pts.append((m, e, k))
    nbad = 0
    for (m, e, k) in pts:
        al = (1 - e)/2; d = k*e; q = al - d; p = 1 - q
        if not (F(1,3) < q < F(1,2)):  # inadmissible
            continue
        # alpha <= r(q)  <=>  alpha^2 + q*alpha - q <= 0
        if al*al + q*al - q > 0:
            continue
        L2 = p*q - al*al
        L = isqrt_iv((L2, L2)); f = (al - L[1], al - L[0])
        def km_iv(lam):
            num = (p**(m-1) - lam[1]**(m-1), p**(m-1) - lam[0]**(m-1))
            return idivpos(num, (p + lam[0], p + lam[1]))
        Lm2 = imul(ipow_nonneg((L2, L2), (m-3)//2), L)
        A = iadd((2*Lm2[0], 2*Lm2[1]), imul(iconst(m), km_iv((al, al))))
        B = iadd((2*Lm2[0], 2*Lm2[1]), imul(iconst(m), km_iv(L)))
        Lm = imul(ipow_nonneg((L2, L2), (m-1)//2), L)
        R_hi = al**m + Lm[1] - p*q**(m-1)
        s2a = isqrt_iv((2*al, 2*al)); sa = isqrt_iv((al, al))
        C = idivpos(imul(imul(B, f), imul(s2a, iconst(e*e))), (4*al*al, 4*al*al))
        xi = 4*al*al*d/(e*e)
        rho = idivpos(imul(A, sa), imul(iconst(2), imul(isqrt_iv(iconst(2)), imul(B, f))))
        # psi lower bounds via dual certificates
        cands = [F(0), xi - 1/(4*(1 + rho[0]))]
        lam = 2*rho[0]*xi
        if lam <= 1:
            cands.append(lam*xi - lam*lam/(4*(rho[0] + lam)))
        psi_lo = max(cands)
        margin_lo = C[0]*psi_lo - R_hi
        if not (R_hi <= 0 or margin_lo > 0):
            nbad += 1
            print(f"   corner UNRESOLVED m={m} e={float(e):.3g} k={float(k):.6g} "
                  f"R_hi={float(R_hi):.3e} marg_lo={float(margin_lo):.3e}")
    check("corner spot checks (target via dual certs)", nbad == 0,
          f"{len(pts)} points, unresolved={nbad}")

if __name__ == "__main__":
    stages = sys.argv[1:] or ["grid", "consts", "corners", "bern", "moderate"]
    if "grid" in stages: stage_grid()
    if "consts" in stages: stage_consts()
    if "corners" in stages: stage_corners()
    if "bern" in stages: stage_bern()
    if "moderate" in stages: stage_moderate()
    print("\n%d failures" % len(FAIL))
    for f_ in FAIL: print("  -", f_)
