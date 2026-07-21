"""Self-contained Zone-C strip row bounds for fixed odd m in {9,11,13}, n=m-2.

Re-implements the [ZC] (proof_zoneC_analytic_v2.tex) interval brackets and the
three assembled row bounds Psi_deep, Psi_sh, Psi_II^{ZC} directly (with the
m-uniform constants 13->n, 14->m-1, 15->m), and ADDS the new MVT Case-II bound

    Psi_II^{MVT}(E) = n x_U^{n-1} / ( p_lo * alpha(e_R) * m * K^- * f^- ),
    p_lo = (1+e_L)/2,

which upper-bounds the SAME Case-II ratio Def_m/(m K_2 f d) via
  alpha Def_m <= (n x^{n-1}/p) N,  N = d - ell^{m-1}(q-L) <= d   (q>L, ell>0),
so Def_m <= (n x^{n-1}/(p alpha)) d and the d cancels against the floor m K2 f d.
Both Psi_II^{ZC} and Psi_II^{MVT} are valid sufficient conditions for the
Case-II target on E, so the effective Case-II bound is their MIN.

No greedy/adaptive cover here: the covers are the FROZEN rational tables below.
"""
import math
from fractions import Fraction as Fr

def alpha(u):  return (1 - u) / 2.0
def delta(u):  return (1 - 3 * u) / 6.0

# ---------------------------------------------------------------- brackets
def brackets(eL, eR, m):
    eLf, eRf = float(eL), float(eR); n = m - 2
    aR, aL = alpha(eRf), alpha(eLf)
    qbar = max(1/3.0, aR - eRf**2 / (1 - eRf)**2)
    D    = min(eRf**2 / (1 - eRf)**2, delta(eLf))
    Lam  = D / qbar
    lamL = math.log((1 + eLf) / (1 - eLf))
    G2h  = 2 * eRf / (1 - eRf)
    Y    = math.sqrt(eRf * (1 - eRf) / 2) / qbar
    ell2_over_e = 2/(1 - eLf) - D*(eRf + D)/(aR**2 * eLf)
    gamma = ell2_over_e * (1 - Y**n) * math.log(1 + G2h) / G2h
    a    = lamL * gamma * eLf
    wmin = 2*gamma*max((1 - eRf)**2 * qbar, eLf**2/(3*delta(eLf)))
    vplus= min(eRf/(2*(1 - eRf)**2 * qbar), 3*delta(eLf)/lamL)
    hplus= math.exp(-1 + vplus/2)
    xU   = (1 - eLf)/(1 + eLf)
    yU   = math.sqrt(eRf*(1 - eRf)/2)/(aR + eRf)
    cminus = 2*(1 - xU**(m-1))*(1 - yU**(m-1))/((1 + xU)*(1 + yU))
    fminus = aR - math.sqrt(eRf*(1 - eRf)/2)
    Kminus = math.sqrt(2*aR)*(1 - yU**(m-1))/(2*aL**3*(1 + yU))
    p_lo   = (1 + eLf)/2                       # p = 1-q >= 1-alpha = (1+e)/2
    return dict(n=n, aR=aR, aL=aL, qbar=qbar, D=D, Lam=Lam, lamL=lamL, gamma=gamma,
                a=a, wmin=wmin, hplus=hplus, xU=xU, yU=yU, cminus=cminus,
                fminus=fminus, Kminus=Kminus, p_lo=p_lo)

# ---------------------------------------------------------------- row bounds
def row(eL, eR, m):
    """Return (Psi_max, arg, detail) using max(deep, sh?, min(II_ZC, II_MVT))."""
    B = brackets(eL, eR, m); n = B['n']
    Psi_deep = B['hplus']*math.exp(-max(B['wmin'], m*B['lamL'])) / \
               (2*B['gamma']*B['aR']*B['cminus']*B['qbar']**2)
    # shallow: applicable only if Lam > gamma e_L / m
    if B['Lam'] > B['gamma']*float(eL)/m:
        Dstar = min(B['Lam'], max(B['a'], B['gamma']*float(eL)/m))
        Psi_sh = B['hplus']*(float(eR)/2)*math.exp(-B['a']/Dstar) / \
                 (m*B['aR']*B['cminus']*B['qbar']**2*Dstar)
    else:
        Psi_sh = None
    Psi_II_ZC  = B['hplus']*math.exp(-B['a']/B['Lam']) / \
                 (m*B['lamL']*B['aR']*B['Kminus']*B['fminus']*B['qbar'])
    Psi_II_MVT = n*B['xU']**(n-1) / (B['p_lo']*B['aR']*m*B['Kminus']*B['fminus'])
    Psi_II = min(Psi_II_ZC, Psi_II_MVT)
    cands = [('deep', Psi_deep), ('II', Psi_II)]
    if Psi_sh is not None: cands.append(('sh', Psi_sh))
    arg, mx = max(cands, key=lambda t: t[1])
    return mx, arg, dict(deep=Psi_deep, sh=Psi_sh, II_ZC=Psi_II_ZC,
                         II_MVT=Psi_II_MVT, II=Psi_II)

# ---------------------------------------------------------------- FROZEN covers
# [ZC] base breakpoints (its Table 1), extended by one tail point to the corner.
_ZC = [Fr(1,60),Fr(1,48),Fr(1,40),Fr(1,32),Fr(1,25),Fr(1,20),Fr(1,16),Fr(1,13),
       Fr(1,10),Fr(1,8),Fr(3,20),Fr(17,100),Fr(9,50),Fr(19,100),Fr(1,5),Fr(21,100),
       Fr(11,50),Fr(6,25),Fr(13,50),Fr(7,25),Fr(29,100),Fr(3,10)]

def _upto(hi):
    e = [x for x in _ZC if x <= hi]
    if e[-1] != hi: e.append(hi)
    return e

def _bisect(edges, pairs):
    """Replace each (a,b) interval in edges by k equal sub-intervals."""
    out = []
    for i in range(len(edges)-1):
        a, b = edges[i], edges[i+1]
        k = pairs.get((a, b))
        if k:
            out += [a + (b-a)*Fr(j, k) for j in range(k)]
        else:
            out.append(a)
    out.append(edges[-1])
    return out

# strip end e*_m = corner start (m=11,13) ; m=9 strip ends at 29/100, sliver to 31/100
STRIP_HI = {9: Fr(29,100), 11: Fr(91,300), 13: Fr(29,100)}
# explicit bisections (fixed, displayed): interval -> number of equal parts
_BIS = {9: {(Fr(1,60),Fr(1,48)): 2, (Fr(13,50),Fr(7,25)): 2, (Fr(7,25),Fr(29,100)): 2},
        11: {(Fr(1,60),Fr(1,48)): 2}, 13: {}}

def strip_cover(m):
    return _bisect(_upto(STRIP_HI[m]), _BIS[m])

# ---- m=9 sliver: trivial R_9<=0 region t<=t_triv, then floored (e,t) cells ----
SLIVER_E    = [Fr(29,100), Fr(59,200), Fr(3,10), Fr(61,200), Fr(31,100)]  # 0.29..0.31
SLIVER_TTRIV= Fr(64,100)                                    # R_9<=0 for t<=t_triv
SLIVER_TB   = [Fr(64,100), Fr(73,100), Fr(82,100), Fr(91,100), Fr(1)]  # floored t-bands

# corner delta-caps (unchanged from verified corner) : e_corner = 1/3 - 2 Dc
CORNER_DC = {9: Fr(7,600), 11: Fr(9,600), 13: Fr(13,600)}

if __name__ == "__main__":
    for m in (9,11,13):
        ed = strip_cover(m); worst = 0; arg=None
        for i in range(len(ed)-1):
            v,a,_ = row(ed[i], ed[i+1], m)
            if v>worst: worst=v; arg=(ed[i],ed[i+1],a)
        print(f"m={m}: {len(ed)-1} strip rows on [1/60,{STRIP_HI[m]}], worst={worst:.4f} at {arg}")
