# -*- coding: utf-8 -*-
"""C11 linear-piece certificate via joint (q,lam) Positivstellensatz, exact fix-up."""
import sympy as sp
import numpy as np
import cvxpy as cp
import pickle

q, lam = sp.symbols("q lam")
RHO = sp.Rational(97, 200)
a = [
 90*q**8 - 396*q**7 + 924*q**6 - 1386*q**5 + 1386*q**4 - 924*q**3 + 396*q**2 - 99*q + 11,
 80*q**7 - 308*q**6 + 616*q**5 - 770*q**4 + 616*q**3 - 308*q**2 + 88*q - 11,
 70*q**6 - 231*q**5 + 385*q**4 - 385*q**3 + 231*q**2 - 77*q + 11,
 60*q**5 - 165*q**4 + 220*q**3 - 165*q**2 + 66*q - 11,
 50*q**4 - 110*q**3 + 110*q**2 - 55*q + 11,
 40*q**3 - 66*q**2 + 44*q - 11, 30*q**2 - 33*q + 11, 20*q - 11, sp.Integer(10)]
P = sp.expand(sum(a[d]*lam**d for d in range(9)))

def monos(iq, jl):
    return [(i, j) for i in range(iq+1) for j in range(jl+1)]

# bases: sigma0 covers full (q^<=4, lam^<=4); sigma1,sigma2 (mult by deg-1 q) q^<=4? use q<=3 to keep deg<=8
b0 = monos(4, 4)        # 25 ; products reach (q^8, lam^8)
b1 = monos(3, 4)        # q-deg<=3 so q*sigma1 has q-deg<=7<=8 (residual representable by b0)
b3 = monos(3, 4)        # q(rho-q)*sigma3 : q-deg <= 2+6=8
weights = [(sp.Integer(1), b0), (q, b1), (RHO - q, b1), (q*(RHO-q), b3)]

# ---- SDP ----
Qs = [cp.Variable((len(b), len(b)), symmetric=True) for _, b in weights]
cons = [Q >> 0 for Q in Qs]
coeff = {}
for (w, b), Q in zip(weights, Qs):
    wmons = sp.Poly(w, q, lam).terms()
    for ai, (ia, ja) in enumerate(b):
        for ci, (ic, jc) in enumerate(b):
            for (eq, el), wc in wmons:
                e = (ia+ic+eq, ja+jc+el)
                coeff[e] = coeff.get(e, 0) + float(wc)*Q[ai, ci]
target = {e: float(c) for e, c in sp.Poly(P, q, lam).terms()}
constraints = list(cons)
for e in set(coeff) | set(target):
    constraints.append(coeff.get(e, 0) == target.get(e, 0.0))
cp.Problem(cp.Minimize(sum(cp.trace(Q) for Q in Qs)), constraints).solve(solver=cp.CLARABEL)
print("trace-min status, total trace =", sum(np.trace(Q.value) for Q in Qs))
Gf = [np.array(Q.value) for Q in Qs]
for i,Q in enumerate(Gf):
    w=np.linalg.eigvalsh(Q); print(f"  Q{i} rank~{int((w>1e-5*max(w.max(),1)).sum())}")

# ---- helper: form expansion of b^T G b as sympy poly ----
def form(G, b):
    return sp.expand(sum(G[i, j]*(q**b[i][0]*lam**b[i][1])*(q**b[j][0]*lam**b[j][1])
                         for i in range(len(b)) for j in range(len(b))))

def exact_match_gram(Pres, b, Gfloat, D):
    """Find rational symmetric G (len b) with b^T G b == Pres exactly, close to rounded Gfloat.
    Strategy: set G = round(Gfloat,D) then correct to satisfy each coeff exactly by adjusting
    a chosen representative entry per monomial-class (the 'diagonal-most' pair)."""
    n = len(b)
    G = [[sp.Rational(round(Gfloat[i, j]*D), D) for j in range(n)] for i in range(n)]
    # symmetrize
    for i in range(n):
        for j in range(i):
            v = (G[i][j]+G[j][i])/2
            G[i][j] = G[j][i] = v
    # current coeffs
    def coeffs_of(G):
        c = {}
        for i in range(n):
            for j in range(n):
                e = (b[i][0]+b[j][0], b[i][1]+b[j][1])
                c[e] = c.get(e, 0) + G[i][j]
        return c
    Pc = {e: cc for e, cc in sp.Poly(Pres, q, lam).terms()}
    Pc = {e: sp.nsimplify(cc) for e, cc in Pc.items()}
    cur = coeffs_of(G)
    # for each monomial class, pick representative pair (i,j) (prefer i==j) and add the deficit
    classes = {}
    for i in range(n):
        for j in range(n):
            e = (b[i][0]+b[j][0], b[i][1]+b[j][1])
            classes.setdefault(e, []).append((i, j))
    alle = set(cur) | set(Pc)
    for e in alle:
        deficit = sp.nsimplify(Pc.get(e, 0)) - cur.get(e, 0)
        if deficit == 0:
            continue
        pairs = classes.get(e, [])
        diag = [(i, j) for (i, j) in pairs if i == j]
        if diag:
            i, j = diag[0]
            G[i][j] += deficit
        else:
            i, j = pairs[0]
            G[i][j] += deficit/2
            G[j][i] += deficit/2
    return sp.Matrix(G)

from fractions import Fraction as Fr
def is_psd_rational(G, n):
    """robust pivoted LDL over Fraction; True iff PSD (all pivots>=0, zero-pivot rows zero)."""
    R=[[Fr(int(sp.Rational(G[i,j]).p), int(sp.Rational(G[i,j]).q)) for j in range(n)] for i in range(n)]
    used=[False]*n
    for _ in range(n):
        cand=[k for k in range(n) if not used[k]]
        # pick largest diagonal
        k=max(cand,key=lambda k:R[k][k])
        if R[k][k] < 0:
            return False
        if R[k][k] == 0:
            # remaining diagonal must be 0 and rows zero for PSD
            for i in cand:
                if R[i][i] != 0: return False
            return True
        used[k]=True; piv=R[k][k]
        for i in range(n):
            if used[i]: continue
            for j in range(n):
                if used[j]: continue
                R[i][j]=R[i][j]-R[k][i]*R[k][j]/piv
    return True

def round_psd(Gfloat, b, D):
    n = len(b)
    G = sp.Matrix(n, n, lambda i, j: sp.Rational(round((Gfloat[i,j]+Gfloat[j,i])/2*D), D))
    return G if is_psd_rational(G, n) else None

# weights[1:] are rounded; weights[0] (sigma0) exact-matched to residual
best = None
for D in [256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536]:
    rounded = []
    okround = True
    for idx in (1, 2, 3):
        Gi = round_psd(Gf[idx], weights[idx][1], D)
        if Gi is None:
            okround = False; break
        rounded.append((Gi, weights[idx][0], weights[idx][1]))
    if not okround:
        continue
    Pres = sp.expand(P - sum(w*form(Gi, b) for Gi, w, b in rounded))
    G0 = exact_match_gram(Pres, b0, Gf[0], D)
    if sp.expand(form(G0, b0) - Pres) != 0:
        best = ("nomatch", D); continue
    if not is_psd_rational(G0, len(b0)):
        best = ("notPSD", D); continue
    print(f"SUCCESS at D={D}: exact identity holds, all four Grams PSD (rational).")
    pickle.dump({"G0":sp.srepr(G0),
                 "G1":sp.srepr(rounded[0][0]),"G2":sp.srepr(rounded[1][0]),"G3":sp.srepr(rounded[2][0]),
                 "b0":b0,"b1":b1,"b3":b3,"rho":str(RHO)}, open("lin11.pkl","wb"))
    print("saved lin11.pkl")
    best = ("ok", D); break
if best is None or best[0] != "ok":
    print("did not succeed:", best)
