# -*- coding: utf-8 -*-
"""Load lin11.pkl; (1) verify moment identity directly from Grams (fast),
(2) pruned+pivoted exact LDL (fractions.Fraction) to get SOS squares, (3) re-verify."""
import sympy as sp, pickle, numpy as np
from fractions import Fraction

q, lam = sp.symbols("q lam")
d = pickle.load(open("lin11.pkl","rb"))
G = {k: sp.sympify(d[k]) for k in ("G0","G1","G2","G3")}
b0 = [tuple(t) for t in d["b0"]]; b1=[tuple(t) for t in d["b1"]]; b3=[tuple(t) for t in d["b3"]]
RHO = sp.Rational(97,200)
a = [
 90*q**8 - 396*q**7 + 924*q**6 - 1386*q**5 + 1386*q**4 - 924*q**3 + 396*q**2 - 99*q + 11,
 80*q**7 - 308*q**6 + 616*q**5 - 770*q**4 + 616*q**3 - 308*q**2 + 88*q - 11,
 70*q**6 - 231*q**5 + 385*q**4 - 385*q**3 + 231*q**2 - 77*q + 11,
 60*q**5 - 165*q**4 + 220*q**3 - 165*q**2 + 66*q - 11,
 50*q**4 - 110*q**3 + 110*q**2 - 55*q + 11, 40*q**3-66*q**2+44*q-11, 30*q**2-33*q+11, 20*q-11, sp.Integer(10)]
s = sp.symbols("s0:20")
L1 = sum(a[dd]*s[dd] for dd in range(9))
weights = [(sp.Integer(1), G["G0"], b0), (q, G["G1"], b1), (RHO-q, G["G2"], b1), (q*(RHO-q), G["G3"], b3)]

# (1) direct moment identity: int(b^T G b)dmu = sum_{j,l} G[j,l] q^{aj+al} s_{cj+cl}
def gram_moment(M, b):
    n=len(b); out=0
    for j in range(n):
        for l in range(n):
            if M[j,l]!=0:
                out += M[j,l]*q**(b[j][0]+b[l][0])*s[b[j][1]+b[l][1]]
    return out
rhs = sum(w*gram_moment(M,b) for w,M,b in weights)
print("direct moment identity exact:", sp.expand(L1-rhs)==0)

# (2) pruned pivoted exact LDL per Gram, using fractions.Fraction (fast)
def to_frac(x):
    r = sp.Rational(x)
    return Fraction(int(r.p), int(r.q))

def ldl_squares(M, b):
    n=len(b)
    Mn=np.array(M.tolist(),dtype=float)
    idx=[i for i in range(n) if np.abs(Mn[i]).max()>1e-12]
    bb=[b[i] for i in idx]
    m=len(idx)
    R=[[to_frac(M[idx[i],idx[j]]) for j in range(m)] for i in range(m)]
    squares=[]
    used=[False]*m
    for _ in range(m):
        cand=[k for k in range(m) if not used[k] and R[k][k]!=0]
        if not cand: break
        k=max(cand,key=lambda k: abs(R[k][k]))
        used[k]=True
        piv=R[k][k]
        col=[Fraction(0)]*m
        col[k]=Fraction(1)
        for j in range(m):
            if not used[j]:
                col[j]=R[k][j]/piv
        maxp=max(bj[1] for bj in b)
        v=[sp.Integer(0)]*(maxp+1)
        for j in range(m):
            cj=col[j]
            if cj!=0:
                v[bb[j][1]] += sp.Rational(cj.numerator,cj.denominator)*q**bb[j][0]
        squares.append((sp.Rational(piv.numerator,piv.denominator),[sp.expand(vp) for vp in v]))
        for i in range(m):
            if used[i]: continue
            rki=R[k][i]
            if rki==0: continue
            for j in range(m):
                if used[j]: continue
                R[i][j]=R[i][j]-rki*R[k][j]/piv
    return squares

terms=[]
for w,M,b in weights:
    for piv,v in ldl_squares(M,b):
        terms.append((w,piv,v))
print("num SOS terms:",len(terms))
rhs2=0
for w,piv,v in terms:
    nv=len(v)
    rhs2+=w*piv*sum(v[p]*v[pp]*s[p+pp] for p in range(nv) for pp in range(nv))
print("LDL moment identity exact:", sp.expand(L1-rhs2)==0)
print("all pivots>=0:", all(p>=0 for _,p,_ in terms))
pickle.dump({"terms":[(sp.srepr(w),sp.srepr(p),[sp.srepr(vp) for vp in v]) for w,p,v in terms],"rho":str(RHO)},
            open("lin11_terms.pkl","wb"))
print("saved",len(terms),"terms")
