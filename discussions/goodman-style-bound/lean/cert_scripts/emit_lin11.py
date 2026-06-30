# -*- coding: utf-8 -*-
"""Emit the Lean lemma cert11_L from lin11.pkl (the 4 PSD Grams)."""
import sympy as sp, pickle
from fractions import Fraction
import numpy as np

q, lam = sp.symbols("q lam")
MU="μ"
d = pickle.load(open("lin11.pkl","rb"))
G = {k: sp.sympify(d[k]) for k in ("G0","G1","G2","G3")}
b0=[tuple(t) for t in d["b0"]]; b1=[tuple(t) for t in d["b1"]]; b3=[tuple(t) for t in d["b3"]]
RHO=sp.Rational(97,200)
a=[90*q**8-396*q**7+924*q**6-1386*q**5+1386*q**4-924*q**3+396*q**2-99*q+11,
 80*q**7-308*q**6+616*q**5-770*q**4+616*q**3-308*q**2+88*q-11,
 70*q**6-231*q**5+385*q**4-385*q**3+231*q**2-77*q+11,
 60*q**5-165*q**4+220*q**3-165*q**2+66*q-11,
 50*q**4-110*q**3+110*q**2-55*q+11,40*q**3-66*q**2+44*q-11,30*q**2-33*q+11,20*q-11,sp.Integer(10)]

def qpoly_lean(expr):
    expr=sp.expand(expr)
    if expr==0: return "0"
    P=sp.Poly(expr,q)
    terms=[]
    for (e,),c in sorted(P.terms(),key=lambda kv:-kv[0][0]):
        c=sp.Rational(c)
        cs=f"({c.p}/{c.q})" if c.q!=1 else f"{c.p}"
        if e==0: terms.append(cs)
        elif e==1: terms.append(f"{cs} * {MU0}" if False else f"{cs} * q")
        else: terms.append(f"{cs} * q ^ {e}")
    out=terms[0]
    for t in terms[1:]:
        out+= " + "+t
    return out

# We'll write q as the bound variable 'q' in the lemma.
def to_frac(x):
    r=sp.Rational(x); return Fraction(int(r.p),int(r.q))
def ldl_squares(M,b):
    n=len(b); Mn=np.array(M.tolist(),dtype=float)
    idx=[i for i in range(n) if np.abs(Mn[i]).max()>1e-12]; bb=[b[i] for i in idx]; m=len(idx)
    R=[[to_frac(M[idx[i],idx[j]]) for j in range(m)] for i in range(m)]
    sq=[]; used=[False]*m
    for _ in range(m):
        cand=[k for k in range(m) if not used[k] and R[k][k]!=0]
        if not cand: break
        k=max(cand,key=lambda k:abs(R[k][k])); used[k]=True; piv=R[k][k]
        col=[Fraction(0)]*m; col[k]=Fraction(1)
        for j in range(m):
            if not used[j]: col[j]=R[k][j]/piv
        maxp=max(bj[1] for bj in b); v=[sp.Integer(0)]*(maxp+1)
        for j in range(m):
            if col[j]!=0: v[bb[j][1]]+=sp.Rational(col[j].numerator,col[j].denominator)*q**bb[j][0]
        sq.append((sp.Rational(piv.numerator,piv.denominator),[sp.expand(x) for x in v]))
        for i in range(m):
            if used[i]:continue
            rki=R[k][i]
            if rki==0:continue
            for j in range(m):
                if used[j]:continue
                R[i][j]=R[i][j]-rki*R[k][j]/piv
    return sq

weights=[("w0",sp.Integer(1),G["G0"],b0),("w1",q,G["G1"],b1),
         ("w2",RHO-q,G["G2"],b1),("w3",q*(RHO-q),G["G3"],b3)]

s=sp.symbols("s0:20")
def sm(i): return f"specMoment U {MU} {i}"

def momform_lean(coeffs):
    # coeffs: dict d-> qpoly ; produce sum coeff_d * specMoment d
    parts=[]
    for dd in sorted(coeffs):
        c=sp.expand(coeffs[dd])
        if c==0: continue
        parts.append(f"({qpoly_lean(c)}) * {sm(dd)}")
    return " + ".join(parts) if parts else "0"

def sos4form_lean(v):
    # v[0..4] coeff of lam^0..4 ; c4=v[4]..c0=v[0]
    v=[sp.expand(x) for x in v]+[sp.Integer(0)]*(5-len(v))
    c0,c1,c2,c3,c4=v[0],v[1],v[2],v[3],v[4]
    def P(e): return f"({qpoly_lean(e)})"
    return (f"{P(c4)}^2 * {sm(8)} + 2*{P(c4)}*{P(c3)} * {sm(7)} "
        f"+ (2*{P(c4)}*{P(c2)} + {P(c3)}^2) * {sm(6)} + (2*{P(c4)}*{P(c1)} + 2*{P(c3)}*{P(c2)}) * {sm(5)} "
        f"+ (2*{P(c4)}*{P(c0)} + 2*{P(c3)}*{P(c1)} + {P(c2)}^2) * {sm(4)} "
        f"+ (2*{P(c3)}*{P(c0)} + 2*{P(c2)}*{P(c1)}) * {sm(3)} + (2*{P(c2)}*{P(c0)} + {P(c1)}^2) * {sm(2)} "
        f"+ 2*{P(c1)}*{P(c0)} * {sm(1)} + {P(c0)}^2 * {sm(0)}")

# gram moment form per weight = int sigma_g dmu = sum_{j,l} G[j,l] q^{aj+al} s_{cj+cl}
def gram_moment(M,b):
    cf={}
    for j in range(len(b)):
        for l in range(len(b)):
            if M[j,l]!=0:
                dd=b[j][1]+b[l][1]
                cf[dd]=cf.get(dd,0)+M[j,l]*q**(b[j][0]+b[l][0])
    return {k:sp.expand(v) for k,v in cf.items()}

lines=[]
gmforms=[]
for gi,(wn,w,M,b) in enumerate(weights):
    sqs=ldl_squares(M,b)
    gm=gram_moment(M,b)
    gmform=momform_lean(gm)
    gmforms.append(gmform)
    rhsterms=[]
    haves=[]
    for ki,(piv,v) in enumerate(sqs):
        vv=[sp.expand(x) for x in v]+[sp.Integer(0)]*(5-len(v))
        Dp=sp.Integer(1)
        for x in vv:
            for c in (sp.Poly(x,q).all_coeffs() if x!=0 else []):
                Dp=sp.lcm(Dp, sp.Rational(c).q)
        ww=[sp.expand(x*Dp) for x in vv]
        pivp=sp.Rational(piv)/Dp**2
        c0,c1,c2,c3,c4=[f"({qpoly_lean(x)})" for x in ww]
        hn=f"h{ki}"
        haves.append(f"  have {hn} := sos4 hU {c4} {c3} {c2} {c1} {c0}")
        ps=f"({pivp.p}/{pivp.q})" if pivp.q!=1 else f"{pivp.p}"
        rhsterms.append((ps,sos4form_lean(ww),hn))
    # integer clearing: Lambda = lcm of pivot denominators and gmform coeff denominators
    Lam=sp.Integer(1)
    for ps,form,hn in rhsterms:
        Lam=sp.lcm(Lam, sp.Rational(ps.strip("()")).q)
    for dd,cc in gm.items():
        for c in (sp.Poly(sp.expand(cc),q).all_coeffs() if cc!=0 else []):
            Lam=sp.lcm(Lam, sp.Rational(c).q)
    Lam=sp.Integer(Lam)
    # integer pivots and integer gmform
    intterms=[]
    for ps,form,hn in rhsterms:
        ip=sp.Integer(Lam*sp.Rational(ps.strip("()")))
        intterms.append((str(ip),form,hn))
    lines.append("set_option maxHeartbeats 1600000 in")
    lines.append(f"lemma cert11_L{gi} (hU : IsGraphon U μ) (q : ℝ) :")
    lines.append(f"    (0:ℝ) ≤ {gmform} := by")
    lines+=haves
    rhs=" + ".join(f"({ip}) * ({form})" for ip,form,_ in intterms)
    lines.append(f"  have key : ({Lam}:ℝ) * ({gmform}) = {rhs} := by ring")
    tnames=[]
    for ti,(ip,form,hn) in enumerate(intterms):
        tn=f"t{ti}"
        lines.append(f"  have {tn} : (0:ℝ) ≤ ({ip}) * ({form}) := mul_nonneg (by norm_num) {hn}")
        tnames.append(tn)
    lines.append(f"  have hL : (0:ℝ) ≤ ({Lam}:ℝ) * ({gmform}) := by rw [key]; linarith [{', '.join(tnames)}]")
    lines.append(f"  exact (mul_nonneg_iff_of_pos_left (by norm_num : (0:ℝ) < {Lam})).mp hL")
    lines.append("")

L1form=momform_lean({dd:a[dd] for dd in range(9)})
gm0,gm1,gm2,gm3=gmforms
lines.append("/-- **`C₁₁` linear part `L₁ ≥ 0`** on the path-certificate range `0 ≤ q ≤ 97/200`,")
lines.append("via the joint `(q,λ)` Positivstellensatz `P_q = σ₀ + q σ₁ + (ρ−q) σ₂ + q(ρ−q) σ₃`. -/")
lines.append("lemma cert11_L (hU : IsGraphon U μ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 97/200) :")
lines.append(f"    0 ≤ {L1form} := by")
lines.append("  have hy : (0:ℝ) ≤ 97/200 - q := by linarith")
lines.append(f"  have hpos0 := cert11_L0 hU q")
lines.append(f"  have e1 : (0:ℝ) ≤ q * ({gm1}) := mul_nonneg hq0 (cert11_L1 hU q)")
lines.append(f"  have e2 : (0:ℝ) ≤ (97/200 - q) * ({gm2}) := mul_nonneg hy (cert11_L2 hU q)")
lines.append(f"  have e3 : (0:ℝ) ≤ q * (97/200 - q) * ({gm3}) := mul_nonneg (mul_nonneg hq0 hy) (cert11_L3 hU q)")
lines.append(f"  have key : {L1form} = ({gm0}) + q * ({gm1}) + (97/200 - q) * ({gm2}) + q * (97/200 - q) * ({gm3}) := by ring")
lines.append("  rw [key]; linarith [hpos0, e1, e2, e3]")

open("cert11_L.lean.txt","w",encoding="utf-8").write("\n".join(lines))
print("wrote cert11_L.lean.txt ; lines:", len(lines))
