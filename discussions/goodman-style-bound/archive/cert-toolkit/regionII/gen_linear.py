# -*- coding: utf-8 -*-
"""Reusable LINEAR-piece certificate generator (joint (q,lam) Positivstellensatz).
Given P_q(lam)=sum a_d(q) lam^d  (>0 on [0,rho]xR), produce + emit a Lean lemma
  0 <= sum a_d(q) s_d
on 0<=q<=rho, via P_q = sigma0 + q sigma1 + (rho-q) sigma2 + q(rho-q) sigma3
with PSD Grams, integer-cleared.  Designed for the large-margin regime (rho=1/3).
"""
import sympy as sp, numpy as np, cvxpy as cp, sys
from fractions import Fraction as Fr
q, lam = sp.symbols("q lam"); MU="μ"

def monos(iq, jl): return [(i, j) for i in range(iq+1) for j in range(jl+1)]
def monos_td(td, jl): return [(i, j) for i in range(td+1) for j in range(jl+1) if i+j<=td]

def is_psd(G, n):
    R=[[Fr(int(sp.Rational(G[i,j]).p),int(sp.Rational(G[i,j]).q)) for j in range(n)] for i in range(n)]
    used=[False]*n
    for _ in range(n):
        cand=[k for k in range(n) if not used[k]]; k=max(cand,key=lambda k:R[k][k])
        if R[k][k]<0: return False
        if R[k][k]==0: return all(R[i][i]==0 for i in cand)
        used[k]=True; piv=R[k][k]
        for i in range(n):
            if used[i]:continue
            for j in range(n):
                if used[j]:continue
                R[i][j]=R[i][j]-R[k][i]*R[k][j]/piv
    return True

def ldl_squares(M, b, maxp):
    n=len(b); Mn=np.array(M.tolist(),dtype=float)
    idx=[i for i in range(n) if np.abs(Mn[i]).max()>1e-12]; bb=[b[i] for i in idx]; m=len(idx)
    R=[[Fr(int(sp.Rational(M[idx[i],idx[j]]).p),int(sp.Rational(M[idx[i],idx[j]]).q)) for j in range(m)] for i in range(m)]
    sq=[]; used=[False]*m
    for _ in range(m):
        cand=[k for k in range(m) if not used[k] and R[k][k]!=0]
        if not cand: break
        k=max(cand,key=lambda k:abs(R[k][k])); used[k]=True; piv=R[k][k]
        col=[Fr(0)]*m; col[k]=Fr(1)
        for j in range(m):
            if not used[j]: col[j]=R[k][j]/piv
        v=[sp.Integer(0)]*(maxp+1)
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

def gen(a, RHO, name, jl=4, out=None, CHUNK=5):
    P=sp.expand(sum(a[d]*lam**d for d in range(len(a))))
    deg=len(a)-1; hd=deg//2
    b0=monos_td(hd, jl); b1=monos_td(max(hd-1,0), jl)
    weights=[(sp.Integer(1),b0),(q,b1),(RHO-q,b1),(q*(RHO-q),b1)]
    Qs=[cp.Variable((len(b),len(b)),symmetric=True) for _,b in weights]
    t=cp.Variable(); cons=[Q-t*np.eye(len(b))>>0 for Q,(_,b) in zip(Qs,weights)]
    coeff={}
    for (w,b),Q in zip(weights,Qs):
        for (eq,el),wc in sp.Poly(w,q,lam).terms():
            for ai,(ia,ja) in enumerate(b):
                for ci,(ic,jc) in enumerate(b):
                    e=(ia+ic+eq,ja+jc+el); coeff[e]=coeff.get(e,0)+float(wc)*Q[ai,ci]
    tgt={e:float(c) for e,c in sp.Poly(P,q,lam).terms()}
    for e in set(coeff)|set(tgt): cons.append(coeff.get(e,0)==tgt.get(e,0.0))
    cp.Problem(cp.Maximize(t),cons).solve(solver=cp.CLARABEL)
    print(f"[{name}] margin t={t.value:.4f}")
    Gf=[np.array(Q.value) for Q in Qs]
    def form(G,b):
        n=len(b); return sp.expand(sum(G[i,j]*(q**b[i][0]*lam**b[i][1])*(q**b[j][0]*lam**b[j][1]) for i in range(n) for j in range(n)))
    def exact_match(Pres,b,Gf,D):
        n=len(b); G=[[sp.Rational(round((Gf[i,j]+Gf[j,i])/2*D),D) for j in range(n)] for i in range(n)]
        classes={}
        for i in range(n):
            for j in range(n):
                e=(b[i][0]+b[j][0],b[i][1]+b[j][1]); classes.setdefault(e,[]).append((i,j))
        cur={}
        for i in range(n):
            for j in range(n):
                e=(b[i][0]+b[j][0],b[i][1]+b[j][1]); cur[e]=cur.get(e,0)+G[i][j]
        Pc={e:sp.nsimplify(c) for e,c in sp.Poly(Pres,q,lam).terms()}
        for e in set(cur)|set(Pc):
            defi=Pc.get(e,0)-cur.get(e,0)
            if defi==0: continue
            pairs=classes.get(e,[])
            if not pairs: return None
            diag=[(i,j) for (i,j) in pairs if i==j]
            if diag: i,j=diag[0]; G[i][j]+=defi
            else: i,j=pairs[0]; G[i][j]+=defi/2; G[j][i]+=defi/2
        return sp.Matrix(G)
    Gres=None
    for D in [8,16,32,64,128,256,512,1024]:
        R=[]; ok=True
        for idx in (1,2,3):
            n=len(b1); Gi=sp.Matrix(n,n,lambda i,j: sp.Rational(round((Gf[idx][i,j]+Gf[idx][j,i])/2*D),D))
            if not is_psd(Gi,n): ok=False;break
            R.append(Gi)
        if not ok: continue
        Pres=sp.expand(P - q*form(R[0],b1) - (RHO-q)*form(R[1],b1) - q*(RHO-q)*form(R[2],b1))
        G0=exact_match(Pres,b0,Gf[0],D)
        if G0 is None or sp.expand(form(G0,b0)-Pres)!=0 or not is_psd(G0,len(b0)): continue
        Gres=(D,[G0,R[0],R[1],R[2]]); break
    if Gres is None:
        print(f"[{name}] FAILED to rationalize"); return None
    D,Gs=Gres; print(f"[{name}] rationalized at D={D}")
    # emit lean
    s=sp.symbols("s0:30")
    def sm(i): return f"specMoment U {MU} {i}"
    def qpoly(expr):
        expr=sp.expand(expr)
        if expr==0: return "0"
        terms=[]
        for (e,),c in sorted(sp.Poly(expr,q).terms(),key=lambda kv:-kv[0][0]):
            c=sp.Rational(c); cs=f"({c.p}/{c.q})" if c.q!=1 else f"{c.p}"
            terms.append(cs if e==0 else (f"{cs} * q" if e==1 else f"{cs} * q ^ {e}"))
        return " + ".join(terms)
    def momform(cf):
        return " + ".join(f"({qpoly(cf[d])}) * {sm(d)}" for d in sorted(cf) if sp.expand(cf[d])!=0) or ["0"]
    def sosform(v):
        # match sos{jl} statement exactly: descending d, products higher-index first
        v=[sp.expand(x) for x in v]+[sp.Integer(0)]*(jl+1-len(v))
        P_=lambda e:f"({qpoly(e)})"
        outp=[]
        for d in range(2*jl, -1, -1):
            pterms=[]
            hi=min(jl, d)
            while hi >= (d+1)//2:
                lo=d-hi
                if lo<0 or lo>jl: hi-=1; continue
                pterms.append(f"{P_(v[hi])}^2" if hi==lo else f"2*{P_(v[hi])}*{P_(v[lo])}")
                hi-=1
            outp.append(f"({' + '.join(pterms)}) * {sm(d)}")
        return " + ".join(outp)
    def gram_moment(M,b):
        cf={}
        for j in range(len(b)):
            for l in range(len(b)):
                if M[j,l]!=0:
                    dd=b[j][1]+b[l][1]; cf[dd]=cf.get(dd,0)+M[j,l]*q**(b[j][0]+b[l][0])
        return {k:sp.expand(v) for k,v in cf.items()}
    def sqmoment(w):
        acc={}
        for p in range(jl+1):
            for pp in range(jl+1):
                d=p+pp; acc[d]=acc.get(d,sp.Integer(0))+w[p]*w[pp]
        return {k:sp.expand(v) for k,v in acc.items() if sp.expand(v)!=0}
    bb=[b0,b1,b1,b1]; L=[]; gmforms=[]
    for gi,(G,b) in enumerate(zip(Gs,bb)):
        gm=gram_moment(G,b); gmform=momform(gm); gmforms.append(gmform)
        sqs=ldl_squares(G,b,jl)
        sqdata=[]
        for piv,v in sqs:
            vv=[sp.expand(x) for x in v]+[sp.Integer(0)]*(jl+1-len(v))
            Dp=sp.Integer(1)
            for x in vv:
                for c in (sp.Poly(x,q).all_coeffs() if x!=0 else []): Dp=sp.lcm(Dp,sp.Rational(c).q)
            w=[sp.expand(x*Dp) for x in vv]; pivp=sp.Rational(piv)/Dp**2
            sqdata.append((pivp,w))
        chunks=[sqdata[i:i+CHUNK] for i in range(0,len(sqdata),CHUNK)]
        chunknames=[]
        for ci,chunk in enumerate(chunks):
            cmf={}; Lam=sp.Integer(1)
            for pivp,w in chunk:
                Lam=sp.lcm(Lam,pivp.q)
                for d,v in sqmoment(w).items(): cmf[d]=cmf.get(d,sp.Integer(0))+pivp*v
            cmf={k:sp.expand(v) for k,v in cmf.items()}
            for v in cmf.values():
                for c in (sp.Poly(v,q).all_coeffs() if v!=0 else []): Lam=sp.lcm(Lam,sp.Rational(c).q)
            Lam=sp.Integer(Lam); cmform=momform(cmf)
            cn=f"{name}_b{gi}c{ci}"; chunknames.append((cn,cmform))
            L.append("set_option maxHeartbeats 2000000 in")
            L.append("set_option maxRecDepth 4000 in")
            L.append(f"lemma {cn} (hU : IsGraphon U μ) (q : ℝ) :")
            L.append(f"    (0:ℝ) ≤ {cmform} := by")
            rhst=[]
            for ki,(pivp,w) in enumerate(chunk):
                c=[f"({qpoly(x)})" for x in w]
                L.append(f"  have h{ki} := sos{jl} hU {c[jl]} " + " ".join(c[jl-1::-1]))
                ip=sp.Integer(Lam*pivp); rhst.append((str(ip),sosform(w),f"h{ki}"))
            rhs=" + ".join(f"({ip}) * ({fm})" for ip,fm,_ in rhst)
            L.append(f"  have key : ({Lam}:ℝ) * ({cmform}) = {rhs} := by ring")
            tn=[]
            for ti,(ip,fm,hn) in enumerate(rhst):
                L.append(f"  have t{ti} : (0:ℝ) ≤ ({ip}) * ({fm}) := mul_nonneg (by norm_num) {hn}")
                tn.append(f"t{ti}")
            L.append(f"  have hL : (0:ℝ) ≤ ({Lam}:ℝ) * ({cmform}) := by rw [key]; linarith [{', '.join(tn)}]")
            L.append(f"  exact (mul_nonneg_iff_of_pos_left (by norm_num : (0:ℝ) < {Lam})).mp hL")
            L.append("")
        L.append("set_option maxHeartbeats 2000000 in")
        L.append("set_option maxRecDepth 4000 in")
        L.append(f"lemma {name}{gi} (hU : IsGraphon U μ) (q : ℝ) :")
        L.append(f"    (0:ℝ) ≤ {gmform} := by")
        csum=" + ".join(f"({cmf})" for _,cmf in chunknames)
        L.append(f"  have key : {gmform} = {csum} := by ring")
        hh=", ".join(f"{cn} hU q" for cn,_ in chunknames)
        L.append(f"  rw [key]; linarith [{hh}]")
        L.append("")
    L1form=momform({d:a[d] for d in range(len(a))})
    rhoq=f"({RHO.p}/{RHO.q} - q)"
    L.append("set_option maxHeartbeats 2000000 in")
    L.append("set_option maxRecDepth 4000 in")
    L.append(f"lemma {name} (hU : IsGraphon U μ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ {RHO.p}/{RHO.q}) :")
    L.append(f"    0 ≤ {L1form} := by")
    L.append(f"  have hy : (0:ℝ) ≤ {RHO.p}/{RHO.q} - q := by linarith")
    L.append(f"  have e1 := mul_nonneg hq0 ({name}1 hU q)")
    L.append(f"  have e2 := mul_nonneg hy ({name}2 hU q)")
    L.append(f"  have e3 := mul_nonneg (mul_nonneg hq0 hy) ({name}3 hU q)")
    L.append(f"  have key : {L1form} = ({gmforms[0]}) + q * ({gmforms[1]}) + {rhoq} * ({gmforms[2]}) + q * {rhoq} * ({gmforms[3]}) := by ring")
    L.append(f"  rw [key]; linarith [{name}0 hU q, e1, e2, e3]")
    txt="\n".join(L)
    if out: open(out,"w",encoding="utf-8").write(txt)
    print(f"[{name}] emitted -> {out} ({len(L)} lines, terms={sum(len(ldl_squares(G,b,jl)) for G,b in zip(Gs,bb))})")
    return txt

if __name__=="__main__":
    a=[90*q**8-396*q**7+924*q**6-1386*q**5+1386*q**4-924*q**3+396*q**2-99*q+11,
       80*q**7-308*q**6+616*q**5-770*q**4+616*q**3-308*q**2+88*q-11,
       70*q**6-231*q**5+385*q**4-385*q**3+231*q**2-77*q+11,
       60*q**5-165*q**4+220*q**3-165*q**2+66*q-11,
       50*q**4-110*q**3+110*q**2-55*q+11,40*q**3-66*q**2+44*q-11,30*q**2-33*q+11,20*q-11,sp.Integer(10)]
    gen(a, sp.Rational(1,3), "cert11_L", jl=4, out="cert11_L.txt")
