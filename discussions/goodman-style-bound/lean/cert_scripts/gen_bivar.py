# -*- coding: utf-8 -*-
"""Bivariate moment-piece certificate generator (joint (q,lam,mu) Positivstellensatz).
Given L2 = sum c_ij(q) s_i s_j (>=0 moment form), build K2(q,lam,mu) symmetric with
L2 = int int K2 dmu dmu, certify K2 = sig0 + q sig1 + (rho-q) sig2 + q(rho-q) sig3 (PSD),
emit a Lean lemma using sos2var4."""
import sympy as sp, numpy as np, cvxpy as cp
from fractions import Fraction as Fr
q, l, m = sp.symbols("q l m"); MU="μ"

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

def ldl_squares(M, b, Nb=4):
    n=len(b); Mn=np.array(M.tolist(),dtype=float)
    idx=[i for i in range(n) if np.abs(Mn[i]).max()>1e-12]; bb=[b[i] for i in idx]; mm=len(idx)
    R=[[Fr(int(sp.Rational(M[idx[i],idx[j]]).p),int(sp.Rational(M[idx[i],idx[j]]).q)) for j in range(mm)] for i in range(mm)]
    sq=[]; used=[False]*mm
    for _ in range(mm):
        cand=[k for k in range(mm) if not used[k] and R[k][k]!=0]
        if not cand: break
        k=max(cand,key=lambda k:abs(R[k][k])); used[k]=True; piv=R[k][k]
        col=[Fr(0)]*mm; col[k]=Fr(1)
        for j in range(mm):
            if not used[j]: col[j]=R[k][j]/piv
        # coefficient matrix C[i][j] (lam^i mu^j) as q-poly, i,j in 0..3
        C=[[sp.Integer(0)]*Nb for _ in range(Nb)]
        for j in range(mm):
            if col[j]!=0:
                a,i,jj=bb[j]  # (q-exp, lam-exp, mu-exp)
                C[i][jj]+=sp.Rational(col[j].numerator,col[j].denominator)*q**a
        sq.append((sp.Rational(piv.numerator,piv.denominator),[[sp.expand(C[i][j]) for j in range(Nb)] for i in range(Nb)]))
        for i in range(mm):
            if used[i]:continue
            rki=R[k][i]
            if rki==0:continue
            for j in range(mm):
                if used[j]:continue
                R[i][j]=R[i][j]-rki*R[k][j]/piv
    return sq

def gen(L2, RHO, name, out, Nb=4):
    s=sp.symbols("s0:20")
    # build K2(q,lam,mu): replace s_i s_j -> symmetric monomial
    K=sp.Integer(0)
    P2=sp.Poly(L2, *s[:9])
    for monom,coeff in P2.terms():
        idxs=[i for i,e in enumerate(monom) for _ in range(e)]
        assert len(idxs)==2, idxs
        i,j=idxs
        if i==j: K+=coeff*l**i*m**j
        else: K+=coeff*(l**i*m**j + l**j*m**i)/2
    K=sp.expand(K)
    # total-degree (q,lam,mu) basis: a+i+j <= td, with i,j<=3 (sos2var4 caps lam,mu deg)
    def basis(td): return [(a,i,j) for a in range(td+1) for i in range(Nb) for j in range(Nb) if i+j<=Nb-1 and a+i+j<=td]
    b0=basis(Nb-1); b1=basis(Nb-2)
    weights=[(sp.Integer(1),b0),(q,b1),(RHO-q,b1),(q*(RHO-q),b1)]
    print(f"[{name}] basis sizes={[len(b) for _,b in weights]}")
    Qs=[cp.Variable((len(b),len(b)),symmetric=True) for _,b in weights]
    t=cp.Variable(); cons=[Q-t*np.eye(len(b))>>0 for Q,(_,b) in zip(Qs,weights)]
    coeff={}
    for (w,b),Q in zip(weights,Qs):
        for (eq,el,em),wc in sp.Poly(w,q,l,m).terms():
            for ai,(qa,la,ma) in enumerate(b):
                for ci,(qc,lc,mc) in enumerate(b):
                    e=(qa+qc+eq,la+lc+el,ma+mc+em); coeff[e]=coeff.get(e,0)+float(wc)*Q[ai,ci]
    tgt={e:float(c) for e,c in sp.Poly(K,q,l,m).terms()}
    for e in set(coeff)|set(tgt): cons.append(coeff.get(e,0)==tgt.get(e,0.0))
    cp.Problem(cp.Maximize(t),cons).solve(solver=cp.CLARABEL)
    print(f"[{name}] margin t={t.value}")
    if t.value is None or t.value<1e-7: print("  marginal"); return None
    Gf=[np.array(Q.value) for Q in Qs]
    def form(G,b):
        n=len(b); return sp.expand(sum(G[i,j]*(q**b[i][0]*l**b[i][1]*m**b[i][2])*(q**b[j][0]*l**b[j][1]*m**b[j][2]) for i in range(n) for j in range(n)))
    def exact_match(Pres,b,Gf,D):
        n=len(b); G=[[sp.Rational(round((Gf[i,j]+Gf[j,i])/2*D),D) for j in range(n)] for i in range(n)]
        cls={}
        for i in range(n):
            for j in range(n):
                e=(b[i][0]+b[j][0],b[i][1]+b[j][1],b[i][2]+b[j][2]); cls.setdefault(e,[]).append((i,j))
        cur={}
        for i in range(n):
            for j in range(n):
                e=(b[i][0]+b[j][0],b[i][1]+b[j][1],b[i][2]+b[j][2]); cur[e]=cur.get(e,0)+G[i][j]
        Pc={e:sp.nsimplify(c) for e,c in sp.Poly(Pres,q,l,m).terms()}
        for e in set(cur)|set(Pc):
            defi=Pc.get(e,0)-cur.get(e,0)
            if defi==0: continue
            pairs=cls.get(e,[])
            if not pairs: return None
            diag=[(i,j) for (i,j) in pairs if i==j]
            if diag: i,j=diag[0]; G[i][j]+=defi
            else: i,j=pairs[0]; G[i][j]+=defi/2; G[j][i]+=defi/2
        return sp.Matrix(G)
    Gres=None
    for D in [8,16,32,64,128,256,512,1024,2048]:
        R=[]; ok=True
        for idx in (1,2,3):
            n=len(b1); Gi=sp.Matrix(n,n,lambda i,j: sp.Rational(round((Gf[idx][i,j]+Gf[idx][j,i])/2*D),D))
            if not is_psd(Gi,n): ok=False;break
            R.append(Gi)
        if not ok: continue
        Pres=sp.expand(K - q*form(R[0],b1) - (RHO-q)*form(R[1],b1) - q*(RHO-q)*form(R[2],b1))
        G0=exact_match(Pres,b0,Gf[0],D)
        if G0 is None or sp.expand(form(G0,b0)-Pres)!=0 or not is_psd(G0,len(b0)): continue
        Gres=(D,[G0,R[0],R[1],R[2]]); break
    if Gres is None: print(f"[{name}] FAILED rationalize"); return None
    D,Gs=Gres; print(f"[{name}] rationalized D={D}")
    nterms=sum(len(ldl_squares(G,b,Nb)) for G,(_,b) in zip(Gs,weights))
    print(f"[{name}] total squares={nterms}")
    # emit
    def sm(i): return f"specMoment U {MU} {i}"
    def qpoly(expr):
        expr=sp.expand(expr)
        if expr==0: return "0"
        ts=[]
        for (e,),c in sorted(sp.Poly(expr,q).terms(),key=lambda kv:-kv[0][0]):
            c=sp.Rational(c); cs=f"({c.p}/{c.q})" if c.q!=1 else f"{c.p}"
            ts.append(cs if e==0 else (f"{cs} * q" if e==1 else f"{cs} * q ^ {e}"))
        return " + ".join(ts)
    # sos2var4 expanded form (must match engine statement EXACTLY up to ring; use nlinarith? no, we use it as a term)
    import gen_engine
    TEMPLATE=gen_engine.sos2var_template(Nb)
    def sos2var4form(C):
        # match sos2var4 statement exactly: substitute c{i}{j} -> (qpoly(C[i][j]))
        parts=[]
        for (a,b,cstr) in TEMPLATE:
            cs=cstr
            for i in range(Nb):
                for j in range(Nb):
                    cs=cs.replace(f"c{i}{j}", f"({qpoly(C[i][j])})")
            prod=f"{sm(a)} ^ 2" if a==b else f"{sm(a)} * {sm(b)}"
            parts.append(f"({cs}) * ({prod})")
        return " + ".join(parts)
    def gram_moment(M,b):
        cf={}
        for j in range(len(b)):
            for ll in range(len(b)):
                if M[j,ll]!=0:
                    a=(b[j][1]+b[ll][1]); bb_=(b[j][2]+b[ll][2]); key=(min(a,bb_),max(a,bb_))
                    cf[key]=cf.get(key,0)+M[j,ll]*q**(b[j][0]+b[ll][0])
        return {k:sp.expand(v) for k,v in cf.items()}
    def momform(cf):
        parts=[]
        for (a,b),c in sorted(cf.items()):
            c=sp.expand(c)
            if c==0: continue
            prod=f"{sm(a)} ^ 2" if a==b else f"{sm(a)} * {sm(b)}"
            parts.append(f"({qpoly(c)}) * ({prod})")
        return " + ".join(parts) if parts else "0"
    bb=[b0,b1,b1,b1]; Lout=[]; gmforms=[]
    CHUNK=(3 if Nb<=4 else 2)
    # moment value (form dict (a,b)->qpoly) of a single square with coeff matrix C
    def sqmoment(C):
        acc={}
        for i in range(Nb):
            for j in range(Nb):
                for k in range(Nb):
                    for ll in range(Nb):
                        a,b=i+k,j+ll; key=(min(a,b),max(a,b))
                        acc[key]=acc.get(key,sp.Integer(0))+C[i][j]*C[k][ll]
        return {k:sp.expand(v) for k,v in acc.items() if sp.expand(v)!=0}
    for gi,(G,b) in enumerate(zip(Gs,bb)):
        gm=gram_moment(G,b); gmform=momform(gm); gmforms.append(gmform)
        sqs=ldl_squares(G,b,Nb)
        # prepare integer-cleared squares
        sqdata=[]
        for piv,C in sqs:
            Dp=sp.Integer(1)
            for i in range(Nb):
                for j in range(Nb):
                    for c in (sp.Poly(C[i][j],q).all_coeffs() if C[i][j]!=0 else []): Dp=sp.lcm(Dp,sp.Rational(c).q)
            Cw=[[sp.expand(C[i][j]*Dp) for j in range(Nb)] for i in range(Nb)]
            pivp=sp.Rational(piv)/Dp**2
            sqdata.append((pivp,Cw))
        # chunk
        chunknames=[]
        chunks=[sqdata[i:i+CHUNK] for i in range(0,len(sqdata),CHUNK)]
        for ci,chunk in enumerate(chunks):
            # chunk moment form = sum pivp * sqmoment(Cw)
            cmf={}
            Lam=sp.Integer(1)
            for pivp,Cw in chunk:
                Lam=sp.lcm(Lam,pivp.q)
                for key,v in sqmoment(Cw).items():
                    cmf[key]=cmf.get(key,sp.Integer(0))+pivp*v
            cmf={k:sp.expand(v) for k,v in cmf.items()}
            for v in cmf.values():
                for c in (sp.Poly(v,q).all_coeffs() if v!=0 else []): Lam=sp.lcm(Lam,sp.Rational(c).q)
            Lam=sp.Integer(Lam)
            cmform=momform(cmf)
            cn=f"{name}{gi}c{ci}"; chunknames.append((cn,cmform))
            Lout.append("set_option maxHeartbeats 4000000 in")
            Lout.append("set_option maxRecDepth 4000 in")
            Lout.append(f"lemma {cn} (hU : IsGraphon U μ) (q : ℝ) :")
            Lout.append(f"    (0:ℝ) ≤ {cmform} := by")
            rhst=[]
            for ki,(pivp,Cw) in enumerate(chunk):
                args=" ".join(f"({qpoly(Cw[i][j])})" for i in range(Nb) for j in range(Nb))
                Lout.append(f"  have h{ki} := sos2var{Nb} hU {args}")
                ip=sp.Integer(Lam*pivp); rhst.append((str(ip),sos2var4form(Cw),f"h{ki}"))
            rhs=" + ".join(f"({ip}) * ({fm})" for ip,fm,_ in rhst)
            Lout.append(f"  have key : ({Lam}:ℝ) * ({cmform}) = {rhs} := by ring")
            tn=[]
            for ti,(ip,fm,hn) in enumerate(rhst):
                Lout.append(f"  have t{ti} : (0:ℝ) ≤ ({ip}) * ({fm}) := mul_nonneg (by norm_num) {hn}")
                tn.append(f"t{ti}")
            Lout.append(f"  have hL : (0:ℝ) ≤ ({Lam}:ℝ) * ({cmform}) := by rw [key]; linarith [{', '.join(tn)}]")
            Lout.append(f"  exact (mul_nonneg_iff_of_pos_left (by norm_num : (0:ℝ) < {Lam})).mp hL")
            Lout.append("")
        # combine chunks -> block
        Lout.append("set_option maxHeartbeats 2000000 in")
        Lout.append("set_option maxRecDepth 4000 in")
        Lout.append(f"lemma {name}{gi} (hU : IsGraphon U μ) (q : ℝ) :")
        Lout.append(f"    (0:ℝ) ≤ {gmform} := by")
        csum=" + ".join(f"({cmf})" for _,cmf in chunknames)
        Lout.append(f"  have key : {gmform} = {csum} := by ring")
        hh=", ".join(f"{cn} hU q" for cn,_ in chunknames)
        Lout.append(f"  rw [key]; linarith [{hh}]")
        Lout.append("")
    # combiner
    Lform=momform({(min(i,j),max(i,j)):0 for i in range(9) for j in range(9)})  # placeholder
    # actual L2 moment form
    def L2form():
        cf={}
        for monom,coeff in sp.Poly(L2,*s[:9]).terms():
            idxs=[i for i,e in enumerate(monom) for _ in range(e)]; i,j=idxs
            key=(min(i,j),max(i,j)); cf[key]=cf.get(key,0)+coeff
        return momform({k:sp.expand(v) for k,v in cf.items()})
    L2f=L2form()
    rhoq=f"({RHO.p}/{RHO.q} - q)"
    Lout.append("set_option maxHeartbeats 4000000 in")
    Lout.append("set_option maxRecDepth 4000 in")
    Lout.append(f"lemma {name} (hU : IsGraphon U μ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ {RHO.p}/{RHO.q}) :")
    Lout.append(f"    0 ≤ {L2f} := by")
    Lout.append(f"  have hy : (0:ℝ) ≤ {RHO.p}/{RHO.q} - q := by linarith")
    Lout.append(f"  have e1 := mul_nonneg hq0 ({name}1 hU q)")
    Lout.append(f"  have e2 := mul_nonneg hy ({name}2 hU q)")
    Lout.append(f"  have e3 := mul_nonneg (mul_nonneg hq0 hy) ({name}3 hU q)")
    Lout.append(f"  have key : {L2f} = ({gmforms[0]}) + q * ({gmforms[1]}) + {rhoq} * ({gmforms[2]}) + q * {rhoq} * ({gmforms[3]}) := by ring")
    Lout.append(f"  rw [key]; linarith [{name}0 hU q, e1, e2, e3]")
    open(out,"w",encoding="utf-8").write("\n".join(Lout))
    print(f"[{name}] emitted -> {out}")
    return True

if __name__=="__main__":
    import pickle
    Ld=pickle.load(open("phi11_L.pkl","rb"))
    L2=sp.sympify(Ld[2])
    import sys
    if len(sys.argv)>1 and sys.argv[1]=="c13":
        Ld13=pickle.load(open("phi13_L.pkl","rb")); gen(sp.sympify(Ld13[2]), sp.Rational(1,3), "cert13_L2", "cert13_L2.txt", Nb=5)
    else:
        gen(L2, sp.Rational(1,3), "cert11_L2", "cert11_L2.txt")
