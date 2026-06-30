# -*- coding: utf-8 -*-
"""Trivariate moment-piece certificate generator (joint (q,lam,mu,nu) Positivstellensatz).
For L3 = sum c_ijk(q) s_i s_j s_k, build K3 symmetric with L3 = int^3 K3, certify
K3 = sig0 + q sig1 + (rho-q) sig2 + q(rho-q) sig3 (PSD), emit Lean using sos3var3."""
import sympy as sp, numpy as np, cvxpy as cp, itertools
from fractions import Fraction as Fr
import gen_engine
q, l, m, n = sp.symbols("q l m n"); MU="μ"
NEWTON=[(0,0,0),(1,0,0),(0,1,0),(0,0,1),(2,0,0),(0,2,0),(0,0,2),(1,1,0),(1,0,1),(0,1,1)]
NIDX={mon:k for k,mon in enumerate(NEWTON)}

def is_psd(G, nn):
    R=[[Fr(int(sp.Rational(G[i,j]).p),int(sp.Rational(G[i,j]).q)) for j in range(nn)] for i in range(nn)]
    used=[False]*nn
    for _ in range(nn):
        cand=[k for k in range(nn) if not used[k]]; k=max(cand,key=lambda k:R[k][k])
        if R[k][k]<0: return False
        if R[k][k]==0: return all(R[i][i]==0 for i in cand)
        used[k]=True; piv=R[k][k]
        for i in range(nn):
            if used[i]:continue
            for j in range(nn):
                if used[j]:continue
                R[i][j]=R[i][j]-R[k][i]*R[k][j]/piv
    return True

def ldl_squares(M, b):
    nn=len(b); Mn=np.array(M.tolist(),dtype=float)
    idx=[i for i in range(nn) if np.abs(Mn[i]).max()>1e-12]; bb=[b[i] for i in idx]; mm=len(idx)
    R=[[Fr(int(sp.Rational(M[idx[i],idx[j]]).p),int(sp.Rational(M[idx[i],idx[j]]).q)) for j in range(mm)] for i in range(mm)]
    sq=[]; used=[False]*mm
    for _ in range(mm):
        cand=[k for k in range(mm) if not used[k] and R[k][k]!=0]
        if not cand: break
        k=max(cand,key=lambda k:abs(R[k][k])); used[k]=True; piv=R[k][k]
        col=[Fr(0)]*mm; col[k]=Fr(1)
        for j in range(mm):
            if not used[j]: col[j]=R[k][j]/piv
        # coefficient vector over Newton monomials (q-poly)
        Cd=[sp.Integer(0)]*10
        for j in range(mm):
            if col[j]!=0:
                a,i,jj,kk=bb[j]
                Cd[NIDX[(i,jj,kk)]]+=sp.Rational(col[j].numerator,col[j].denominator)*q**a
        sq.append((sp.Rational(piv.numerator,piv.denominator),[sp.expand(x) for x in Cd]))
        for i in range(mm):
            if used[i]:continue
            rki=R[k][i]
            if rki==0:continue
            for j in range(mm):
                if used[j]:continue
                R[i][j]=R[i][j]-rki*R[k][j]/piv
    return sq

def gen(L3, RHO, name, out):
    s=sp.symbols("s0:20")
    # K3(q,l,m,n): for each term coeff*s_i*s_j*s_k symmetrize over the 3 vars
    K=sp.Integer(0)
    for monom,coeff in sp.Poly(L3, *s[:9]).terms():
        idxs=[i for i,e in enumerate(monom) for _ in range(e)]
        assert len(idxs)==3, idxs
        perms=set(itertools.permutations(idxs))
        K+=coeff*sum(l**p[0]*m**p[1]*n**p[2] for p in perms)/len(perms)
    K=sp.expand(K)
    def basis(td): return [(a,i,j,k) for a in range(td+1) for i in range(3) for j in range(3) for k in range(3)
                           if i+j+k<=2 and a+i+j+k<=td]
    b0=basis(3); b1=basis(2)
    weights=[(sp.Integer(1),b0),(q,b1),(RHO-q,b1),(q*(RHO-q),b1)]
    print(f"[{name}] basis sizes={[len(b) for _,b in weights]}")
    Qs=[cp.Variable((len(b),len(b)),symmetric=True) for _,b in weights]
    t=cp.Variable(); cons=[Q-t*np.eye(len(b))>>0 for Q,(_,b) in zip(Qs,weights)]
    coeff={}
    for (w,b),Q in zip(weights,Qs):
        for (eq,el,em,en),wc in sp.Poly(w,q,l,m,n).terms():
            for ai,(qa,la,ma,na) in enumerate(b):
                for ci,(qc,lc,mc,nc) in enumerate(b):
                    e=(qa+qc+eq,la+lc+el,ma+mc+em,na+nc+en); coeff[e]=coeff.get(e,0)+float(wc)*Q[ai,ci]
    tgt={e:float(c) for e,c in sp.Poly(K,q,l,m,n).terms()}
    for e in set(coeff)|set(tgt): cons.append(coeff.get(e,0)==tgt.get(e,0.0))
    cp.Problem(cp.Maximize(t),cons).solve(solver=cp.CLARABEL)
    print(f"[{name}] margin t={t.value}")
    if t.value is None or t.value<1e-7: print("  marginal"); return None
    Gf=[np.array(Q.value) for Q in Qs]
    def form(G,b):
        nn=len(b); return sp.expand(sum(G[i,j]*(q**b[i][0]*l**b[i][1]*m**b[i][2]*n**b[i][3])*(q**b[j][0]*l**b[j][1]*m**b[j][2]*n**b[j][3]) for i in range(nn) for j in range(nn)))
    def exact_match(Pres,b,Gf,D):
        nn=len(b); G=[[sp.Rational(round((Gf[i,j]+Gf[j,i])/2*D),D) for j in range(nn)] for i in range(nn)]
        cls={}
        for i in range(nn):
            for j in range(nn):
                e=tuple(b[i][t]+b[j][t] for t in range(4)); cls.setdefault(e,[]).append((i,j))
        cur={}
        for i in range(nn):
            for j in range(nn):
                e=tuple(b[i][t]+b[j][t] for t in range(4)); cur[e]=cur.get(e,0)+G[i][j]
        Pc={e:sp.nsimplify(c) for e,c in sp.Poly(Pres,q,l,m,n).terms()}
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
            nn=len(b1); Gi=sp.Matrix(nn,nn,lambda i,j: sp.Rational(round((Gf[idx][i,j]+Gf[idx][j,i])/2*D),D))
            if not is_psd(Gi,nn): ok=False;break
            R.append(Gi)
        if not ok: continue
        Pres=sp.expand(K - q*form(R[0],b1) - (RHO-q)*form(R[1],b1) - q*(RHO-q)*form(R[2],b1))
        G0=exact_match(Pres,b0,Gf[0],D)
        if G0 is None or sp.expand(form(G0,b0)-Pres)!=0 or not is_psd(G0,len(b0)): continue
        Gres=(D,[G0,R[0],R[1],R[2]]); break
    if Gres is None: print(f"[{name}] FAILED rationalize"); return None
    D,Gs=Gres; print(f"[{name}] rationalized D={D}")
    def sm(i): return f"specMoment U {MU} {i}"
    def qpoly(expr):
        expr=sp.expand(expr)
        if expr==0: return "0"
        ts=[]
        for (e,),c in sorted(sp.Poly(expr,q).terms(),key=lambda kv:-kv[0][0]):
            c=sp.Rational(c); cs=f"({c.p}/{c.q})" if c.q!=1 else f"{c.p}"
            ts.append(cs if e==0 else (f"{cs} * q" if e==1 else f"{cs} * q ^ {e}"))
        return " + ".join(ts)
    TEMPLATE,_=gen_engine.sos3var_template()
    from collections import Counter
    def tripprod(t):
        cnt=Counter(t); pf=[]
        for idx in sorted(cnt): pf.append(f"{sm(idx)} ^ {cnt[idx]}" if cnt[idx]>1 else f"{sm(idx)}")
        return " * ".join(pf)
    def sos3form(Cd):
        parts=[]
        for (t,cstr) in TEMPLATE:
            cs=cstr
            for k in range(10): cs=cs.replace(f"d{k}", f"({qpoly(Cd[k])})")
            parts.append(f"({cs}) * ({tripprod(t)})")
        return " + ".join(parts)
    def sqmoment3(Cd):
        acc={}
        for al in range(10):
            for be in range(10):
                t=tuple(sorted(tuple(NEWTON[al][x]+NEWTON[be][x] for x in range(3))))
                acc[t]=acc.get(t,sp.Integer(0))+Cd[al]*Cd[be]
        return {k:sp.expand(v) for k,v in acc.items() if sp.expand(v)!=0}
    def gram_moment(M,b):
        cf={}
        for j in range(len(b)):
            for ll in range(len(b)):
                if M[j,ll]!=0:
                    t=tuple(sorted((b[j][1]+b[ll][1],b[j][2]+b[ll][2],b[j][3]+b[ll][3])))
                    cf[t]=cf.get(t,0)+M[j,ll]*q**(b[j][0]+b[ll][0])
        return {k:sp.expand(v) for k,v in cf.items()}
    def momform(cf):
        parts=[]
        for t,c in sorted(cf.items()):
            c=sp.expand(c)
            if c==0: continue
            parts.append(f"({qpoly(c)}) * ({tripprod(t)})")
        return " + ".join(parts) if parts else "0"
    bb=[b0,b1,b1,b1]; Lout=[]; gmforms=[]; CHUNK=3
    for gi,(G,b) in enumerate(zip(Gs,bb)):
        gm=gram_moment(G,b); gmform=momform(gm); gmforms.append(gmform)
        sqs=ldl_squares(G,b)
        sqdata=[]
        for piv,Cd in sqs:
            Dp=sp.Integer(1)
            for x in Cd:
                for c in (sp.Poly(x,q).all_coeffs() if x!=0 else []): Dp=sp.lcm(Dp,sp.Rational(c).q)
            Cw=[sp.expand(x*Dp) for x in Cd]; pivp=sp.Rational(piv)/Dp**2
            sqdata.append((pivp,Cw))
        chunknames=[]
        chunks=[sqdata[i:i+CHUNK] for i in range(0,len(sqdata),CHUNK)]
        for ci,chunk in enumerate(chunks):
            cmf={}; Lam=sp.Integer(1)
            for pivp,Cw in chunk:
                Lam=sp.lcm(Lam,pivp.q)
                for key,v in sqmoment3(Cw).items(): cmf[key]=cmf.get(key,sp.Integer(0))+pivp*v
            cmf={k:sp.expand(v) for k,v in cmf.items()}
            for v in cmf.values():
                for c in (sp.Poly(v,q).all_coeffs() if v!=0 else []): Lam=sp.lcm(Lam,sp.Rational(c).q)
            Lam=sp.Integer(Lam); cmform=momform(cmf)
            cn=f"{name}{gi}c{ci}"; chunknames.append((cn,cmform))
            Lout.append("set_option maxHeartbeats 2000000 in")
            Lout.append("set_option maxRecDepth 4000 in")
            Lout.append(f"lemma {cn} (hU : IsGraphon U μ) (q : ℝ) :")
            Lout.append(f"    (0:ℝ) ≤ {cmform} := by")
            rhst=[]
            for ki,(pivp,Cw) in enumerate(chunk):
                args=" ".join(f"({qpoly(Cw[k])})" for k in range(10))
                Lout.append(f"  have h{ki} := sos3var3 hU {args}")
                ip=sp.Integer(Lam*pivp); rhst.append((str(ip),sos3form(Cw),f"h{ki}"))
            rhs=" + ".join(f"({ip}) * ({fm})" for ip,fm,_ in rhst)
            Lout.append(f"  have key : ({Lam}:ℝ) * ({cmform}) = {rhs} := by ring")
            tn=[]
            for ti,(ip,fm,hn) in enumerate(rhst):
                Lout.append(f"  have t{ti} : (0:ℝ) ≤ ({ip}) * ({fm}) := mul_nonneg (by norm_num) {hn}")
                tn.append(f"t{ti}")
            Lout.append(f"  have hL : (0:ℝ) ≤ ({Lam}:ℝ) * ({cmform}) := by rw [key]; linarith [{', '.join(tn)}]")
            Lout.append(f"  exact (mul_nonneg_iff_of_pos_left (by norm_num : (0:ℝ) < {Lam})).mp hL")
            Lout.append("")
        Lout.append("set_option maxHeartbeats 2000000 in")
        Lout.append("set_option maxRecDepth 4000 in")
        Lout.append(f"lemma {name}{gi} (hU : IsGraphon U μ) (q : ℝ) :")
        Lout.append(f"    (0:ℝ) ≤ {gmform} := by")
        csum=" + ".join(f"({cmf})" for _,cmf in chunknames)
        Lout.append(f"  have key : {gmform} = {csum} := by ring")
        hh=", ".join(f"{cn} hU q" for cn,_ in chunknames)
        Lout.append(f"  rw [key]; linarith [{hh}]")
        Lout.append("")
    def L3form():
        cf={}
        for monom,coeff in sp.Poly(L3,*s[:9]).terms():
            idxs=tuple(sorted(i for i,e in enumerate(monom) for _ in range(e)))
            cf[idxs]=cf.get(idxs,0)+coeff
        return momform({k:sp.expand(v) for k,v in cf.items()})
    L3f=L3form()
    rhoq=f"({RHO.p}/{RHO.q} - q)"
    Lout.append("set_option maxHeartbeats 4000000 in")
    Lout.append("set_option maxRecDepth 4000 in")
    Lout.append(f"lemma {name} (hU : IsGraphon U μ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ {RHO.p}/{RHO.q}) :")
    Lout.append(f"    0 ≤ {L3f} := by")
    Lout.append(f"  have hy : (0:ℝ) ≤ {RHO.p}/{RHO.q} - q := by linarith")
    Lout.append(f"  have e1 := mul_nonneg hq0 ({name}1 hU q)")
    Lout.append(f"  have e2 := mul_nonneg hy ({name}2 hU q)")
    Lout.append(f"  have e3 := mul_nonneg (mul_nonneg hq0 hy) ({name}3 hU q)")
    Lout.append(f"  have key : {L3f} = ({gmforms[0]}) + q * ({gmforms[1]}) + {rhoq} * ({gmforms[2]}) + q * {rhoq} * ({gmforms[3]}) := by ring")
    Lout.append(f"  rw [key]; linarith [{name}0 hU q, e1, e2, e3]")
    open(out,"w",encoding="utf-8").write("\n".join(Lout))
    print(f"[{name}] emitted -> {out}")
    return True

if __name__=="__main__":
    import pickle
    Ld=pickle.load(open("phi11_L.pkl","rb"))
    gen(sp.sympify(Ld[3]), sp.Rational(1,3), "cert11_L3", "cert11_L3.txt")
