# -*- coding: utf-8 -*-
"""Generate fixed expanded multivariate Hankel-SOS engine lemmas (sos2var4, sos3var3)
matching sos_sq_expand_2var / sos_sq_expand_3var after simp."""
import sympy as sp

MU="μ"
def sm(i): return f"specMoment U {MU} {i}"

def sos2var_template(N):
    """Return ordered list [(a, b, coeff_str_in_c_symbols)] matching the sos2varN statement,
    so callers can substitute c{i}{j} -> their value strings to build a matching expression."""
    C=[[sp.Symbol(f"c{a}{b}") for b in range(N)] for a in range(N)]
    expr=0
    for a in range(N):
        for b in range(N):
            for c in range(N):
                for dd in range(N):
                    expr+=C[a][b]*C[c][dd]*sp.Symbol(f"S_{a+c}_{b+dd}")
    expr=sp.expand(expr)
    poly=sp.Poly(expr, *[sp.Symbol(f"S_{i}_{j}") for i in range(2*N-1) for j in range(2*N-1)])
    terms={}
    svars=[(i,j) for i in range(2*N-1) for j in range(2*N-1)]
    for monom,coeff in poly.terms():
        idx=[k for k,e in enumerate(monom) if e==1]
        i,j=svars[idx[0]]; key=(min(i,j),max(i,j))
        terms[key]=terms.get(key,0)+coeff
    out=[]
    for (i,j),c in sorted(terms.items()):
        c=sp.expand(c)
        if c==0: continue
        out.append((i,j,str(c).replace("**","^")))
    return out

def gen_sos2var(N, name):
    # C a b for a,b in 0..N-1 ; value 0 <= sum_{a,b,c,d} C[a][b] C[c][d] s_{a+c} s_{b+d}
    C=[[sp.Symbol(f"c{a}{b}") for b in range(N)] for a in range(N)]
    expr=0
    for a in range(N):
        for b in range(N):
            for c in range(N):
                for dd in range(N):
                    expr+=C[a][b]*C[c][dd]*sp.Symbol(f"S_{a+c}_{b+dd}")
    parts=[]
    for (i,j,cstr) in sos2var_template(N):
        prod=f"{sm(i)} * {sm(j)}" if i!=j else f"{sm(i)} ^ 2"
        parts.append(f"({cstr}) * ({prod})")
    rhs=" + ".join(parts)
    # signature: c00 c01 ... c_{N-1,N-1}
    args=" ".join(f"c{a}{b}" for a in range(N) for b in range(N))
    L=[]
    L.append(f"-- Degree-({N-1},{N-1}) bivariate Hankel SOS (basis monomials of degree < {N}).")
    L.append("set_option maxHeartbeats 6000000 in")
    L.append(f"lemma {name} (hU : IsGraphon U μ) ({args} : ℝ) :")
    L.append(f"    0 ≤ {rhs} := by")
    # C as function
    cdef=("fun a b => " + " ".join(
        [f"if a = {a} then (if b = {b} then c{a}{b} else" for a in range(N) for b in range(N)]))
    # simpler: nested if
    def cbuild():
        s="fun a b =>"
        for a in range(N):
            s+=f" if a = {a} then ("
            for b in range(N):
                s+=f"if b = {b} then c{a}{b} else "
            s+="0) else "
        s+="0"
        return s
    L.append(f"  have h := sos_sq_expand_2var hU ({cbuild()}) {N}")
    L.append("  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h")
    L.append("  norm_num at h")
    L.append("  nlinarith [h]")
    return "\n".join(L)

if __name__=="__main__":
    print(gen_sos2var(4,"sos2var4"))

def sos3var_newton(maxdeg=2, name='sos3var3'):
    """Fixed trivariate engine over Newton basis (total degree <=2 in lam,mu,nu) = 10 monomials.
    Returns (lean_text, monomials list). Coefficients named d0..d9."""
    N=maxdeg+1
    mons=[(i,j,k) for i in range(N) for j in range(N) for k in range(N) if i+j+k<=maxdeg]
    names=[f"d{k}" for k in range(len(mons))]
    sym={mons[k]:sp.Symbol(names[k]) for k in range(len(mons))}
    # statement: sum over alpha,beta of sym[alpha] sym[beta] * S_{a+d}_{b+e}_{c+f} (sorted triple)
    acc={}
    for al in mons:
        for be in mons:
            t=tuple(sorted((al[0]+be[0],al[1]+be[1],al[2]+be[2])))
            acc[t]=acc.get(t,0)+sym[al]*sym[be]
    def sm(i): return f"specMoment U μ {i}"
    parts=[]
    for t,c in sorted(acc.items()):
        c=sp.expand(c)
        if c==0: continue
        i,j,k=t
        # product s_i s_j s_k with repeats -> ^ powers
        from collections import Counter
        cnt=Counter(t); pf=[]
        for idx in sorted(cnt):
            pf.append(f"{sm(idx)} ^ {cnt[idx]}" if cnt[idx]>1 else f"{sm(idx)}")
        prod=" * ".join(pf)
        parts.append(f"({str(c).replace('**','^')}) * ({prod})")
    rhs=" + ".join(parts)
    args=" ".join(names)
    # C mapping for sos_sq_expand_3var as a nested grid if (a,b,c in 0..2), value d_k on Newton else 0
    val={mons[k]:names[k] for k in range(len(mons))}
    def cbuild():
        s="fun a b c =>"
        for a in range(N):
            s+=f" if a = {a} then ("
            for b in range(N):
                s+=f"if b = {b} then ("
                for c in range(N):
                    s+=f"if c = {c} then {val.get((a,b,c),'0')} else "
                s+="0) else "
            s+="0) else "
        s+="0"
        return s
    L=[]
    L.append("-- Trivariate Hankel SOS over the Newton basis (total degree <= 2 in lam,mu,nu).")
    L.append("set_option maxHeartbeats 4000000 in")
    L.append(f"lemma {name} (hU : IsGraphon U μ) ({args} : ℝ) :")
    L.append(f"    0 ≤ {rhs} := by")
    L.append(f"  have h := sos_sq_expand_3var hU ({cbuild()}) {N}")
    L.append("  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h")
    L.append("  norm_num at h")
    L.append("  nlinarith [h]")
    return "\n".join(L), mons

def sos3var_template():
    """Ordered list [(sorted_triple, coeff_str_in_d_symbols)] matching sos3var3."""
    mons=[(0,0,0),(1,0,0),(0,1,0),(0,0,1),(2,0,0),(0,2,0),(0,0,2),(1,1,0),(1,0,1),(0,1,1)]
    names=[f"d{k}" for k in range(len(mons))]
    sym={mons[k]:sp.Symbol(names[k]) for k in range(len(mons))}
    acc={}
    for al in mons:
        for be in mons:
            t=tuple(sorted((al[0]+be[0],al[1]+be[1],al[2]+be[2])))
            acc[t]=acc.get(t,0)+sym[al]*sym[be]
    out=[]
    for t,c in sorted(acc.items()):
        c=sp.expand(c)
        if c==0: continue
        out.append((t, str(c).replace("**","^")))
    return out, mons
