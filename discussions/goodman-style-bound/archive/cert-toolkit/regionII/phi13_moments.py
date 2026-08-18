# -*- coding: utf-8 -*-
"""Compute Phi_13 in moments (q, s0..s10), split into L1..L6, inspect piece degrees."""
import sympy as sp
from collections import Counter, defaultdict
from itertools import combinations
import pickle

def path_components(n, subset):
    adj=[set() for _ in range(n)]
    for i in subset:
        u,v=i,(i+1)%n; adj[u].add(v); adj[v].add(u)
    seen=set(); comps=[]
    for v in range(n):
        if adj[v] and v not in seen:
            st=[v]; seen.add(v); et=0
            while st:
                a=st.pop(); et+=len(adj[a])
                for b in adj[a]:
                    if b not in seen: seen.add(b); st.append(b)
            comps.append(et//2)
    return tuple(sorted(comps,reverse=True))

def cycle_forest_counts(n):
    return {r: Counter(path_components(n,s) for s in combinations(range(n),r)) for r in range(n+1)}

def path_formulae(maxn):
    q=sp.symbols("q"); s=sp.symbols("s0:30")
    a=sp.Integer(1); h=defaultdict(lambda: sp.Integer(0)); xs={0:a}
    for n in range(1,maxn+1):
        inner=sum(c*s[p] for p,c in h.items()); a_new=sp.expand(q*a+inner)
        h_new=defaultdict(lambda: sp.Integer(0)); h_new[0]+=a
        for pwr,c in h.items(): h_new[pwr+1]+=c
        a,h=a_new,h_new; xs[n]=a
    return q,s,xs

def expression_from_counts(n,q,xs):
    counts=cycle_forest_counts(n)
    def term(comp):
        out=sp.Integer(1)
        for a in comp: out*= q if a==1 else xs[a]
        return out
    E=sp.Integer(1)
    for r in range(1,n):
        for comp,c in counts[r].items(): E+=(-1)**r*c*term(comp)
    E-=xs[n-1]
    return sp.expand(E)

q,s,xs=path_formulae(12)
target=(1-q)**13-(1-q)*q**12
Phi=sp.expand(expression_from_counts(13,q,xs)-target)
poly=sp.Poly(Phi,*s[:11])
L={d:sp.Integer(0) for d in range(7)}
for monom,coeff in poly.terms():
    L[sum(monom)]+=coeff*sp.prod(v**e for v,e in zip(s[:11],monom))
for d in range(7): L[d]=sp.expand(L[d])
print("deg0 zero:", L[0]==0, "  deg6==12s0^6:", sp.expand(L[6]-12*s[0]**6)==0)
for d in range(1,7):
    P=sp.Poly(L[d],*s[:11])
    maxidx=max((max((i for i,e in enumerate(m) if e>0), default=0) for m,_ in P.terms()), default=0)
    print(f"L{d}: #s-monomials={len(P.terms())}, max moment index s_{maxidx}, q-deg={sp.Poly(L[d],q).degree()}")
pickle.dump({d:sp.srepr(L[d]) for d in range(1,7)}, open("phi13_L.pkl","wb"))
print("saved phi13_L.pkl")
