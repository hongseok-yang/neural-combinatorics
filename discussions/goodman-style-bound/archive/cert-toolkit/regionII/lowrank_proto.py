# -*- coding: utf-8 -*-
"""Low-rank SOS prototype (sympy/cvxpy, NO Lean output yet).

Goal: replace the margin-maximizing SDP (which forces every Gram to FULL rank,
=> 95 squares for C13 L2) by a rank-minimizing solve, then measure the numerical
ranks. A rank-r rational PSD Gram factors (via the existing pivoted LDL) into
exactly r squares, so the total square count = sum of Gram ranks.

This script only DIAGNOSES: build K2, solve three ways, report ranks + recovered
square count. Exact rational low-rank factorization is the next step once we see
the achievable ranks.
"""
import sympy as sp, numpy as np, cvxpy as cp, pickle, sys

q, l, m = sp.symbols("q l m")

def build_K2(L2, Nb):
    s = sp.symbols("s0:20")
    K = sp.Integer(0)
    P2 = sp.Poly(L2, *s[:Nb*2])
    for monom, coeff in P2.terms():
        idxs = [i for i, e in enumerate(monom) for _ in range(e)]
        i, j = idxs
        if i == j: K += coeff*l**i*m**j
        else: K += coeff*(l**i*m**j + l**j*m**i)/2
    return sp.expand(K)

def basis(td, Nb):
    return [(a, i, j) for a in range(td+1) for i in range(Nb) for j in range(Nb)
            if i+j <= Nb-1 and a+i+j <= td]

def setup(L2, RHO, Nb):
    K = build_K2(L2, Nb)
    b0 = basis(Nb-1, Nb); b1 = basis(Nb-2, Nb)
    weights = [(sp.Integer(1), b0), (q, b1), (RHO-q, b1), (q*(RHO-q), b1)]
    Qs = [cp.Variable((len(b), len(b)), symmetric=True) for _, b in weights]
    # linear coefficient-matching constraints (exact, as in gen_bivar)
    coeff = {}
    for (w, b), Q in zip(weights, Qs):
        for (eq, el, em), wc in sp.Poly(w, q, l, m).terms():
            for ai, (qa, la, ma) in enumerate(b):
                for ci, (qc, lc, mc) in enumerate(b):
                    e = (qa+qc+eq, la+lc+el, ma+mc+em)
                    coeff[e] = coeff.get(e, 0) + float(wc)*Q[ai, ci]
    tgt = {e: float(c) for e, c in sp.Poly(K, q, l, m).terms()}
    match = [coeff.get(e, 0) == tgt.get(e, 0.0) for e in set(coeff) | set(tgt)]
    return K, weights, Qs, match

def numrank(M, tol=1e-6):
    w = np.linalg.eigvalsh((M+M.T)/2)
    mx = max(abs(w).max(), 1e-12)
    return int((w > tol*mx).sum()), w

def report(tag, Qs, weights):
    ranks = []
    for (w, b), Q in zip(weights, Qs):
        if Q.value is None:
            ranks.append(None); continue
        r, ev = numrank(Q.value)
        ranks.append(r)
    print(f"  [{tag}] gram sizes={[len(b) for _,b in weights]}  ranks={ranks}  total_squares={sum(r for r in ranks if r)}")
    return ranks

if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "c13"
    if which == "c13":
        Ld = pickle.load(open("phi13_L.pkl", "rb")); L2 = sp.sympify(Ld[2]); Nb = 5
    else:
        Ld = pickle.load(open("phi11_L.pkl", "rb")); L2 = sp.sympify(Ld[2]); Nb = 4
    RHO = sp.Rational(1, 3)
    K, weights, Qs, match = setup(L2, RHO, Nb)
    print(f"K2 built; gram sizes={[len(b) for _,b in weights]}")

    # (A) margin maximization (current method): Q - t I >> 0
    t = cp.Variable()
    cons = match + [Q - t*np.eye(Q.shape[0]) >> 0 for Q in Qs]
    cp.Problem(cp.Maximize(t), cons).solve(solver=cp.CLARABEL)
    print(f"(A) margin-max t={t.value:.4f}")
    report("margin-max", Qs, weights)

    # (B) trace minimization (low-rank heuristic): minimize sum trace, Q >> 0
    cons = match + [Q >> 0 for Q in Qs]
    cp.Problem(cp.Minimize(sum(cp.trace(Q) for Q in Qs)), cons).solve(solver=cp.CLARABEL)
    print(f"(B) trace-min done")
    ranksB = report("trace-min", Qs, weights)

    # (C) reweighted trace min (log-det surrogate, 3 iters) for lower rank
    Wt = [np.eye(Q.shape[0]) for Q in Qs]
    for it in range(4):
        cons = match + [Q >> 0 for Q in Qs]
        cp.Problem(cp.Minimize(sum(cp.trace(W @ Q) for W, Q in zip(Wt, Qs))), cons).solve(solver=cp.CLARABEL)
        Wt = [np.linalg.inv((Q.value+Q.value.T)/2 + 1e-4*np.eye(Q.shape[0])) for Q in Qs]
        Wt = [W/np.linalg.norm(W) for W in Wt]
    print(f"(C) reweighted trace-min done")
    report("reweighted", Qs, weights)

def inspect_factors(L2, RHO, Nb, tol=1e-6):
    """Solve reweighted trace-min, then for each Gram print the rank-r column-space
    factor vectors (sqrt(eig)*eigvec) and check how cleanly they rationalize."""
    K, weights, Qs, match = setup(L2, RHO, Nb)
    Wt=[np.eye(Q.shape[0]) for Q in Qs]
    for it in range(5):
        cons=match+[Q>>0 for Q in Qs]
        cp.Problem(cp.Minimize(sum(cp.trace(W@Q) for W,Q in zip(Wt,Qs))),cons).solve(solver=cp.CLARABEL)
        Wt=[np.linalg.inv((Q.value+Q.value.T)/2+1e-4*np.eye(Q.shape[0])) for Q in Qs]
        Wt=[W/np.linalg.norm(W) for W in Wt]
    for gi,((w,b),Q) in enumerate(zip(weights,Qs)):
        G=(Q.value+Q.value.T)/2
        ev,V=np.linalg.eigh(G); mx=abs(ev).max()
        keep=[i for i in range(len(ev)) if ev[i]>tol*mx]
        print(f"\n=== Gram {gi} (size {len(b)}) rank {len(keep)} ; nonzero eigs {[f'{ev[i]:.4f}' for i in keep]}")
        for i in keep:
            vec=V[:,i]*np.sqrt(ev[i])
            # normalize so largest |entry| = 1 then see if rational-friendly
            big=np.abs(vec).max(); vn=vec/big
            terms=[]
            for c,(a,li,mj) in zip(vn,b):
                if abs(c)>1e-4:
                    rc=sp.nsimplify(c, rational=True, tolerance=1e-4)
                    terms.append(f"{rc}*q^{a}l^{li}m^{mj}")
            print(f"   v(|{big:.3f}|): "+"  ".join(terms[:12])+(" ..." if len(terms)>12 else ""))

if __name__=="__main__" and len(sys.argv)>2 and sys.argv[2]=="inspect":
    Ld=pickle.load(open("phi13_L.pkl","rb")); inspect_factors(sp.sympify(Ld[2]),sp.Rational(1,3),5)
