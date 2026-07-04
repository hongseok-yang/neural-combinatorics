#!/usr/bin/env python3
"""Validate the aggregate forced-coupling lemma:

For any graphon U (0<=U<=1), any unit eigenfunction phi of A (A phi = alpha phi,
int phi = 0), with a = int phi+ = int phi-, wpm = projections of phi+- - a onto
span{1,phi}-perp:

  (L)  a * <g, |phi|>  >=  alpha ||phi+||^2 ||phi-||^2 - q a^2 - <w+, A w->

and the weaker closed forms
  (L')  a <g,|phi|> >= alpha ||phi+||^2||phi-||^2 - q a^2 - (1/2)||w+|| ||w-||
  (L'') ||g|| sqrt(1-4a^2) * a >= RHS of (L')     [since <g,|phi|> = <g,|phi|-2a>]

Test on random block graphons (all eigenvectors of A, esp. positive eigenvalues),
plus the two-clique family.
"""
import numpy as np
rng = np.random.default_rng(42)

def check(w, Uv, tol=1e-10):
    k = len(w)
    sw = np.sqrt(w)
    Tu = sw[:, None]*Uv*sw[None, :]
    one = sw
    q = one @ Tu @ one
    g = Tu @ one - q*one
    P = np.eye(k) - np.outer(one, one)
    A = P @ Tu @ P
    evals, evecs = np.linalg.eigh(A)
    viol = []
    for i in range(k):
        if abs(one @ evecs[:, i]) > 1e-8:
            continue
        alpha = evals[i]
        phi = evecs[:, i]           # symmetrized coords; function values f = phi/sw
        f = phi/sw                  # function on blocks
        # phi+ etc as functions: f+ = max(f,0)
        fp = np.maximum(f, 0.0); fm = np.maximum(-f, 0.0)
        a = np.sum(w*fp)
        am = np.sum(w*fm)
        assert abs(a - am) < 1e-9
        n2p = np.sum(w*fp**2); n2m = np.sum(w*fm**2)
        gf = g/sw                   # g as function
        gip = np.sum(w*gf*(fp+fm))  # <g,|phi|>
        # w+- = (f+- - a) - <f+-, f> f   (in L2(w), inner prods weighted)
        cp = np.sum(w*fp*f); cm = np.sum(w*fm*f)
        wp = (fp - a) - cp*f; wm = (fm - am) - cm*f
        nwp = np.sqrt(max(0.0, np.sum(w*wp**2))); nwm = np.sqrt(max(0.0, np.sum(w*wm**2)))
        # exact <w+, A w-> term
        # compute A w- as function: Aw = P Tu P; in function coords:
        vm = sw*wm
        Avm = P @ Tu @ (P @ vm)
        wAw = (sw*wp) @ Avm
        lhs = a*gip
        rhsL = alpha*n2p*n2m - q*a*a - wAw
        rhsLp = alpha*n2p*n2m - q*a*a - 0.5*nwp*nwm
        if lhs < rhsL - tol:
            viol.append(("L", alpha, lhs, rhsL))
        if lhs < rhsLp - tol:
            viol.append(("L'", alpha, lhs, rhsLp))
        # L'' only meaningful when 1-4a^2 >= 0 (always true: a<=1/2)
        gn = np.sqrt(np.sum(w*gf**2))
        s4 = max(0.0, 1 - 4*a*a)
        if gn*np.sqrt(s4)*a < rhsLp - tol:
            viol.append(("L''", alpha, gn*np.sqrt(s4)*a, rhsLp))
    return viol

nv = 0; ntests = 0
for trial in range(4000):
    k = rng.integers(2, 7)
    w = rng.dirichlet(np.ones(k))
    Uv = rng.random((k, k)); Uv = (Uv + Uv.T)/2
    v = check(w, Uv)
    ntests += 1
    if v:
        nv += 1
        print("VIOLATION:", v[:2])
        if nv > 4: break
print(f"random block graphons: {ntests} tested, violations: {nv}")

# two-clique family sharpness
print("\ntwo-clique family (values of LHS/RHS of L''):")
for s in (0.3, 0.1, 0.03, 0.01, 0.003):
    w = np.array([(1-s)/2, (1-s)/2, s])
    Uv = np.zeros((3,3)); Uv[0,0] = Uv[1,1] = 1.0
    k=3; sw=np.sqrt(w); Tu = sw[:,None]*Uv*sw[None,:]; one=sw
    q = one@Tu@one; g = Tu@one - q*one
    P = np.eye(3)-np.outer(one,one); A = P@Tu@P
    evals, evecs = np.linalg.eigh(A)
    i = np.argmax(evals + (np.abs(evecs.T@one)>1e-8)*(-10))
    alpha = evals[i]; f = evecs[:,i]/sw
    fp=np.maximum(f,0); fm=np.maximum(-f,0)
    a=np.sum(w*fp); n2p=np.sum(w*fp**2); n2m=np.sum(w*fm**2)
    cp=np.sum(w*fp*f); cm=np.sum(w*fm*f)
    wp=(fp-a)-cp*f; wm=(fm-a)-cm*f
    nwp=np.sqrt(abs(np.sum(w*wp**2))); nwm=np.sqrt(abs(np.sum(w*wm**2)))
    gf=g/sw; gn=np.sqrt(np.sum(w*gf**2))
    rhs = alpha*n2p*n2m - q*a*a - 0.5*nwp*nwm
    lhs = gn*np.sqrt(max(0,1-4*a*a))*a
    print(f"  s={s}: alpha-q={alpha-q:.5f}  LHS={lhs:.6f} RHS={rhs:.6f} ratio={lhs/rhs:.3f}")
