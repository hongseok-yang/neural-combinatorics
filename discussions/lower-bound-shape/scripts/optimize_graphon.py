#!/usr/bin/env python3
"""
Direct step-graphon optimisation to probe Step A1.

We minimise t(P,W) (and separately t(K4,W)) over symmetric step graphons W in
[0,1]^{n x n} at fixed edge density x = t(K2,W), by projected-gradient with
random restarts.  Densities and their gradients are exact (einsum); the
gradient is finite-difference checked.

Goals:
  (E1) Find the t(P,.)-minimiser; inspect whether it is a 3-blowup skeleton,
       and compute its t(K4,W).
  (E2) Compute the K4-minimum g_{4,3}(x) (min t(K4) at the same x) and compare:
       is the t(P)-minimiser's t(K4) close to g_{4,3}?  (Tests the strategy
       note's Step A1 mechanism.)
"""
import numpy as np

# ---- densities on an n-block step graphon (uniform blocks) ----
def tK2(W):
    n=W.shape[0]; return W.sum()/n**2
def tK4(W):
    n=W.shape[0]
    return np.einsum('ij,ik,il,jk,jl,kl->',W,W,W,W,W,W,optimize=True)/n**4
def tP(W):
    n=W.shape[0]
    d=W.mean(1)
    # t(P) = (1/n) sum_l kappa_l d_l ; kappa_l = rooted-K4 at l
    kappa=np.einsum('li,lj,lk,ij,ik,jk->l',W,W,W,W,W,W,optimize=True)/n**3
    return (kappa*d).mean()

# ---- exact gradients (sum over edges of H, each endpoint pair left free) ----
def gradK2(W):
    n=W.shape[0]; return np.ones_like(W)*2/n**2 - np.eye(n)/n**2  # symmetric var
def gradK4(W):
    n=W.shape[0]
    # 6 equivalent edges; remove edge (i,j): contract k,l
    M=np.einsum('ik,il,jk,jl,kl->ij',W,W,W,W,W)/n**4
    G=6*M
    return (G+G.T)/2*2 - np.diag(np.diag(G))*0 + 0*G  # symmetric handled below
def _grad_generic(W, edges, nV):
    """grad of mean-hom-density for graph with given edges (vertices 0..nV-1)."""
    n=W.shape[0]
    G=np.zeros_like(W)
    letters='ijklmnop'
    ones=np.ones(n)
    for (u,v) in edges:
        # einsum over all vertices, omit factor W on edge (u,v), leave u,v free
        subs=[]; args=[]
        for (a,b) in edges:
            if (a,b)==(u,v): continue
            subs.append(letters[a]+letters[b]); args.append(W)
        present=set(''.join(subs))
        out=letters[u]+letters[v]
        # any leaf output index (absent from remaining edges) broadcasts uniformly
        for ch in out:
            if ch not in present:
                subs.append(ch); args.append(ones)
        expr=','.join(subs)+'->'+out
        G+=np.einsum(expr,*args,optimize=True)
    G=G/n**nV
    R=G+G.T                       # off-diagonal symmetric entries: 2*dt/dW_ab
    np.fill_diagonal(R,np.diag(G))# diagonal entry perturbed once: dt/dW_aa
    return R
P_edges=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,4)]
K4_edges=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def gradP(W):  return _grad_generic(W,P_edges,5)
def gradK4b(W):return _grad_generic(W,K4_edges,4)

# ---- finite-difference check ----
def fd_check():
    n=5; rng=np.random.default_rng(0); W=rng.random((n,n)); W=(W+W.T)/2
    for f,g,nm in [(tP,gradP,'P'),(tK4,gradK4b,'K4')]:
        G=g(W); Gfd=np.zeros_like(W); h=1e-6
        for a in range(n):
            for b in range(a,n):
                Wp=W.copy(); Wm=W.copy()
                Wp[a,b]+=h; Wp[b,a]=Wp[a,b]; Wm[a,b]-=h; Wm[b,a]=Wm[a,b]
                d=(f(Wp)-f(Wm))/(2*h)
                Gfd[a,b]=d; Gfd[b,a]=d
        # analytic G has off-diagonal counted twice (W_ab and W_ba) -> compare to Gfd
        err=np.max(np.abs(G-Gfd))
        print(f"  grad {nm}: max|analytic-FD| = {err:.2e}")
fd_check()

# ---- projected-gradient minimiser of objective at fixed x (penalty) ----
def minimize(obj, gobj, x, n=16, rho=300.0, iters=4000, restarts=6, seed=0):
    rng=np.random.default_rng(seed); best=None; bestval=np.inf
    for r in range(restarts):
        W=rng.random((n,n)); W=(W+W.T)/2
        m=np.zeros_like(W); v=np.zeros_like(W); b1,b2,eps=0.9,0.999,1e-8; lr=0.02
        for t in range(1,iters+1):
            g = gobj(W) + rho*2*(tK2(W)-x)*gradK2(W)
            m=b1*m+(1-b1)*g; v=b2*v+(1-b2)*g*g
            mh=m/(1-b1**t); vh=v/(1-b2**t)
            W=W-lr*mh/(np.sqrt(vh)+eps)
            W=np.clip(W,0,1); W=(W+W.T)/2
        val=obj(W); con=abs(tK2(W)-x)
        score=val+1e5*con**2
        if score<bestval: bestval=score; best=(W.copy(),val,con)
    return best

def describe(W, tol=0.12):
    """heuristic: cluster blocks by degree, report block structure."""
    n=W.shape[0]; d=W.mean(1)
    order=np.argsort(d); Wo=W[order][:,order]
    return d, Wo

# LS K4-min at density x: minimise t(K4) at fixed x.
# Reiher's clique-density theorem: on the first Turan interval I_3=[2/3,3/4] the
# extremal graphon has one part of size s and three equal parts of size (1-s)/3,
# with x_3(s)=1-s^2-(1-s)^2/3 and g_{4,3}(s)=(8/9) s (1-s)^3.  Inverting x_3 on
# s in [0,1/4] gives s=(1-sqrt(9-12x))/4.  (Endpoints: x=2/3->0, x=3/4->3/32.)
def Psi_K4_min(x):
    x=min(max(x,2/3),3/4)              # clamp to the interval (achieved x may drift)
    s=(1-np.sqrt(9-12*x))/4
    return 8/9*s*(1-s)**3

def Psi_P_balanced(x):
    # value of the in-family balanced reduced curve (numeric min over alpha)
    a=np.linspace((1-np.sqrt(3-4*x))/2+1e-6,(1+np.sqrt(3-4*x))/2-1e-6,200000)
    s=1-a; q=(x-1/2-a+1.5*a**2)/a**2
    feas=(q>=0)&(q<=0.5)
    val=1.5*a**2*(1-a)**2*((3-a)/2*q+a*q**2)
    val=np.where(feas,val,np.inf)
    return val.min()

print("\n=== E1/E2: minimise t(P) and t(K4) at fixed x ===")
print("Comparisons are made at the ACHIEVED density x'=t(K2,Wopt) to remove the")
print("penalty-constraint confound.  conj-ok means t(P,Wopt) >= Psi_P(x') (the")
print("global-min conjecture); K4gap = t(K4,Wopt)-g43(x') tests the A1 mechanism.")
print(f"{'x':>6} {'xprime':>8} {'minP':>10} {'Psi_P(xp)':>10} {'conj-ok':>8} {'tK4@Pmin':>10} {'g43(xp)':>10} {'K4gap':>9}")
for x in [0.68, 0.70, 0.72]:
    WP,vP,cP=minimize(tP,gradP,x,seed=1)
    WK,vK,cK=minimize(tK4,gradK4b,x,seed=1)
    xpP=tK2(WP); xpK=tK2(WK)
    PsiP=Psi_P_balanced(xpP)            # balanced reduced value at ACHIEVED density
    # g43 at xpP: re-minimise t(K4) at xpP if different; here use WK's value adjusted
    g43=Psi_K4_min(xpP)
    k4_at_Pmin=tK4(WP)
    conj_ok = vP >= PsiP-2e-3
    print(f"{x:6.3f} {xpP:8.5f} {vP:10.6f} {PsiP:10.6f} {str(conj_ok):>8} "
          f"{k4_at_Pmin:10.6f} {g43:10.6f} {k4_at_Pmin-g43:9.5f}")
    d=np.sort(WP.mean(1))
    print(f"        t(P)-min degree profile (sorted): {np.round(d,3)}")
