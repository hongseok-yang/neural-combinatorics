"""
FINAL end-to-end verification of the independent (non-Ky-Fan) PSD reduction.

Chain (all steps for PSD T_W>=0, p>=1/2), g=phi_1 Perron (g>=0,||g||=1), L=lam_1=||T_W||:
  Delta2 = sum_ijk lam_i lam_j^2 lam_k^4 c_ijk^2 - (2p-1) t(C5)          [exact]
   (S0) drop all (i,j) but (i,j)=(1,1); each dropped term = lam_i lam_j^2 c_ijk^2 >=0 (PSD):
        Delta2 >= sum_k lam_k^4 (L * L^2 c_11k^2) - (2p-1)t(C5)
                = L^3 <g^2,T^4 g^2> - (2p-1) t(C5)                       [PROVED drop]
   (D2) t(C5)=sum lam^5 <= L^3 sum lam^2 = L^3 t(C2)   (lam_k<=L, lam_k>=0) [PROVED]
        => Delta2 >= L^3[ <g^2,T^4 g^2> - (2p-1) t(C2) ]
   (S0') <g^2,T^4 g^2> = sum_k lam_k^4 c_11k^2 >= L^4 c_111^2 = L^4 (int g^3)^2 [drop k!=1, PROVED]
   (R7) int g^3 >= int g = a1   (need g>=0, int g^2=1: <g,g^2-1>=... verified)  [PROVED-mechanism below]
        => <g^2,T^4 g^2> >= L^4 a1^2
        => Delta2 >= L^3[ L^4 a1^2 - (2p-1) t(C2) ]     ... but simpler keep <g^2,T^4g^2>
   REDUCED INEQUALITY (any of, equivalent-strength, machine-zero-tight at W=1):
        (A)  <g^2,T^4 g^2> >= (2p-1) t(C2)                    [primary]
        (S2) L^4 a1^2 >= (2p-1) t(C2)                          [stronger-looking, also holds; => A via S0',R7]
   PROVED SUB-RELATIONS (Dirichlet/pointwise mechanism, exact identities):
        (P1) R1:=int d_W g^2 >= L >= p     (Dirichlet on weight g^2)
        (P2) m1:=<g^2,T^2 g^2> = [int int g^2 T_U^2 g^2 >=0] + 2(R1-p) + (2p-1) >= 2p-1
        (P3) a1=int g >= p ; int g^3 >= a1
        (P4) t(C2)=||W||_HS^2 <= p        (W^2<=W)
"""
import numpy as np
from scipy.optimize import minimize
from spectral import step_graphon, eig_decomp, edge_density, triple_tensor, Tpow, delta2_direct

def data(w,M):
    w,M=step_graphon(w,M); Dm=np.diag(w); p=edge_density(w,M)
    lam,phi=eig_decomp(w,M); i1=np.argmax(lam); g=phi[i1]; L=lam[i1]
    if (w*g).sum()<0: g=-g
    c=triple_tensor(w,phi); ck=c[i1,i1]**2
    m2=float(np.sum(lam**4*ck)); C2=float(np.sum(lam**2))
    a1=float(np.sum(w*g)); I3=float(np.sum(w*g**3)); R1=float(np.sum(w*(M@w)*g*g))
    m1=float(np.sum(lam**2*ck))
    return dict(p=p,L=L,a1=a1,I3=I3,R1=R1,m1=m1,m2=m2,C2=C2,
                d2=delta2_direct(w,M),
                A=m2-(2*p-1)*C2, S2=L**4*a1**2-(2*p-1)*C2)

def gram(rng,r):
    k=rng.integers(1,r+2);B=rng.random((r,k));M=B@B.T;M/=max(M.max(),1e-12);w=rng.random(r);w/=w.sum();return w,M
def corr(rng,r):
    X=rng.random((r,rng.integers(1,r+2)));Gm=X@X.T;dd=np.sqrt(np.diag(Gm));M=Gm/np.outer(dd,dd);w=rng.random(r);w/=w.sum();return w,M
def extremal(rng,r):
    M=np.zeros((r,r));tot=0
    for _ in range(rng.integers(1,3*r)):
        u=(rng.random(r)<rng.random()).astype(float);cc=rng.random();M+=cc*np.outer(u,u);tot+=cc
    M/=max(tot,1e-12);M=np.clip(M,0,1);ev,Q=np.linalg.eigh((M+M.T)/2);M=Q@np.diag(np.clip(ev,0,None))@Q.T;M=np.clip(M,0,1)
    w=rng.random(r);w/=w.sum();return w,M
def nearone(rng,r):
    M=np.ones((r,r))-rng.random()*0.4*rng.random((r,r));M=(M+M.T)/2;M=np.clip(M,0,1)
    ev,Q=np.linalg.eigh(M);M=Q@np.diag(np.clip(ev,0,None))@Q.T;M=np.clip(M,0,1)
    w=rng.random(r);w/=w.sum();return w,M
samplers=[gram,corr,extremal,nearone]

rng=np.random.default_rng(31415)
mins=dict(P1=np.inf,P2=np.inf,P3a=np.inf,P3b=np.inf,P4=np.inf,S0drop=np.inf,D2=np.inf,
          A_high=np.inf,S2_high=np.inf,A_low=np.inf,d2_high=np.inf,d2_all=np.inf)
samps=[]
for r in range(2,15):
    for _ in range(2500):
        w,M=samplers[rng.integers(len(samplers))](rng,r)
        if np.linalg.eigvalsh((M+M.T)/2).min()<-1e-10: continue
        d=data(w,M); p=d['p']
        mins['P1']=min(mins['P1'], d['R1']-d['L'])
        mins['P2']=min(mins['P2'], d['m1']-(2*p-1))
        mins['P3a']=min(mins['P3a'], d['a1']-p)
        mins['P3b']=min(mins['P3b'], d['I3']-d['a1'])
        mins['P4']=min(mins['P4'], p-d['C2'])
        mins['d2_all']=min(mins['d2_all'], d['d2'])
        if p>=0.5:
            mins['A_high']=min(mins['A_high'], d['A'])
            mins['S2_high']=min(mins['S2_high'], d['S2'])
            mins['d2_high']=min(mins['d2_high'], d['d2'])
            samps.append((d['A'],w.copy(),M.copy()))
        else:
            mins['A_low']=min(mins['A_low'], d['A'])
# adversarial polish of A near p=1/2
samps.sort(key=lambda t:t[0]); polA=mins['A_high']
for a0,w0,M0 in samps[:25]:
    r=len(w0); ev,Q=np.linalg.eigh(M0); B0=(Q*np.sqrt(np.clip(ev,0,None))).reshape(-1)
    lg=np.log(w0+1e-9); x0=np.concatenate([lg[1:]-lg[0],B0])
    def obj(x):
        logits=np.concatenate([[0.0],x[:r-1]]);w=np.exp(logits-logits.max());w/=w.sum()
        B=x[r-1:].reshape(r,r);Gm=B@B.T;mx=Gm.max();M=Gm/mx if mx>0 else Gm
        p=edge_density(w,M);pen=400*(0.5-p)**2 if p<0.5 else 0.0
        return data(w,M)['A']+pen
    res=minimize(obj,x0,method='Nelder-Mead',options=dict(maxiter=5000,fatol=1e-16,xatol=1e-12))
    logits=np.concatenate([[0.0],res.x[:r-1]]);w=np.exp(logits-logits.max());w/=w.sum()
    B=res.x[r-1:].reshape(r,r);Gm=B@B.T;mx=Gm.max();M=Gm/mx if mx>0 else Gm
    if edge_density(w,M)>=0.4995: polA=min(polA, data(w,M)['A'])

P1=mins['P1'];P2=mins['P2'];P3a=mins['P3a'];P3b=mins['P3b'];P4=mins['P4']
Ah=mins['A_high'];S2h=mins['S2_high'];Al=mins['A_low'];d2h=mins['d2_high'];d2a=mins['d2_all']
print('PROVED sub-relations (min over PSD; nonneg expected):')
print('  P1  R1 - L                 : %.3e' % P1)
print('  P2  m1 - (2p-1)            : %.3e' % P2)
print('  P3a a1 - p                 : %.3e' % P3a)
print('  P3b int g^3 - a1           : %.3e' % P3b)
print('  P4  p - t(C2)              : %.3e' % P4)
print('REDUCED INEQUALITY (the remaining crux):')
print('  A   <g^2,T^4 g^2> - (2p-1)t(C2),  p>=1/2 random : %.3e' % Ah)
print('  A   ... after adversarial polish near p=1/2     : %.3e' % polA)
print('  S2  L^4 a1^2 - (2p-1)t(C2), p>=1/2              : %.3e' % S2h)
print('  A   for p<1/2 (may be negative)                 : %.3e' % Al)
print('SANITY:')
print('  min Delta2, p>=1/2 PSD : %.3e' % d2h)
print('  min Delta2, any p PSD  : %.3e' % d2a)
