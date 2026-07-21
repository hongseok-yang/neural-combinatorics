"""Independent core: all quantities from scratch, from BRIEF notation.
   Parametrize Region II by (e, kappa). alpha=(1-e)/2, d=kappa*e, q=alpha-d,
   p=1-q, L=sqrt(pq-alpha^2). Admissible: e in(0,1/3), 0<kappa<=kappa_hi.
"""
import mpmath as mp
mp.mp.dps = 60

def quantities(e, kap, m):
    e = mp.mpf(e); kap = mp.mpf(kap); m = int(m)
    alpha = (1-e)/2
    d = kap*e
    q = alpha - d
    p = 1 - q
    L2 = p*q - alpha*alpha
    if L2 < 0:
        return None
    L = mp.sqrt(L2)
    f = alpha - L
    x = alpha/p; s = q/p; y = L/p; ell = L/alpha
    xi = (1-e)**2 * kap / e            # = 4 alpha^2 d / e^2
    def km(lam):
        return (p**(m-1) - lam**(m-1))/(p+lam)
    Am = 2*L**(m-2) + m*km(alpha)
    Bm = 2*L**(m-2) + m*km(L)
    Rm = alpha**m + L**m - p*q**(m-1)
    Cm = Bm * f * mp.sqrt(2*alpha) * e*e / (4*alpha*alpha)
    rho = (Am/Bm) * mp.sqrt(alpha) / (2*mp.sqrt(2)*f)
    # psi = max_{0<=lam<=1} lam*xi - lam^2/(4(rho+lam))
    # unconstrained interior optimum; also check endpoints 0 and 1.
    def g(lam):
        return lam*xi - lam*lam/(4*(rho+lam))
    # derivative: xi - [2lam*4(rho+lam) - lam^2*4]/(16(rho+lam)^2)
    #   = xi - (2lam(rho+lam)-lam^2)/(4(rho+lam)^2) = xi - (2 lam rho+lam^2)/(4(rho+lam)^2)
    # solve numerically on [0,1]
    best = max(g(mp.mpf(0)), g(mp.mpf(1)))
    # sample + refine
    N=200
    for i in range(N+1):
        lam = mp.mpf(i)/N
        v = g(lam)
        if v>best: best=v
    # golden refine
    lo,hi=mp.mpf(0),mp.mpf(1)
    for _ in range(200):
        m1=lo+(hi-lo)/3; m2=hi-(hi-lo)/3
        if g(m1)<g(m2): lo=m1
        else: hi=m2
    v=g((lo+hi)/2)
    if v>best: best=v
    psi = best
    return dict(alpha=alpha,d=d,q=q,p=p,L=L,f=f,x=x,s=s,y=y,ell=ell,
                xi=xi,Am=Am,Bm=Bm,Rm=Rm,Cm=Cm,rho=rho,psi=psi)

def kappa_hi(e):
    e=mp.mpf(e)
    kmax=(1-e)/(1+e)
    kq=(1-3*e)/(6*e)
    return min(kmax,kq)

def kappa_xi(e):
    e=mp.mpf(e)
    return e/(1-e)**2

if __name__=="__main__":
    # sanity at a point
    for m in (9,11,13):
        Q=quantities(mp.mpf(1)/10, mp.mpf(1)/10, m)
        print(m, "Rm=",mp.nstr(Q['Rm'],6),"Cpsi=",mp.nstr(Q['Cm']*Q['psi'],6),
              "xi=",mp.nstr(Q['xi'],5))
