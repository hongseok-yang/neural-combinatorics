"""Core (e,kappa) geometry, full payment C_m*psi, R_m, true ratio.
All floats for the feasibility scan; exact-rational spot checks done separately.
"""
import numpy as np

def geom(e, kap):
    alpha = (1.0-e)/2.0
    d = kap*e
    q = alpha-d
    p = 1.0-q
    L2 = alpha*e - d*(d+e)   # = pq - alpha^2
    L = np.sqrt(L2) if L2 > 0 else float('nan')
    f = alpha-L
    x = alpha/p
    s = q/p
    y = L/p
    ell = L/alpha
    xi = (1.0-e)**2*kap/e
    delta = (1.0-3.0*e)/6.0
    return dict(alpha=alpha,d=d,q=q,p=p,L2=L2,L=L,f=f,x=x,s=s,y=y,ell=ell,
                xi=xi,delta=delta,e=e,kap=kap)

def km(lam, p, m):
    return (p**(m-1)-lam**(m-1))/(p+lam)

def payment(g, m):
    """Return C_m*psi (full payment), R_m."""
    alpha,L,p,q,f,e,d,x = (g['alpha'],g['L'],g['p'],g['q'],g['f'],
                           g['e'],g['d'],g['x'])
    Am = 2.0*L**(m-2) + m*km(alpha,p,m)
    Bm = 2.0*L**(m-2) + m*km(L,p,m)
    Rm = alpha**m + L**m - p*q**(m-1)
    xi = g['xi']
    Cm = Bm*f*np.sqrt(2.0*alpha)*e**2/(4.0*alpha**2)
    rho = (Am/Bm)*np.sqrt(alpha)/(2.0*np.sqrt(2.0)*f)
    # psi = max_{0<=lam<=1} lam*xi - lam^2/(4(rho+lam))
    lams = np.linspace(0.0,1.0,20001)
    vals = lams*xi - lams**2/(4.0*(rho+lams))
    psi = vals.max()
    return Cm*psi, Rm, Am, Bm, rho, xi

def admissible(e, kap):
    if not (0.0 < e < 1.0/3.0): return False
    kmax = (1.0-e)/(1.0+e)      # frontier alpha<=r(q)
    kq = (1.0-3.0*e)/(6.0*e)    # q>1/3
    if not (0.0 < kap <= kmax): return False
    if not (kap < kq): return False
    g = geom(e,kap)
    if not (g['L2'] > 0): return False
    return True

if __name__ == "__main__":
    # sanity
    g = geom(0.1, 0.3)
    print("admissible(0.1,0.3):", admissible(0.1,0.3))
    print({k:round(v,5) for k,v in g.items()})
    for m in (9,11,13):
        pay,Rm,Am,Bm,rho,xi = payment(g,m)
        print(f"m={m}: R={Rm:.3e} pay={pay:.3e} ratio={Rm/pay:.4f} xi={xi:.3f}")
