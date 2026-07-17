"""Scan the Region-II scalar Huber inequality R_m <= C_m * psi(xi, rho)
outside its proven domain:
  (A) small cycles m in {3,5,...,13} on the Region-II domain q in (1/3,1/2);
  (B) Region-I densities q in (0,1/3] (one-frontier data assumed), all odd m.

Definitions from paper_region2_v2.tex (Def. huber / Prop. psi-forms).
Uses mpmath-free float scan first; refine minima with high precision.
"""
import math

def r_of_q(q):
    return (math.sqrt(q*q + 4*q) - q) / 2.0

def k_m(lam, p, m):
    # (p^{m-1} - lam^{m-1})/(p + lam)
    return (p**(m-1) - lam**(m-1)) / (p + lam)

def psi(xi, rho):
    # closed form
    xic = (2*rho + 1) / (4*(rho + 1)**2)
    if xi < xic:
        if xi < 0:
            return rho * 0.0
        vm = (1 - math.sqrt(max(0.0, 1 - 4*xi))) / 2
        return rho * vm * vm
    else:
        return xi - 1.0/(4*(1 + rho))

def margin(q, alpha, m):
    """Return (R_m, C_m*psi, relative margin (pay - R)/scale)."""
    p = 1 - q
    d = alpha - q
    e = 1 - 2*alpha
    L2 = p*q - alpha*alpha
    if L2 < 0 or d <= 0 or e <= 0:
        return None
    L = math.sqrt(L2)
    f = alpha - L
    Am = 2*L**(m-2) + m*k_m(alpha, p, m)
    Bm = 2*L**(m-2) + m*k_m(L, p, m)
    Rm = alpha**m + L**m - p*q**(m-1)
    Cm = Bm*f*math.sqrt(2*alpha)*e*e/(4*alpha*alpha)
    xi = 4*alpha*alpha*d/(e*e)
    rho = (Am/Bm)*math.sqrt(alpha)/(2*math.sqrt(2)*f)
    pay = Cm*psi(xi, rho)
    scale = max(abs(Rm), pay, p**m)
    return Rm, pay, (pay - Rm)/scale

def scan(qlo, qhi, ms, nq=400, na=400, label=""):
    worst = (1e9, None)
    fails = 0
    for m in ms:
        for i in range(1, nq+1):
            q = qlo + (qhi - qlo)*i/(nq+1)
            rq = r_of_q(q)
            if rq <= q:
                continue
            for j in range(1, na+1):
                alpha = q + (rq - q)*j/na   # include alpha = r(q) at j=na
                res = margin(q, alpha, m)
                if res is None:
                    continue
                Rm, pay, rel = res
                if Rm <= 0:
                    continue  # nothing to prove
                if pay < Rm:
                    fails += 1
                    if rel < worst[0]:
                        worst = (rel, (q, alpha, m, Rm, pay))
                else:
                    if rel < worst[0]:
                        worst = (rel, (q, alpha, m, Rm, pay))
    print(f"[{label}] fails={fails}, worst rel margin={worst[0]:.6g} at {worst[1]}")
    return fails, worst

if __name__ == "__main__":
    # (A) small m on Region II domain
    scan(1/3, 1/2, [3, 5, 7, 9, 11, 13], label="A: m<=13, q in (1/3,1/2)")
    # (B) Region I densities, moderate m
    scan(0.01, 1/3, [5, 7, 9, 11, 15, 21, 31, 41, 61, 101], nq=300, na=300,
         label="B: q<=1/3, odd m")
    # (C) sanity: proven domain m>=15, q in (1/3,1/2)
    scan(1/3, 1/2, [15, 21, 31, 61, 101, 301], nq=300, na=300,
         label="C: sanity proven domain")
