import sympy as sp

q, s0, s1, s2, s3, s4 = sp.symbols('q s0 s1 s2 s3 s4')

# xden_j (Lemma 2.4) in moments
xden = {
 1: q,
 2: q**2 + s0,
 3: q**3 + 2*q*s0 + s1,
 4: q**4 + 3*q**2*s0 + 2*q*s1 + s0**2 + s2,
 5: q**5 + 4*q**3*s0 + 3*q**2*s1 + 3*q*s0**2 + 2*q*s2 + 2*s0*s1 + s3,
 6: (q**6 + 5*q**4*s0 + 4*q**3*s1 + 6*q**2*s0**2 + 3*q**2*s2 + 6*q*s0*s1
     + 2*q*s3 + s0**3 + 2*s0*s2 + s1**2 + s4),
}

# recursions for m[j,k] = <T^j 1, B^k 1> and pcomp[k] = <1, B^k 1>
from functools import lru_cache
@lru_cache(maxsize=None)
def pcomp(k):
    if k == 0: return sp.Integer(1)
    return pcomp(k-1) - m(1, k-1)
@lru_cache(maxsize=None)
def m(j, k):
    if k == 0: return xden[j]
    return pcomp(k-1)*xden[j] - m(j+1, k-1)

# E7' = ccomp7 with c7 -> x6 (the bound side)
E7 = pcomp(6) - m(1,5) + m(2,4) - m(3,3) + m(4,2) - m(5,1)
P = 1 - q
g7 = P**7 - P*(1-P)**6
Phi7 = (6*s4 + (12*q-7)*s3 + (18*q**2-21*q+7)*s2 + (24*q**3-42*q**2+28*q-7)*s1
        + (30*q**4-70*q**3+70*q**2-35*q+7)*s0 + 12*s0*s2 + (36*q-21)*s0*s1
        + (36*q**2-42*q+14)*s0**2 + 6*s0**3 + 6*s1**2)
print("E7' - g7 == Phi7 :", sp.expand(E7 - g7 - Phi7) == 0)
