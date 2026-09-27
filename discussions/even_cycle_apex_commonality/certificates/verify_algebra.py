#!/usr/bin/env python3
"""Exact auxiliary checks for the universal even-cycle apex proof.

Only Python's standard library is used. The graph-polynomial identities and
positive definiteness are checked separately by verify_six_vertex.py.
"""
from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
import json
import verify_six_vertex as sos

if not __debug__:
    raise SystemExit('Run without -O: this program uses assertion checks.')

# Sparse polynomial arithmetic, with five indeterminates (j, R, p, m, tau).
ZERO=(0,0,0,0,0)
def add(*terms):
    out={}
    for a,P in terms:
        for e,c in P.items():out[e]=out.get(e,F(0))+a*c
    return {e:c for e,c in out.items() if c}
def mul(A,B):
    out={}
    for e,a in A.items():
        for f,b in B.items():
            g=tuple(x+y for x,y in zip(e,f));out[g]=out.get(g,F(0))+a*b
    return {e:c for e,c in out.items() if c}
def var(i):
    e=list(ZERO);e[i]=1;return {tuple(e):F(1)}
ONE={ZERO:F(1)}
j,R,p,m,tau=[var(i) for i in range(5)]
mu=add((3,m),(-1,tau))
star=add((2,j),(-1,R),(-4,p),(-1,ONE))
# The j_sigma and j_P terms cancel on both sides. Verify the residuals.
Fminus=add((1,mul(add((3,ONE),(2,mu)),j)),
           (-1,mul(add((3,ONE),(1,mu)),add((1,R),(4,m),(4,p)))))
G_without_odd=add((3,j),(-3,R),(-13,m),(-1,tau),
                  (-12,mul(m,m)),(4,mul(m,tau)),(-12,p))
assert add((1,Fminus),(-1,G_without_odd),(-4,m),(-1,mul(mu,star)))=={}
Fplus=add((1,mul(add((6,ONE),(-2,mu)),j)),
          (-1,mul(add((6,ONE),(-1,mu)),add((1,R),(4,m),(4,p)))))
H_without_odd=add((6,j),(-6,R),(-19,m),(-23,tau),
                  (12,mul(m,m)),(-4,mul(m,tau)),(-24,p))
assert add((1,Fplus),(-1,H_without_odd),(-24,tau),(8,m),(1,mul(mu,star)))=={}
print('PASS: both weighted-comparison algebra identities are exact.')

# The shifted scalar polynomial in the proof of R_4^(3/2) >= R_4 + 4br.
co=[-4,15,-12,-4,0,27]
shift=[sum(F(co[i])*comb(i,k)*F(1,2)**(i-k) for i in range(k,6)) for k in range(6)]
assert shift==[F(27,32),F(135,16),F(63,4),F(127,2),F(135,2),F(27)]
assert all(x>0 for x in shift)
assert sorted(set(a+b+c-a*b*c for a,b,c in product((-1,1),repeat=3)))==[-2,2]
for s in (1,2,3):assert (3*s+1)-(s+2)==2*s-1
print('PASS: majority endpoints, scalar shift, and all normalization powers are exact.')

def mm(A,B):
    return [[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def power(A,n):
    I=[[F(int(i==j)) for j in range(len(A))] for i in range(len(A))]
    while n:
        if n&1:I=mm(I,A)
        A=mm(A,A);n//=2
    return I
def trace(A):return sum(A[i][i] for i in range(len(A)))
def scalars(U,pi):
    n=len(pi);f=[sum(U[i][j]*pi[j] for j in range(n)) for i in range(n)]
    m=sum(pi[i]*f[i] for i in range(n));b=sum(pi[i]*f[i]**2 for i in range(n))
    T=[[U[i][j]*pi[j] for j in range(n)] for i in range(n)]
    tau=trace(power(T,3));c=trace(power(T,4))
    p=sum(pi[i]*f[i]*U[i][j]*pi[j]*f[j] for i in range(n) for j in range(n))
    R=1+2*m*m+4*b+c
    rr=[]
    for sig in (1,-1):
        S=[[1+sig*U[i][j] for j in range(n)] for i in range(n)]
        rr.append(trace(power([[S[i][j]*pi[j] for j in range(n)] for i in range(n)],4)))
    assert rr==[R+4*(m+p),R-4*(m+p)]
    return m,b,c,tau,p,R,rr

def conditional(U,pi,s):
    n=len(pi);out=[]
    for roots in product(range(n),repeat=s):
        prob=F(1)
        for z in roots:prob*=pi[z]
        if s==3:
            x,y,z=roots;P=U[x][y]+U[x][z]+U[y][z]-U[x][y]*U[x][z]*U[y][z]
        else:P=F(0)
        for sig in (1,-1):
            S=[[1+sig*U[i][j] for j in range(n)] for i in range(n)]
            h=[]
            for x in range(n):
                hx=F(1)
                for z in roots:hx*=S[z][x]
                h.append(hx)
            D=sum(pi[i]*h[i] for i in range(n))
            Sh=[sum(S[i][j]*h[j]*pi[j] for j in range(n)) for i in range(n)]
            N=sum(pi[i]*h[i]*Sh[i] for i in range(n))
            Pi=sum(pi[i]*h[i]*Sh[i]**2 for i in range(n))
            B4=Pi**2/D**2 if D else F(0)
            oldQ=N/D if D else F(0)
            variance=sum(pi[i]*h[i]*(Sh[i]-oldQ)**2 for i in range(n))/D if D else F(0)
            assert (Pi/D if D else F(0))-oldQ**2==variance>=0
            assert B4-(2*Pi-D*D)==(Pi/D-D)**2 if D else Pi==0
            out.append((prob/2,sig,P,D,Pi,B4))
    assert sum(x[0] for x in out)==1
    return out

def evaluate_sos(U,pi,certificate):
    data=json.loads((Path(__file__).parent/certificate).read_text());den=int(data['denominator'])
    total=F(0);n=len(pi)
    for (r,t,k,pats),Q in zip(sos.blocks(),data['matrices']):
        Q=[[int(q) for q in row] for row in Q]
        redges=list(__import__('itertools').combinations(range(r),2))
        for roots in product(range(n),repeat=r):
            pr=F(1)
            for z in roots:pr*=pi[z]
            for idx,(i,j) in enumerate(redges):
                sign=1 if (t>>idx)&1 else -1
                pr*=F(1,2)*(1+sign*U[roots[i]][roots[j]])
            if not pr:continue
            values=[]
            for pat in pats:
                val=F(0)
                for new in product(range(n),repeat=k):
                    z=roots+new;v=F(1)
                    for x in new:v*=pi[x]
                    for i,j in pat:v*=U[z[i]][z[j]]
                    val+=v
                values.append(val)
            value=sum(Q[i][j]*values[i]*values[j] for i in range(len(values)) for j in range(len(values)))/den
            assert value>=0
            total+=pr*value
    return total

cases=[
    ('case 1',[[F(0),F(1,4)],[F(1,4),F(-1,2)]],[F(1,2),F(1,2)]),
    ('case 2',[[F(1,4),F(1,4)],[F(1,4),F(1,4)]],[F(1,3),F(2,3)]),
    ('case 3',[[F(17,32),F(-15,32)],[F(-15,32),F(17,32)]],[F(1,2),F(1,2)]),
]
for expected,U,pi in cases:
    m,b,c,tau,p,R,rr=scalars(U,pi);mu=3*m-tau
    assert m>=0
    law=conditional(U,pi,3)
    J=sum(pr*(2*Pi-D*D) for pr,sg,P,D,Pi,v in law)
    Js=sum(pr*sg*(2*Pi-D*D) for pr,sg,P,D,Pi,v in law)
    JP=sum(pr*P*(2*Pi-D*D) for pr,sg,P,D,Pi,v in law)
    G=3*J-3*R+Js-JP-13*m-tau-12*m*m+4*m*tau-12*p
    H=6*J-6*R+Js+JP-19*m-23*tau+12*m*m-4*m*tau-24*p
    assert G>=0 and H>=0
    assert sum(pr*P for pr,sg,P,D,Pi,v in law)==mu
    if m+p<=0:
        chosen='case 1';weights=[F(1) for _ in law]
    elif mu>=0:
        chosen='case 2';weights=[1+(sg-P+mu)/(3+mu) for pr,sg,P,D,Pi,v in law]
    else:
        chosen='case 3';weights=[1+(sg+P-mu)/(6-mu) for pr,sg,P,D,Pi,v in law]
    assert chosen==expected and all(0<=w<=2 for w in weights)
    assert sum(pr*w for (pr,*rest),w in zip(law,weights))==1
    assert sum(row[0]*w*row[-1] for row,w in zip(law,weights))>=max(rr)
    assert G==evaluate_sos(U,pi,'negative_majority_sos.json')
    assert H==evaluate_sos(U,pi,'positive_majority_sos.json')
    for s,certificate in [(2,'mean_two_sos.json'),(3,'mean_three_sos.json')]:
        law_s=conditional(U,pi,s)
        difference=sum(pr*(Pi-D*D) for pr,sg,P,D,Pi,v in law_s)
        assert difference>=0 and difference==evaluate_sos(U,pi,certificate)
    print('PASS:',expected,'has exact conditional, rooted-square, and weighted-moment agreement.')
print('PASS: all auxiliary checks complete. Finite host checks are consistency tests, not a covering argument.')
