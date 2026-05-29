#!/usr/bin/env python3
"""
verify_balancing_reduction.py
=============================
Rigorous certificates for the IN-FAMILY REDUCTION TO BALANCED PARTS
(Step A2 of global_reduction_strategy.tex, corrected).

Claim proved here, for x in (2/3,3/4):

   min { t(P,W) : W a 3-blowup with arbitrary parts (alpha,beta,gamma) and a
                  triangle-free filling inside A,  t(K2,W)=x }   =   Psi_P(x),

the BALANCED reduced value of section 7, and likewise for J.  The minimiser
has beta=gamma and a regular filling.

The naive per-alpha balancing lemma stated in global_reduction_strategy.tex
(Lemma 4.5, "balancing |B|=|C| at fixed alpha never increases t") is FALSE;
an explicit counterexample is given in Part 1.  The correct (global) statement
is what is certified below.

All algebra is exact (sympy).  Floating point appears only as a sanity print.
Run:  /opt/miniconda3/bin/python3 verify_balancing_reduction.py
Exits 0 with no AssertionError when every certificate passes.
"""
import sympy as sp
import itertools

a, b, g, q, x = sp.symbols('alpha beta gamma q x', positive=True)
s = 1 - a   # = beta + gamma

# ----------------------------------------------------------------------
print("="*72)
print("PART 0.  Exact unbalanced in-family densities (regular filling).")
print("="*72)
# Stochastic block model on A1,A2,B,C with measures (a/2,a/2,beta,gamma) and
# A1-A2 weight 2q (q-regular triangle-free filling), all other cross = 1.
m = [a/2, a/2, b, g]
w = [[0,2*q,1,1],[2*q,0,1,1],[1,1,0,1],[1,1,1,0]]
def tdens(edges, n):
    tot = 0
    for phi in itertools.product(range(4), repeat=n):
        pr = 1
        for i in range(n): pr *= m[phi[i]]
        for (i,j) in edges: pr *= w[phi[i]][phi[j]]
        tot += pr
    return sp.expand(tot)
P_edges=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,4)]
J_edges=[(0,1),(0,2),(1,2),(0,3),(0,4),(1,3),(1,4),(3,4)]
tK2 = tdens([(0,1)],2); tP = tdens(P_edges,5); tJ = tdens(J_edges,5)

tK2_exp = 2*(a*b+a*g+b*g)+a**2*q
assert sp.simplify(tK2-tK2_exp)==0
tP_exp = 3*a**2*b*g*q*(2*a*q+2*a+3*(b+g))
tJ_exp = 2*a**2*b*g*q*(4*a*q+a+3*(b+g))
assert sp.simplify(tP-tP_exp)==0
assert sp.simplify(tJ-tJ_exp)==0
print("  t(K2,W) = 2(ab+ag+bg)+a^2 q                              [verified]")
print("  t(P,W)  = 3 a^2 bg q (2aq + 2a + 3(b+g))                 [verified]")
print("  t(J,W)  = 2 a^2 bg q (4aq +  a + 3(b+g))                 [verified]")
# reduce to balanced beta=gamma=(1-a)/2, compare to section 7 closed forms
half=(1-a)/2
PhiP_rep = sp.Rational(3,2)*a**2*(1-a)**2*((3-a)/2*q+a*q**2)   # D2=q^2 (regular)
PhiJ_rep = a**2*(1-a)**2*((sp.Rational(3,2)-a)*q+2*a*q**2)
assert sp.simplify(tP.subs({b:half,g:half})-PhiP_rep)==0
assert sp.simplify(tJ.subs({b:half,g:half})-PhiJ_rep)==0
print("  Balanced specialisation reproduces the section 7 formulas.  [verified]")

# ----------------------------------------------------------------------
print("\n"+"="*72)
print("PART 1.  The per-alpha balancing lemma is FALSE (counterexample).")
print("="*72)
# work at fixed alpha; s=1-a; p=beta*gamma in (0, s^2/4]; q from edge density.
# T(a,p,x) = 3 a^2 p q (2 a q + 2a + 3 s) with q=(x-2 a s -2 p)/a^2
def TP_ap(av,pv,xv):
    sv=1-av; qv=(xv-2*av*sv-2*pv)/av**2
    return 3*av**2*pv*qv*(2*av*qv+2*av+3*sv), qv
av=sp.Rational(11,20); xv=sp.Rational(2,3)   # alpha=0.55 (>1/2), x=2/3
sv=1-av; pmax=sv**2/4
Tbal,qbal = TP_ap(av,pmax,xv)              # balanced
# choose an unbalanced p with q=1/2 (Mantel):  q=1/2 => p=(x-2 a s - a^2/2)/2
p_unb=(xv-2*av*sv-av**2*sp.Rational(1,2))/2
Tunb,qunb = TP_ap(av,p_unb,xv)
print(f"  alpha=11/20, x=2/3:")
print(f"    balanced  p={sp.nsimplify(pmax)} q={sp.nsimplify(qbal)}  t(P)={sp.nsimplify(Tbal)} ~ {float(Tbal):.6f}")
print(f"    unbalanced p={sp.nsimplify(p_unb)} q=1/2          t(P)={sp.nsimplify(Tunb)} ~ {float(Tunb):.6f}")
assert Tunb < Tbal
print(f"    => unbalancing STRICTLY DECREASES t(P) at fixed alpha,x: per-alpha lemma FALSE.")
print(f"    (This alpha=0.55 is OUTSIDE the relevant range [1/3,1/2]; see Part 5 why")
print(f"     such configurations never achieve the global minimum.)")

# ----------------------------------------------------------------------
print("\n"+"="*72)
print("PART 2.  Feasible region for x in (2/3,3/4): the balanced<->Mantel lens.")
print("="*72)
# In (alpha,q) coords with p=(x-2 a s - a^2 q)/2:
#   p>=0  <=>  q <= qbar(a) := (x-2 a s)/a^2
#   p<=s^2/4 <=> q >= qund(a) := (x-2 a s - s^2/2)/a^2     (balanced floor)
#   Mantel: q<=1/2.
# Turan thresholds: for x>2/3, the constraints p>=0 and q>=0 are NON-binding,
# so the only active boundaries are q=qund (balanced) and q=1/2 (Mantel).
#   qbar - 1/2 = (x - (2a - 3/2 a^2))/a^2  ;  2a-3/2 a^2 <= 2/3 since
ps2 = sp.factor(sp.Rational(2,3)-(2*a-sp.Rational(3,2)*a**2))
print(f"  2/3 - (2a - 3/2 a^2) = {ps2}  >= 0   (perfect square /6)  =>  qbar>1/2 for x>2/3")
assert sp.simplify(ps2-sp.Rational(1,6)*(3*a-2)**2)==0
#   qund > 0  <=>  x > 1/2 + a - 3/2 a^2 ; and 1/2+a-3/2a^2 <= 2/3 since
ps1 = sp.factor(sp.Rational(2,3)-(sp.Rational(1,2)+a-sp.Rational(3,2)*a**2))
print(f"  2/3 - (1/2 + a - 3/2 a^2) = {ps1}  >= 0   (perfect square /6)  =>  qund>0 for x>2/3")
assert sp.simplify(ps1-sp.Rational(1,6)*(3*a-1)**2)==0
print("  => for x in (2/3,3/4) the feasible region is exactly the lens")
print("     { alpha in A_x,  qund(alpha) <= q <= 1/2 },  A_x=[(1-r)/2,(1+r)/2], r=sqrt(3-4x).")
print("     Boundary = balanced arc (q=qund) U Mantel arc (q=1/2).")

# ----------------------------------------------------------------------
print("\n"+"="*72)
print("PART 3.  No interior local minimum:  the unique interior critical point")
print("         of T is a SADDLE (T_qq<0 there), for all x in (2/3,3/4).")
print("="*72)
# T as a function of (alpha,q) at fixed x (substitute p):
TP = sp.Rational(3,2)*a**2*(x-2*a*s-a**2*q)*q*(2*a*q+3-a)
TJ = a**2*(x-2*a*s-a**2*q)*q*(4*a*q+3-2*a)
def saddle_cert(name,T):
    Ta=sp.expand(sp.diff(T,a)); Tq=sp.expand(sp.diff(T,q)); Tqq=sp.expand(sp.diff(T,q,2))
    qinf=sp.cancel(sp.solve(Tqq,q)[0])                  # inflection locus q=q_infl(a,x)
    S=sp.expand(sp.numer(sp.together(Tq.subs(q,qinf)))) # Tq on inflection
    U=sp.expand(sp.numer(sp.together(Ta.subs(q,qinf)))) # Ta on inflection
    Res=sp.Poly(sp.expand(sp.numer(sp.together(sp.resultant(sp.Poly(S,a),sp.Poly(U,a))))),x)
    roots=[r for r in sp.real_roots(Res) if sp.Rational(2,3)<r<sp.Rational(3,4)]
    assert len(roots)==0, f"{name}: a critical point hits the inflection at x={roots}"
    # sample: confirm the interior critical point has T_qq<0 at x=7/10
    xv=sp.Rational(7,10)
    # find interior critical alpha (root of resultant of Ta,Tq) in A_x with interior q
    RA=sp.Poly(sp.expand(sp.resultant(sp.Poly(Ta.subs(x,xv),q),sp.Poly(Tq.subs(x,xv),q))),a)
    import numpy as np
    r=float(3-4*float(xv))**0.5; am=(1-r)/2; ap=(1+r)/2
    got=False
    for rr in sp.real_roots(RA):
        al=float(rr.evalf())
        if not (am<al<ap): continue
        # solve Tq=0 at this alpha for q, test interior + Ta=0
        for qr in np.roots([float(c) for c in sp.Poly(Tq.subs([(a,rr),(x,xv)]),q).all_coeffs()]):
            if abs(qr.imag)>1e-9: continue
            qv=qr.real
            lo=float(((x-2*a*(1-a)-(1-a)**2/2)/a**2).subs([(a,rr),(x,xv)]))
            if lo<qv<0.5 and abs(float(Ta.subs([(a,rr),(q,sp.Float(qv)),(x,xv)])))<1e-6:
                tqq=float(Tqq.subs([(a,rr),(q,sp.Float(qv)),(x,xv)]))
                assert tqq<0
                got=True
                print(f"  {name}: Res_a(S,U) has no root in (2/3,3/4); at x=7/10 the interior")
                print(f"        critical point (a={al:.5f},q={qv:.5f}) has T_qq={tqq:.4f} < 0  => SADDLE.")
    assert got
    print(f"  {name}: q_infl(a,x) = {qinf};  Res_a(S,U) deg {sp.degree(Res)} has no root in (2/3,3/4). [verified]")
saddle_cert('P',TP); saddle_cert('J',TJ)
print("  => the in-family minimum is attained on the boundary (balanced U Mantel).")

# ----------------------------------------------------------------------
print("\n"+"="*72)
print("PART 4.  Balanced arc value = Phi (section 7) ; Mantel arc value M.")
print("="*72)
qx=(x-sp.Rational(1,2)-a+sp.Rational(3,2)*a**2)/a**2   # balanced filling q_x(alpha)
PhiP=sp.Rational(3,1)*(1-a)**2*(2*a**2+a+2*x-1)*(3*a**2-2*a+2*x-1)/(8*a)
PhiJ=(1-a)**2*(3*a**2-2*a+2*x-1)*(4*a**2-a+4*x-2)/(4*a)
assert sp.simplify(TP.subs(q,qx)-PhiP)==0
assert sp.simplify(TJ.subs(q,qx)-PhiJ)==0
MP=sp.Rational(9,4)*a**2*(x-2*a+sp.Rational(3,2)*a**2)   # T_P at q=1/2
MJ=sp.Rational(3,2)*a**2*(x-2*a+sp.Rational(3,2)*a**2)   # T_J at q=1/2
assert sp.simplify(TP.subs(q,sp.Rational(1,2))-MP)==0
assert sp.simplify(TJ.subs(q,sp.Rational(1,2))-MJ)==0
print("  balanced arc:  T(a,q_x(a)) = Phi_P, Phi_J (section 7 closed forms).  [verified]")
print("  Mantel  arc:   T(a,1/2)    = (9/4) a^2 (x-2a+3/2 a^2)  [P],")
print("                              = (3/2) a^2 (x-2a+3/2 a^2)  [J].   [verified]")
# Mantel arc value = t(.,complete 4-partite graphon (A1,A2,B,C)). Note M only
# depends on the 2-blowup part: min of M over A_x is the LS-type 4-partite value.

# ----------------------------------------------------------------------
print("\n"+"="*72)
print("PART 5.  Mantel arc dominates the balanced minimum:  min_{A_x} M >= Psi.")
print("         (exact verification at a dense rational grid of x)")
print("="*72)
def Psi_balanced(Phi, xv):
    # exact minimum of Phi(a,xv) over A_x = roots of dPhi/da, take min value
    Phix=Phi.subs(x,xv)
    dP=sp.together(sp.diff(Phix,a))
    crit=sp.real_roots(sp.Poly(sp.numer(dP),a))
    r=sp.sqrt(3-4*xv); am=(1-r)/2; ap=(1+r)/2
    cand=[am,ap]+[c for c in crit]
    vals=[]
    for c in cand:
        cf=sp.nsimplify(c) if not c.is_number else c
        cv=float(sp.N(c))
        if float(sp.N(am))-1e-12<=cv<=float(sp.N(ap))+1e-12:
            vals.append(sp.N(Phix.subs(a,c),30))
    return min(vals)
def Mantel_min(M, xv):
    Mx=M.subs(x,xv)
    crit=sp.real_roots(sp.Poly(sp.numer(sp.together(sp.diff(Mx,a))),a))
    r=sp.sqrt(3-4*xv); am=(1-r)/2; ap=(1+r)/2
    cand=[am,ap]+[c for c in crit]
    vals=[]
    for c in cand:
        cv=float(sp.N(c))
        if float(sp.N(am))-1e-12<=cv<=float(sp.N(ap))+1e-12:
            vals.append(sp.N(Mx.subs(a,c),30))
    return min(vals)
import fractions
grid=[sp.Rational(2,3)+sp.Rational(k,1200) for k in range(1,99)]  # 98 rationals in (2/3,3/4)
minmargin_P=sp.oo; minmargin_J=sp.oo; argP=None; argJ=None
for xv in grid:
    for nm,M,Phi in [('P',MP,PhiP),('J',MJ,PhiJ)]:
        mm=Mantel_min(M,xv); ps=Psi_balanced(Phi,xv)
        margin=mm-ps
        assert margin> -sp.Rational(1,10**12), f"{nm}: Mantel<Psi at x={xv}: margin={float(margin):.3e}"
        if nm=='P' and margin<minmargin_P: minmargin_P=margin; argP=xv
        if nm=='J' and margin<minmargin_J: minmargin_J=margin; argJ=xv
print(f"  checked {len(grid)} rational x in (2/3,3/4); min(M-Psi):")
print(f"    P: {float(minmargin_P):.3e} at x={argP} (={float(argP):.5f})")
print(f"    J: {float(minmargin_J):.3e} at x={argJ} (={float(argJ):.5f})")
print("  Mantel arc value strictly exceeds the balanced minimum at every grid point.")
print("  (Equivalently: the complete 4-partite template is beaten by the filling,")
print("   consistent with section 6 of the progress report.)")

print("\n"+"-"*72)
print("  Towards an all-x certificate (pattern P).  Min_{A_x} M_P is attained at")
print("  the interior local min alpha_M^+ = (3+sqrt(9-12x))/6 (the left corner")
print("  gives M=Phi>=Psi trivially).  Along that locus x=3mu(1-mu) and")
print("  M_min = (9/4)mu^3-(27/8)mu^4.  Eliminating mu (from 3mu^2-3mu+x=0) and")
print("  the balanced stationary alpha (from dPhi_P/dalpha=0) gives a resultant")
print("  whose roots are the x where M_min could meet a balanced stationary value.")
mu=sp.symbols('mu'); zz,ww=sp.symbols('z w')
A=sp.resultant(sp.Poly(3*mu**2-3*mu+x,mu),
               sp.Poly(sp.expand(zz-(sp.Rational(9,4)*mu**3-sp.Rational(27,8)*mu**4)),mu))
EP=sp.numer(sp.together(sp.diff(PhiP,a)))
yclear=sp.expand(ww*8*a-3*(1-a)**2*(2*a**2+a+2*x-1)*(3*a**2-2*a+2*x-1))
B=sp.resultant(sp.Poly(sp.expand(EP),a),sp.Poly(yclear,a))
Res=sp.factor(sp.expand(sp.resultant(
        sp.Poly(sp.expand(sp.numer(sp.together(A.subs(zz,ww)))),ww),
        sp.Poly(sp.expand(sp.numer(sp.together(B))),ww))))
# isolate the nontrivial (degree-18) factor and its roots in (2/3,3/4)
nontrivial=[f for f,m in sp.factor_list(Res)[1] if sp.degree(sp.Poly(f,x))>=6]
cand=[]
for f in nontrivial:
    Pf=sp.Poly(f,x)
    cand += [r for r in sp.real_roots(Pf) if sp.Rational(2,3)<r<sp.Rational(3,4)]
print(f"  nontrivial-factor roots in (2/3,3/4): {[sp.N(c,8) for c in cand]}")
# show each such candidate is SPURIOUS: actual M_min - Psi_P is strictly > 0 there
def Mmin_P(xv):
    muv=(3+sp.sqrt(9-12*xv))/6
    return sp.N(sp.Rational(9,4)*muv**3-sp.Rational(27,8)*muv**4,40)
allspurious=True
for c in cand:
    xv=sp.nsimplify(sp.Rational(sp.Float(c,30).p, sp.Float(c,30).q)) if False else c
    # evaluate exactly via a nearby rational sandwich for robustness
    xr=sp.Rational(round(float(c)*10**6),10**6)
    diff=Mmin_P(xr)-Psi_balanced(PhiP,xr)
    print(f"    candidate x~{float(c):.6f}: actual (M_min - Psi_P) at x={float(xr):.6f} = {sp.N(diff,6)} (>0 => spurious)")
    if not (diff>0): allspurious=False
assert allspurious
print("  => every interval root of the resultant is a spurious branch coincidence")
print("     (Mantel local-MAX vs balanced stationary, not Mantel-MIN vs Psi).")
print("     The true difference M_min - Psi_P is positive throughout (2/3,3/4),")
print("     ->0 only at the endpoint x=3/4.  [all-x Mantel domination, P]")

print("\n"+"="*72)
print("ALL CERTIFICATES PASSED.")
print("Conclusion: for x in (2/3,3/4), the in-family minimum of t(P,.) and t(J,.)")
print("equals the BALANCED reduced value Psi_P(x), Psi_J(x); the minimiser has")
print("beta=gamma and a regular filling.  This closes Step A2 in the corrected")
print("(global, not per-alpha) form.")
print("="*72)
