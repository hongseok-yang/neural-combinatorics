# -*- coding: utf-8 -*-
"""Emit cert11_specMoment + C11_path_integral (necklace assembly), mirroring C9."""
import sympy as sp
from collections import defaultdict
q=sp.symbols("q"); s=sp.symbols("s0:20"); MU="μ"

# path densities + Phi11 in moments
a=sp.Integer(1); h=defaultdict(lambda: sp.Integer(0)); xs={0:a}
for nn in range(1,11):
    inner=sum(c*s[p] for p,c in h.items()); a_new=sp.expand(q*a+inner)
    h_new=defaultdict(lambda: sp.Integer(0)); h_new[0]+=a
    for pwr,c in h.items(): h_new[pwr+1]+=c
    a,h=a_new,h_new; xs[nn]=a
def c11(x):
    return sp.expand(
        -10*q**10 + 55*q**9 - 165*q**8 + 330*q**7 - 462*q**6 + 451*q**5
        + 11*q**4*x[2] - 275*q**4 - 110*q**3*x[2] + 44*q**3*x[3] - 11*q**3*x[4] + 88*q**3
        + 66*q**2*x[2]**2 - 33*q**2*x[2]*x[3] + 165*q**2*x[2] - 110*q**2*x[3] + 66*q**2*x[4]
        - 33*q**2*x[5] + 11*q**2*x[6] - 11*q**2 - 11*q*x[2]**3 - 110*q*x[2]**2 + 132*q*x[2]*x[3]
        - 66*q*x[2]*x[4] + 22*q*x[2]*x[5] - 77*q*x[2] - 33*q*x[3]**2 + 22*q*x[3]*x[4] + 66*q*x[3]
        - 55*q*x[4] + 44*q*x[5] - 33*q*x[6] + 22*q*x[7] - 11*q*x[8] + 10*x[10] + 22*x[2]**3
        - 33*x[2]**2*x[3] + 11*x[2]**2*x[4] + 33*x[2]**2 + 11*x[2]*x[3]**2 - 55*x[2]*x[3]
        + 44*x[2]*x[4] - 33*x[2]*x[5] + 22*x[2]*x[6] - 11*x[2]*x[7] + 11*x[2] + 22*x[3]**2
        - 33*x[3]*x[4] + 22*x[3]*x[5] - 11*x[3]*x[6] - 11*x[3] + 11*x[4]**2 - 11*x[4]*x[5]
        + 11*x[4] - 11*x[5] + 11*x[6] - 11*x[7] + 11*x[8] - 11*x[9])
Phi=sp.expand(c11(xs))

def sm(i): return f"specMoment U {MU} {i}"
def term_lean(monom, coeff):
    c=sp.Rational(coeff);
    parts=[]
    # q power from coeff? No: monom is over s; coeff is q-poly
    # We'll format coeff*q-structure separately: here monom is s-exponents, coeff includes q
    return None

def poly_lean(expr):
    # expr polynomial in q and s0..s8 -> Lean string
    P=sp.Poly(sp.expand(expr), q, *s[:9])
    terms=[]
    for monom,coeff in sorted(P.terms(), key=lambda kv:(-sum(kv[0]), kv[0])):
        c=int(coeff)
        fac=[]
        qp=monom[0]
        if qp==1: fac.append("q")
        elif qp>1: fac.append(f"q ^ {qp}")
        for si in range(9):
            e=monom[1+si]
            if e==1: fac.append(sm(si))
            elif e>1: fac.append(f"{sm(si)} ^ {e}")
        body=" * ".join(fac) if fac else "1"
        if abs(c)==1 and fac: t=("" if c==1 else "-")+body
        else: t=f"{c} * {body}" if fac else f"{c}"
        terms.append(t)
    out=terms[0]
    for t in terms[1:]:
        out += (" - "+t[1:]) if t.startswith("-") else (" + "+t)
    return out

Phi_lean=poly_lean(Phi)

# extract the conclusion of a generated cert lemma (the final combiner lemma)
def extract_concl(fn, lemname):
    import re
    txt=open(fn,encoding="utf-8").read()
    # find 'lemma {lemname} (' then capture up to ':= by'
    i=txt.index(f"lemma {lemname} (")
    seg=txt[i:]
    j=seg.index(":= by")
    head=seg[:j]
    # conclusion after the ':' following the signature line: find '0 ≤'
    k=head.rindex("0 ≤")
    return head[k+len("0 ≤"):].strip()

L1=extract_concl("cert11_L.txt","cert11_L1")
L2=extract_concl("cert11_L2.txt","cert11_L2")
L3=extract_concl("cert11_L3.txt","cert11_L3")
# L4, L5 hand-written forms:
L4="150*q^2*specMoment U μ 0^4 - 165*q*specMoment U μ 0^4 + 200*q*specMoment U μ 0^3*specMoment U μ 1 + 55*specMoment U μ 0^4 - 110*specMoment U μ 0^3*specMoment U μ 1 + 40*specMoment U μ 0^3*specMoment U μ 2 + 60*specMoment U μ 0^2*specMoment U μ 1^2"
L5="10 * specMoment U μ 0^5"

out=[]
out.append("set_option maxHeartbeats 1600000 in")
out.append("lemma cert11_specMoment (hU : IsGraphon U μ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/3) :")
out.append(f"    0 ≤ {Phi_lean} := by")
out.append("  have h1 := cert11_L1 hU q hq0 hq1")
out.append("  have h2 := cert11_L2 hU q hq0 hq1")
out.append("  have h3 := cert11_L3 hU q hq0 hq1")
out.append("  have h4 := cert11_L4 hU q hq0 hq1")
out.append("  have h5 := cert11_L5 hU")
out.append(f"  have key : {Phi_lean} = ({L1}) + ({L2}) + ({L3}) + ({L4}) + ({L5}) := by ring")
out.append("  rw [key]; linarith [h1, h2, h3, h4, h5]")
out.append("")
# C11_path_integral mirroring C9
out.append("set_option maxHeartbeats 1600000 in")
out.append("set_option maxRecDepth 8000 in")
out.append("theorem C11_path_integral (hU : IsGraphon U μ) (hq : edgeDensity U μ ≤ 1/3) :")
out.append("    trace μ (compPow μ (compl U) 10) ≥ (1 - edgeDensity U μ) ^ 11 - (1 - edgeDensity U μ) * edgeDensity U μ ^ 10 := by")
out.append("  have hq0 : 0 ≤ edgeDensity U μ := edgeDensity_nonneg hU")
out.append("  have hx1 : pathDensity U μ 1 = edgeDensity U μ := pathDensity_one hU")
out.append("  have hx2 := pathDensity_two hU")
out.append("  have hx3 := pathDensity_three hU")
out.append("  have hx4 := pathDensity_four hU")
out.append("  have hx5 := pathDensity_five hU")
out.append("  have hx6 := pathDensity_six hU")
out.append("  have hx7 := pathDensity_seven hU")
out.append("  have hx8 := pathDensity_eight hU")
out.append("  have hx9 := pathDensity_nine hU")
out.append("  have hx10 := pathDensity_ten hU")
out.append("  have hed : trace μ (compPow μ U 10) ≤ pathDensity U μ 10 := edge_deletion_general hU 9")
out.append("  have hcert := cert11_specMoment hU (edgeDensity U μ) hq0 hq")
# Phi with edgeDensity U μ in place of q
Phi_ed=Phi_lean.replace(" q ", " edgeDensity U μ ").replace("(q ", "(edgeDensity U μ ")
# safer: rebuild with explicit substitution string for q
def poly_lean_ed(expr):
    P=sp.Poly(sp.expand(expr), q, *s[:9]); terms=[]
    for monom,coeff in sorted(P.terms(), key=lambda kv:(-sum(kv[0]), kv[0])):
        c=int(coeff); fac=[]; qp=monom[0]
        if qp==1: fac.append("(edgeDensity U μ)")
        elif qp>1: fac.append(f"(edgeDensity U μ) ^ {qp}")
        for si in range(9):
            e=monom[1+si]
            if e==1: fac.append(sm(si))
            elif e>1: fac.append(f"{sm(si)} ^ {e}")
        body=" * ".join(fac) if fac else "1"
        if abs(c)==1 and fac: t=("" if c==1 else "-")+body
        else: t=f"{c} * {body}" if fac else f"{c}"
        terms.append(t)
    o=terms[0]
    for t in terms[1:]: o+=(" - "+t[1:]) if t.startswith("-") else (" + "+t)
    return o
Phi_ed=poly_lean_ed(Phi)
out.append("  have key : trace μ (compPow μ (compl U) 10)")
out.append("      = ((1 - edgeDensity U μ) ^ 11 - (1 - edgeDensity U μ) * edgeDensity U μ ^ 10)")
out.append(f"        + ({Phi_ed})")
out.append("        + (pathDensity U μ 10 - trace μ (compPow μ U 10)) := by")
out.append("    rw [complTrace_necklace hU 9]")
out.append("    simp only [pairing_pathIter_complIter_closed hU, complMean_succ hU, complMean_zero, pathDensity_zero, pairing_pathIter_zero,")
out.append("      Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,")
out.append("      Nat.reduceSub, Nat.reduceAdd, mul_one, one_mul, mul_neg, neg_neg, zero_add, add_zero]")
out.append("    rw [hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9, hx10]")
out.append("    ring")
out.append("  rw [key]; linarith [hcert, hed]")
open("c11_assembly.txt","w",encoding="utf-8").write("\n".join(out))
print("wrote c11_assembly.txt")
