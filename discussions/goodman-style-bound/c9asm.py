# -*- coding: utf-8 -*-
import sympy as sp
from collections import defaultdict
q=sp.symbols('q'); s=sp.symbols('s0:7')
a=sp.Integer(1); h=defaultdict(lambda: sp.Integer(0)); xs={0:a}
for n in range(1,9):
    inner=sum(c*s[p] for p,c in h.items()); a=sp.expand(q*a+inner)
    h2=defaultdict(lambda: sp.Integer(0)); h2[0]+=xs[n-1]
    for p,c in h.items(): h2[p+1]+=c
    h=h2; xs[n]=a
Phi=sp.expand( 8*xs[8]-9*xs[7]+9*xs[6]-9*xs[5]+9*xs[4]-9*xs[3]+9*xs[2]-9*q*xs[6]+18*q*xs[5]-27*q*xs[4]+36*q*xs[3]-45*q*xs[2]-9*q**2+54*q**2*xs[2]-27*q**2*xs[3]+9*q**2*xs[4]+54*q**3-9*q**3*xs[2]-117*q**4+126*q**5-84*q**6+36*q**7-8*q**8+3*xs[2]**3+18*xs[2]**2-27*q*xs[2]**2-27*xs[2]*xs[3]+18*q*xs[2]*xs[3]+18*xs[2]*xs[4]-9*xs[2]*xs[5]+9*xs[3]**2-9*xs[3]*xs[4])
po=sp.Poly(Phi,*s)
def part(d): return sum(co*sp.prod(v**e for v,e in zip(s,mon)) for mon,co in po.terms() if (sum(mon)==d if d<3 else sum(mon)>=3))
def lean(e):
    t=str(sp.expand(e)).replace('**','^')
    for k in range(7): t=t.replace(f's{k}',f'smom U MU {k}')
    t=t.replace('q','(qval U MU)')
    return t
Lf,Qf,Hf=lean(part(1)),lean(part(2)),lean(part(3))
O=[]
O.append("/-- The `C₉` necklace identity, unrolled from `ccomp_necklace 7`. -/")
O.append("lemma ccomp9_necklace (hU : IsGraphon U μ) :")
O.append("    tr μ (Kpow μ (Wk U) 8)")
O.append("      = mean μ (vcomp U μ 8) - ip μ (pathFun U μ 1) (vcomp U μ 7)")
O.append("        + ip μ (pathFun U μ 2) (vcomp U μ 6) - ip μ (pathFun U μ 3) (vcomp U μ 5)")
O.append("        + ip μ (pathFun U μ 4) (vcomp U μ 4) - ip μ (pathFun U μ 5) (vcomp U μ 3)")
O.append("        + ip μ (pathFun U μ 6) (vcomp U μ 2) - ip μ (pathFun U μ 7) (vcomp U μ 1)")
O.append("        + xden U μ 8 - tr μ (Kpow μ U 8) := by")
O.append("  have h := ccomp_necklace hU 7")
O.append("  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ip_pathFun_zero] at h")
O.append("  norm_num at h")
O.append("  rw [h]; ring")
O.append("")
O.append("set_option maxHeartbeats 1600000 in")
O.append("set_option maxRecDepth 8000 in")
O.append("/-- **`C₉` path-certificate range** (complement form): for `q = ∫∫U ≤ 997/2000`,")
O.append("`t(C₉, 1−U) ≥ (1−q)⁹ − (1−q)q⁸`. -/")
O.append("theorem C9_path_integral (hU : IsGraphon U μ) (hq : qval U μ ≤ 997/2000) :")
O.append("    tr μ (Kpow μ (Wk U) 8) ≥ (1 - qval U μ) ^ 9 - (1 - qval U μ) * qval U μ ^ 8 := by")
O.append("  have hq0 : 0 ≤ qval U μ := qval_nonneg hU")
O.append("  have hx1 : xden U μ 1 = qval U μ := xden_one hU")
for k in range(2,9): O.append(f"  have hx{k} := xden_{['','one','two','three','four','five','six','seven','eight'][k]} hU")
# ip{j}_1 (k=1)
for j in range(1,8):
    O.append(f"  have ip{j}_1 : ip μ (pathFun U μ {j}) (vcomp U μ 1) = xden U μ {j} - xden U μ {j+1} := by")
    O.append(f"    have h := ip_vcomp_succ hU {j} 0; rw [pcomp_zero, ip_vcomp_zero hU {j+1}] at h; simpa using h")
O.append("  have v1 : mean μ (vcomp U μ 1) = 1 - xden U μ 1 := by")
O.append("    have h := pcomp_succ hU 0; rw [pcomp_zero, ip_vcomp_zero hU 1] at h; simpa using h")
# k=2..7
for k in range(2,8):
    for j in range(1,8-k+1):
        O.append(f"  have ip{j}_{k} : ip μ (pathFun U μ {j}) (vcomp U μ {k}) = mean μ (vcomp U μ {k-1}) * xden U μ {j} - ip μ (pathFun U μ {j+1}) (vcomp U μ {k-1}) := by")
        O.append(f"    have h := ip_vcomp_succ hU {j} {k-1}; simpa using h")
    O.append(f"  have v{k} : mean μ (vcomp U μ {k}) = mean μ (vcomp U μ {k-1}) - ip μ (pathFun U μ 1) (vcomp U μ {k-1}) := by")
    O.append(f"    have h := pcomp_succ hU {k-1}; simpa using h")
O.append("  have v8 : mean μ (vcomp U μ 8) = mean μ (vcomp U μ 7) - ip μ (pathFun U μ 1) (vcomp U μ 7) := by")
O.append("    have h := pcomp_succ hU 7; simpa using h")
O.append("  have hed : tr μ (Kpow μ U 8) ≤ xden U μ 8 := edge_deletion_general hU 7")
O.append("  have hcert := cert9_smom hU (qval U μ) hq0 hq")
# build simp list
simps=["v8"]+[f"v{k}" for k in range(7,0,-1)]
for k in range(7,0,-1):
    for j in range(1,8-k+1): simps.append(f"ip{j}_{k}")
O.append("  have key : tr μ (Kpow μ (Wk U) 8)")
O.append("      = ((1 - qval U μ) ^ 9 - (1 - qval U μ) * qval U μ ^ 8)")
O.append(f"        + (({Lf}) + ({Qf}) + ({Hf}))")
O.append("        + (xden U μ 8 - tr μ (Kpow μ U 8)) := by")
O.append("    rw [ccomp9_necklace hU]")
O.append("    simp only [" + ", ".join(simps) + "]")
O.append("    rw [hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8]")
O.append("    ring")
O.append("  rw [key]; linarith [hcert, hed]")
txt="\n".join(O).replace("MU","μ")
open('c9asm_lemma.txt','w',encoding='utf-8').write(txt)
print("wrote",len(txt),"chars,",len(O),"lines")
