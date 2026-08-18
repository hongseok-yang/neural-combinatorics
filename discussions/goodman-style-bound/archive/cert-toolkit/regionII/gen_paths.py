# -*- coding: utf-8 -*-
import sympy as sp
from collections import defaultdict

MU = "μ"  # μ

def path_formulae(max_n):
    q = sp.symbols("q")
    s = sp.symbols("s0:30")
    a = sp.Integer(1)
    h = defaultdict(lambda: sp.Integer(0))
    xs = {0: a}
    for n in range(1, max_n + 1):
        inner = sum(c * s[p] for p, c in h.items())
        a_new = sp.expand(q * a + inner)
        h_new = defaultdict(lambda: sp.Integer(0))
        h_new[0] += a
        for pwr, c in h.items():
            h_new[pwr + 1] += c
        a, h = a_new, h_new
        xs[n] = a
    return q, s, xs

q, s, xs = path_formulae(12)

def to_lean(expr):
    P = sp.Poly(sp.expand(expr), q, *s[:12])
    terms = []
    for monom, coeff in sorted(P.terms(), key=lambda kv: (-sum(kv[0]), tuple(-x for x in kv[0]))):
        c = int(coeff)
        factors = []
        qp = monom[0]
        if qp == 1: factors.append(f"edgeDensity U {MU}")
        elif qp > 1: factors.append(f"edgeDensity U {MU} ^ {qp}")
        for si in range(0, 12):
            e = monom[1 + si]
            if e == 1: factors.append(f"specMoment U {MU} {si}")
            elif e > 1: factors.append(f"specMoment U {MU} {si} ^ {e}")
        body = " * ".join(factors) if factors else "1"
        if abs(c) == 1 and factors:
            term = ("" if c == 1 else "-") + body
        else:
            term = f"{c} * {body}" if factors else f"{c}"
        terms.append(term)
    out = ""
    for idx, term in enumerate(terms):
        if idx == 0:
            out = term
        else:
            out += (" - " + term[1:]) if term.startswith("-") else (" + " + term)
    return out

words = {9: "nine", 10: "ten", 11: "eleven", 12: "twelve"}
prev = {9: "eight", 10: "nine", 11: "ten", 12: "eleven"}

lines = []
for n in [9, 10, 11, 12]:
    cf = to_lean(xs[n])
    # recurrence: x_n = q*x_{n-1} + sum_{i<n-1} s_i * x_{n-2-i}
    m = n - 1  # pathDensity_succ hU m gives x_{m+1}=x_n
    inner = " + ".join(f"specMoment U {MU} {i} * pathDensity U {MU} {m-1-i}" for i in range(m))
    # rw chain of lower closed forms, descending from n-1 to 2
    rwchain = ", ".join(f"pathDensity_{['zero','one','two','three','four','five','six','seven','eight','nine','ten','eleven'][k]} hU" if k>=2 else "" for k in range(n-1, 1, -1))
    lines.append(f"lemma pathDensity_{words[n]} (hU : IsGraphon U {MU}) :")
    lines.append(f"    pathDensity U {MU} {n} = {cf} := by")
    lines.append(f"  have e : pathDensity U {MU} {n} = edgeDensity U {MU} * pathDensity U {MU} {n-1}")
    lines.append(f"      + ({inner}) := by")
    lines.append(f"    have h := pathDensity_succ hU {m}")
    lines.append(f"    simpa [Finset.sum_range_succ, Finset.sum_range_zero] using h")
    lines.append(f"  rw [e, {rwchain},")
    lines.append(f"    show pathDensity U {MU} 1 = edgeDensity U {MU} from pathDensity_one hU, pathDensity_zero]")
    lines.append(f"  ring")
    lines.append("")

with open("paths_out.lean", "w", encoding="utf-8") as f:
    f.write("\n".join(lines))
print("wrote paths_out.lean")
