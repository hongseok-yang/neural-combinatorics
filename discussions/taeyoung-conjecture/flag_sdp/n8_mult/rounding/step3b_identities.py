"""
Step 3b: EXACT identity checks on the integer tables (pure Fraction/int).

(1) Delta2(W==p) = p^5 (1-p)^2 as an exact polynomial identity:
      sum_H nlab[H] * coef_int[H]/40320 * p^e(H) (1-p)^(28-e(H))
    with nlab[H] = 8!/|Aut(H)| recounted as exact ints.
(2) Delta2(T_k) = 0 for ALL k>=2:
      p8(K_lam, T_k) = S_lam * (k)_l / k^8,  S_lam = 8!/(prod lam_i! prod m_j!)
    so it suffices that for every part count l: sum_{lam: l parts} S_lam *
    coef_int[K_lam] = 0.  (Also gives Delta2(T_k)=0 for the W==1 limit.)
(3) the same per-l identity with p8 weights, evaluated at k=2..10 exactly.
"""
import pickle, itertools, math
from fractions import Fraction
import numpy as np

import common
import n8lib

cl, coef, SQ, metaQ, pl, res = common.load_everything()
with open(common.os.path.join(common.DATA, "exact_tables.pkl"), "rb") as f:
    ET = pickle.load(f)
coef_int = [int(x) for x in ET["coef_int"]]
CD = ET["COEF_DEN"]

# ---------------- (1) constant-graphon polynomial identity
print("recounting |Aut| for all 12346 classes (exact ints) ...")
nlab = []
for m in cl.masks:
    a = n8lib.aut_count(n8lib.adjrows_from_mask(m))
    assert math.factorial(8) % a == 0
    nlab.append(math.factorial(8) // a)
# cross-check the cached float labeled counts
lc = n8lib.labeled_counts(cl)
assert max(abs(int(round(x)) - y) for x, y in zip(lc, nlab)) == 0
print("  matches cached labeled_counts exactly")

# polynomial sum: P(p) = sum_H nlab*coef_int/CD * p^e (1-p)^(28-e)
# coefficients of p^j: accumulate integer polys
polyacc = [Fraction(0)] * 29
binom = [[math.comb(n, k) for k in range(n + 1)] for n in range(29)]
for h, m in enumerate(cl.masks):
    c = coef_int[h]
    if c == 0:
        continue
    e = n8lib.mask_edge_count(m)
    w = Fraction(nlab[h] * c, CD)
    # p^e (1-p)^(28-e) = sum_t C(28-e,t) (-1)^t p^(e+t)
    for t in range(28 - e + 1):
        polyacc[e + t] += w * ((-1) ** t) * binom[28 - e][t]
# target: p^5 (1-p)^2 = p^5 - 2p^6 + p^7
target = [Fraction(0)] * 29
target[5], target[6], target[7] = Fraction(1), Fraction(-2), Fraction(1)
ok1 = polyacc == target
print(f"(1) Delta2(W==p) == p^5(1-p)^2 exactly: {ok1}")
assert ok1

# ---------------- (2) per-part-count multipartite identities
with open(common.os.path.join(common.DATA, "multipartite22.pkl"), "rb") as f:
    multi_idx = pickle.load(f)


def S_lam(lam):
    from collections import Counter
    r = math.factorial(8)
    for x in lam:
        r //= math.factorial(x)
    for mult in Counter(lam).values():
        r //= math.factorial(mult)
    return r


byl = {}
for lam, idx in multi_idx.items():
    byl.setdefault(len(lam), []).append((lam, idx))
print("(2) per-l identities  sum_lam S_lam * coef[K_lam]  (must be 0):")
allok = True
for l in sorted(byl):
    tot = sum(S_lam(lam) * coef_int[idx] for lam, idx in byl[l])
    print(f"    l={l}:  {tot}")
    allok &= (tot == 0)
assert allok
print("    => Delta2(T_k) = 0 EXACTLY for every k>=2 (and W==1).")

# ---------------- (3) direct exact Delta2(T_k), k=2..10
for k in range(2, 11):
    tot = Fraction(0)
    for lam, idx in multi_idx.items():
        l = len(lam)
        if l > k:
            continue
        fall = 1
        for i in range(l):
            fall *= (k - i)
        tot += Fraction(S_lam(lam) * fall, k ** 8) * Fraction(coef_int[idx], CD)
    assert tot == 0, (k, tot)
print("(3) direct Delta2(T_k)==0 for k=2..10: all pass")
print("\nALL EXACT IDENTITY CHECKS PASSED")
