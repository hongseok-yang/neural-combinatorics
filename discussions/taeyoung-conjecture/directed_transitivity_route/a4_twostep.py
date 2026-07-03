"""
For all n=6 top-branch non-multipartite graphs:
  L0: exists clone (i->j, nonadjacent) with ENDPOINT Delta2(1) <= Delta2(0)+tol?
  L1: if not, exists two-step clone sequence with final Delta2 <= start?
  Report counts; if some graph fails both, print it (two-step dead too).
Endpoint here = full discrete Zykov clone (t=1).
Also: for graphs failing L0, is Delta2 already >= the multipartite bound
anyway... not needed; we only care about potential-route viability.
"""
import sys
sys.path.insert(0, "/private/tmp/cancel")
import numpy as np
from itertools import combinations
from frame import F_data

def clone_graph(A, i, j):
    B = A.copy()
    n = A.shape[0]
    for k in range(n):
        if k == i: continue
        B[i, k] = B[k, i] = (0 if k == j else A[j, k])
    B[i, i] = 0
    return B

def d2(A):
    n = A.shape[0]
    return F_data(np.full(n, 1.0/n), A)["Delta2"]

def is_cm(A):
    n = A.shape[0]
    U = (1 - A - np.eye(n)) > 0.5
    for a in range(n):
        for b in range(n):
            if not U[a, b]: continue
            for c in range(n):
                if c != a and U[b, c] and not (U[a, c] or a == c):
                    return False
    return True

n = 6
pairs = list(combinations(range(n), 2))
tol = 1e-12
fail_L0 = []
for mask in range(1 << len(pairs)):
    A = np.zeros((n, n))
    for e, (i, j) in enumerate(pairs):
        if (mask >> e) & 1: A[i, j] = A[j, i] = 1
    if 2 * A.sum() < n * n: continue
    if is_cm(A): continue
    base = d2(A)
    ok = False
    for (i, j) in pairs:
        if A[i, j] == 1: continue
        if d2(clone_graph(A, i, j)) <= base + tol or d2(clone_graph(A, j, i)) <= base + tol:
            ok = True; break
    if not ok:
        fail_L0.append((mask, base))
print(f"n=6: graphs with NO single-clone endpoint decrease: {len(fail_L0)}")

fail_L1 = []
for mask, base in fail_L0:
    A = np.zeros((n, n))
    for e, (i, j) in enumerate(pairs):
        if (mask >> e) & 1: A[i, j] = A[j, i] = 1
    ok = False
    moves = [(i, j) for (i, j) in pairs if A[i, j] == 0] + \
            [(j, i) for (i, j) in pairs if A[i, j] == 0]
    for (i, j) in moves:
        B = clone_graph(A, i, j)
        moves2 = [(a, b) for (a, b) in combinations(range(n), 2) if B[a, b] == 0] + \
                 [(b, a) for (a, b) in combinations(range(n), 2) if B[a, b] == 0]
        for (a, b) in moves2:
            if d2(clone_graph(B, a, b)) <= base + tol:
                ok = True; break
        if ok: break
    if not ok:
        fail_L1.append((mask, base))
print(f"n=6: of those, graphs with NO two-step decrease: {len(fail_L1)}")
for mask, base in fail_L1[:5]:
    A = np.zeros((n, n), int)
    for e, (i, j) in enumerate(pairs):
        if (mask >> e) & 1: A[i, j] = A[j, i] = 1
    print(f"mask={mask} Delta2={base:.6f} p={A.sum()/n**2}")
    print(A)
