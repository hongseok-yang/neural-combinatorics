"""
Checker for the "Closure attempt (negative)" addendum of odd_cycle_c13_working_note.tex.

Verifies the load-bearing facts of the (failed) attempt to close the residual C_13 band
q in (0.481, 0.48441):

  C1. PATH CERTIFICATE FAILS IN THE GAP (exact rational witness, UNEQUAL weights).
      Two-block complement U with weights (39/100, 61/100) and block values
      [[43/50, 1/10], [1/10, 41/50]] has q = 120877/250000 = 0.483508 (in the gap),
      Phi_13 = -2.0758...e-7 < 0   (so the deletion-discarding path certificate cannot
      be extended below rho_13 = 519/1000), while the TRUE defect t(C13,W)-g13 = +1.10e-4 > 0.

  C2. ONE-EXCESS-EIGENVALUE LEMMA. Tr(A^2) <= pq, so for q > 1/3 the compression
      A = P_{1perp} T_U P_{1perp} has at most one eigenvalue exceeding q.
      (numeric: zero violations over random band graphons.)

  C3. lambda_min(T_W) >= -1/2 for every graphon (T_W = (1/2)(J + T_S), ||T_S|| <= 1).

Builds Phi_13 from inclusion-exclusion (same as odd_cycle_c13_checker.py) and evaluates it
on the witness via the UNEQUAL-weight moment recursion (the equal-weight version used earlier
misses this witness -- that was the diagnostic error the addendum corrects).
"""
from __future__ import annotations
import numpy as np
import sympy as sp
from collections import Counter, defaultdict
from itertools import combinations


def _path_components(n, subset):
    adj = [set() for _ in range(n)]
    for i in subset:
        u, v = i, (i + 1) % n
        adj[u].add(v); adj[v].add(u)
    seen, comps = set(), []
    for v in range(n):
        if adj[v] and v not in seen:
            st = [v]; seen.add(v); e2 = 0
            while st:
                a = st.pop(); e2 += len(adj[a])
                for b in adj[a]:
                    if b not in seen:
                        seen.add(b); st.append(b)
            comps.append(e2 // 2)
    return tuple(sorted(comps, reverse=True))


def _build_Phi(n=13):
    counts = {r: Counter(_path_components(n, s) for s in combinations(range(n), r))
              for r in range(n + 1)}
    q = sp.symbols('q'); s = sp.symbols('s0:30')
    a = sp.Integer(1); h = defaultdict(lambda: sp.Integer(0)); xs = {0: a}
    for k in range(1, n):
        inner = sum(c * s[p] for p, c in h.items())
        a2 = sp.expand(q * a + inner)
        h2 = defaultdict(lambda: sp.Integer(0)); h2[0] += a
        for pw, c in h.items():
            h2[pw + 1] += c
        a, h = a2, h2; xs[k] = a

    def term(comp):
        o = sp.Integer(1)
        for x in comp:
            o *= q if x == 1 else xs[x]
        return o
    E = sp.Integer(1)
    for r in range(1, n):
        for comp, c in counts[r].items():
            E += (-1) ** r * c * term(comp)
    E -= xs[n - 1]
    Phi = sp.expand(E - ((1 - q) ** n - (1 - q) * q ** (n - 1)))
    return Phi, q, [s[j] for j in range(n - 2)]


def check_C1_path_fails():
    Phi, q_s, sv = _build_Phi(13)
    # exact moments for an UNEQUAL-weight 2-block complement U
    w = [sp.Rational(39, 100), sp.Rational(61, 100)]
    B = sp.Matrix([[sp.Rational(43, 50), sp.Rational(1, 10)],
                   [sp.Rational(1, 10), sp.Rational(41, 50)]])
    wv = sp.Matrix(w)
    Dw = sp.diag(*w); one = sp.ones(2, 1)
    qv = (wv.T * B * wv)[0]
    g = B * wv - qv * one                      # d_U - q 1, d_U = B w
    P0 = sp.eye(2) - one * wv.T                 # P0 f = f - (w^T f) 1
    A = P0 * (B * Dw) * P0                       # T_U = B Dw (standard), compression
    sjs, Aj = [], sp.eye(2)
    for j in range(11):
        sjs.append((g.T * Dw * Aj * g)[0]); Aj = A * Aj
    Phi_val = sp.nsimplify(Phi.subs({q_s: qv, **{sv[j]: sjs[j] for j in range(11)}}))
    assert qv == sp.Rational(120877, 250000), qv
    assert 0.481 < float(qv) < 0.48441, float(qv)
    assert float(Phi_val) < 0, float(Phi_val)
    # true defect > 0
    wf = np.array([0.39, 0.61]); Bf = np.array([[0.86, 0.10], [0.10, 0.82]])
    TW = (1 - Bf) @ np.diag(wf)
    tc13 = np.trace(np.linalg.matrix_power(TW, 13))
    p = 1 - float(qv); g13 = p ** 13 - p * (1 - p) ** 12
    assert tc13 - g13 > 0, tc13 - g13
    print(f"OK C1: witness q={float(qv):.6f} (in gap), Phi_13={float(Phi_val):.3e}<0, "
          f"true defect={tc13-g13:+.3e}>0  (path certificate provably fails in the gap)")


def check_C2_one_excess():
    rng = np.random.default_rng(0); bad = 0; tested = 0
    for _ in range(20000):
        k = rng.integers(2, 8); w = rng.random(k); w /= w.sum()
        B = rng.random((k, k)); B = (B + B.T) / 2
        qv = w @ B @ w
        if not (1/3 < qv < 0.5):
            continue
        tested += 1
        Dw = np.diag(w); one = np.ones(k)
        P0 = np.eye(k) - np.outer(one, w)
        A = P0 @ (B @ Dw) @ P0
        Dh = np.diag(np.sqrt(w)); Dhi = np.diag(1/np.sqrt(w))
        As = Dh @ A @ Dhi; ev = np.linalg.eigvalsh((As + As.T) / 2)
        if np.sum(ev > qv + 1e-9) > 1:
            bad += 1
    assert bad == 0, bad
    print(f"OK C2: at most one eigenvalue of A exceeds q over {tested} band graphons "
          f"(0 violations; rigorous for q>1/3 since Tr(A^2)<=pq)")


def check_C3_lambda_min():
    # lambda_min(T_W) >= -1/2 for random step graphons W (T_W = (1/2)(J + T_S), S=2W-1)
    rng = np.random.default_rng(1); worst = np.inf
    for _ in range(20000):
        k = rng.integers(2, 9); w = rng.random(k); w /= w.sum()
        W = rng.random((k, k)); W = (W + W.T) / 2
        Dh = np.diag(np.sqrt(w))
        TWsym = Dh @ W @ Dh           # symmetric similarity of T_W = W Dw
        worst = min(worst, float(np.min(np.linalg.eigvalsh(TWsym))))
    assert worst >= -0.5 - 1e-9, worst
    print(f"OK C3: min eigenvalue of T_W over random graphons = {worst:.4f} >= -1/2")


def main():
    check_C1_path_fails()
    check_C2_one_excess()
    check_C3_lambda_min()
    print("\nAll C13-closure-attempt checks passed (the gap remains OPEN; these verify the "
          "obstruction facts, not a closure).")


if __name__ == "__main__":
    main()
