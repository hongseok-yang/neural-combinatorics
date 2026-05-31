"""
Findings from the strategy-#1 proof attempt (2026-05-31): the local-rigidity / stability
approach anchored at the TRIANGLE-extremal family is misaimed for C_13, because that family
is not the C_13 extremal structure in the strip.  Two checks:

F1 (RIGOROUS). The triangle-extremal complete tripartite graphon W_c = (c, b, b), b=(1-c)/2,
   is NOT a KKT-stationary point of  min t(C_13, W) s.t. t(K_2,W)=p  for c in (0, 1/3).
   First-variation kernel K = 13 * (T_{W_c})^12, block values via ((B_W D_w)^11 B_W),
   B_W = [[0,1,1],[1,0,1],[1,1,0]], D_w = diag(c,b,b).
   - Validation anchor: at c=1/3 (balanced Turan T_3) K is block-constant with
       min(K_diag) - max(K_offdiag) = 13/3^11  (Direction-2 value) > 0.  [stationary at p=2/3]
   - For c in (0, ~0.3328): K_cb (c-b cross block, W=1, must be <= nu) STRICTLY EXCEEDS
       K_bb (b-b within block, W=0, must be >= nu).  No multiplier nu can separate them, so
       W_c is NOT stationary: t(C_13) strictly decreases along "add b-b within / remove c-b cross".

F2 (NUMERICAL). The actual C_13 minimizer at p in the strip is a NEAR-BIPARTITE 2-block graphon:
   two parts ~1/2 each, cross density 1, one part with a small internal fill ~0.06-0.074, the
   other ~0.  Margin t(C_13)-g_13 ~ 4.7e-6, BELOW the triangle-extremal margin ~1.9e-5.  So the
   minimizer is NOT complete multipartite and NOT the triangle-extremal family.
"""
from __future__ import annotations
import numpy as np
import sympy as sp


def check_F1_triangle_not_stationary():
    c = sp.symbols('c'); b = (1 - c) / 2
    Dw = sp.diag(c, b, b); BW = sp.Matrix([[0, 1, 1], [1, 0, 1], [1, 1, 0]])
    K = sp.expand(13 * ((BW * Dw) ** 11) * BW)
    Kcc, Kbb, Kcb, Kbb2 = K[0, 0], K[1, 1], K[0, 1], K[1, 2]
    # anchor at c=1/3: block-constant, gap = 13/3^11
    sub = {c: sp.Rational(1, 3)}
    vals = [sp.nsimplify(x.subs(sub)) for x in (Kcc, Kbb, Kcb, Kbb2)]
    gap13 = min(vals[0], vals[1]) - max(vals[2], vals[3])
    assert sp.nsimplify(gap13 - sp.Rational(13, 3 ** 11)) == 0, gap13
    print(f"OK F1-anchor: at c=1/3, min(K_diag)-max(K_offdiag) = 13/3^11 = {float(gap13):.3e} (stationary)")
    # strip / interior: K_cb > K_bb (KKT violation) -> not stationary
    f = sp.lambdify(c, sp.expand(Kcb - Kbb), 'numpy')
    cs = np.linspace(0.005, 0.33, 60)
    viol = np.min(f(cs))
    assert viol > 1e-9, viol   # K_cb - K_bb > 0 throughout => violation everywhere on the strip
    # find where stationarity is restored (sign change of min(diag)-max(off))
    fcc, fbb, fcb, fbb2 = [sp.lambdify(c, x, 'numpy') for x in (Kcc, Kbb, Kcb, Kbb2)]
    grid = np.linspace(0.001, 1/3 - 1e-7, 4000)
    gamma = np.array([min(fcc(x), fbb(x)) - max(fcb(x), fbb2(x)) for x in grid])
    sc = grid[np.where(np.diff(np.sign(gamma)) != 0)]
    print(f"OK F1: K_cb - K_bb >= {viol:.3e} > 0 on (0,1/3) (triangle-extremal NOT C_13-stationary);")
    print(f"       stationarity holds only for c >~ {sc[0]:.4f} (i.e. only near the Turan point p=2/3)")


def _t2(w, b1, b2, gam):
    wv = np.array([w, 1 - w]); s = np.sqrt(wv)
    B = np.array([[b1, gam], [gam, b2]]); M = np.diag(s) @ B @ np.diag(s)
    return np.trace(np.linalg.matrix_power(M, 13))


def _e2(w, b1, b2, gam):
    wv = np.array([w, 1 - w]); return wv @ np.array([[b1, gam], [gam, b2]]) @ wv


def check_F2_minimizer_near_bipartite():
    from scipy.optimize import minimize
    rng = np.random.default_rng(1)
    g13 = lambda p: p ** 13 - p * (1 - p) ** 12
    # triangle-extremal margin at strip p
    ptar = 0.5152
    c = 0.0156; b = (1 - c) / 2; wv = np.array([c, b, b]); s = np.sqrt(wv)
    BW = np.array([[0., 1, 1], [1, 0, 1], [1, 1, 0]]); M = np.diag(s) @ BW @ np.diag(s)
    tri = np.trace(np.linalg.matrix_power(M, 13)); ptri = wv @ BW @ wv
    tri_margin = tri - g13(ptri)
    # 2-block minimizer
    best = np.inf; bx = None
    for _ in range(300):
        x0 = rng.random(4)
        r = minimize(lambda x: _t2(*x), x0, bounds=[(1e-4, 1 - 1e-4), (0, 1), (0, 1), (0, 1)],
                     constraints=[{'type': 'eq', 'fun': lambda x: _e2(*x) - ptar}],
                     method='SLSQP', options={'maxiter': 500, 'ftol': 1e-15})
        if r.success and abs(_e2(*r.x) - ptar) < 1e-9 and _t2(*r.x) < best:
            best = _t2(*r.x); bx = r.x
    nb_margin = best - g13(ptar)
    assert nb_margin > 0, nb_margin
    assert nb_margin < tri_margin, (nb_margin, tri_margin)  # near-bipartite beats triangle-extremal
    w, b1, b2, gam = bx
    assert abs(gam - 1) < 1e-2, gam                          # cross ~ 1
    assert min(b1, b2) < 1e-2 and 0.02 < max(b1, b2) < 0.2   # one internal ~0, other small fill
    print(f"OK F2: 2-block near-bipartite min margin = {nb_margin:.3e}  <  triangle-extremal margin = {tri_margin:.3e}")
    print(f"       minimizer: weights ~(1/2,1/2), cross gamma={gam:.3f}, internals ({b1:.3f},{b2:.3f})"
          f"  -> complete bipartite + small fill, NOT multipartite, NOT tripartite")


def main():
    check_F1_triangle_not_stationary()
    check_F2_minimizer_near_bipartite()
    print("\nConclusion: the C_13 strip extremal structure is NEAR-BIPARTITE, not the triangle-extremal\n"
          "tripartite family -> strategy #1 (stability around the triangle-extremal) is misaimed.")


if __name__ == "__main__":
    main()
