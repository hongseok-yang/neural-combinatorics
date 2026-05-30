"""
Exact / numerical checker for extremal_structure_direction.tex (Direction 2).

Verifies the variational / extremal-structure results on the odd-cycle conjecture
    f_{C_m}(p) = min{ t(C_m,W) : t(K_2,W)=p } >= g_m(p) := p^m - p(1-p)^{m-1}.

Sections checked (sympy exact where marked, numpy grid scans otherwise):
  S1. Complete-multipartite identity: t(C_m,K(w)) = Tr(M^m), M = s s^T - diag(w), s=sqrt(w),
      p = 1 - ||w||^2; eigenvalues satisfy sum=0, sum sq = p.
  S2. The SCALLOP: between Turan points the best multipartite construction is STRICTLY above g_m,
      with ZERO slack at Turan points (so g_m is tight only at p=1-1/r).
  S3. P2 (multipartite conjecture): Tr(M^m) >= g_m(p) over random simplex, odd m=3..13.
  S4. Two-value family closed form: w=(a,...,a,b) [r copies of a, one b]; M has eigenvalue -a
      (mult r-1) and {lam,-eta} of [[a(r-1),sqrt(rab)],[sqrt(rab),0]];
      Tr(M^m) = -(r-1)a^m + lam^m - eta^m.
  S5. Recursion identity (exact):
        D_{m+2}-a^2 D_m = lam^m(lam^2-a^2) - eta^m(eta^2-a^2) - p^m(p^2-a^2) + p q^{m-1}(q^2-a^2),
      D_m := Tr(M^m) - g_m(p), and base case  D_3 = 2 a r b (a-b)^2 >= 0.
  S6. The section-9 compensation condition (d)  p^2(lam^2-p^2) >= q^2(a^2-q^2)  is FALSE here
      (the (2,2)=0 / independent-part block has larger q=ra^2+b^2); the proof needs the corrected route.
  S7. Corrected route: conditions (a) eta<=a, (b) p>=a, (c) lam>=p, (aux) p>=q, q<=a, eta<=q, and
      A,B,C>=0; the reduced quantity g(m)=Z(m)/p^{m-1} is nondecreasing in odd m with base g(3)>=0,
      where Z(m)=p^{m-1}A + eta^m B - p q^{m-1} C, A=lam(lam^2-a^2)-p(p^2-a^2), B=a^2-eta^2, C=a^2-q^2.
  S8. End-to-end 2-value inequality Tr(M^m) >= g_m via DIRECT matrix powers, r=2..40, odd m<=21.
  S9. m=3 simplex reduction: the gradient F_i=2w_i^2-2w_i+p gives the Schur identity
        (w_i-w_j)(F_i-F_j) = 2(w_i-w_j)^2(w_i+w_j-1) <= 0,  forcing <=2 distinct active part sizes.

All scans report a worst-case margin; '+' margins (or machine-eps negatives) pass.
"""
from __future__ import annotations
import numpy as np
import sympy as sp

def gnum(p, m): return p**m - p*(1-p)**(m-1)
def ok(name, cond, extra=""):
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}{('  '+extra) if extra else ''}")
    if not cond: raise AssertionError(name)

# ----- multipartite operator -----
def M_of_w(w):
    w = np.asarray(w, float); s = np.sqrt(np.maximum(w, 0.0))
    M = np.outer(s, s); np.fill_diagonal(M, np.diag(M) - w)   # ss^T - diag(w)
    return M
def tCm(w, m): return np.trace(np.linalg.matrix_power(M_of_w(w), m))
def pof(w): w = np.asarray(w, float); return 1 - np.sum(w*w)


def S1_identity():
    print("S1. multipartite identity + spectral constraints")
    rng = np.random.default_rng(0)
    worst = 0.0
    for _ in range(2000):
        k = rng.integers(2, 9); w = rng.random(k); w /= w.sum()
        M = M_of_w(w); ev = np.linalg.eigvalsh(M); p = pof(w)
        # sum eigenvalues = 0 ; sum squares = p
        worst = max(worst, abs(ev.sum()), abs(np.sum(ev**2) - p))
        # direct multipartite density Tr((sqrt(wi wj)(1-delta))^m) equals Tr(M^m)
        s = np.sqrt(w); Mt = np.outer(s, s); np.fill_diagonal(Mt, 0.0)
        for m in (3, 5, 7):
            worst = max(worst, abs(np.trace(np.linalg.matrix_power(Mt, m)) - tCm(w, m)))
    ok("Tr M=0, Tr M^2=p, and Tr(M^m)=multipartite density", worst < 1e-9, f"max dev {worst:.1e}")


def S2_scallop():
    print("S2. the scallop: best multipartite > g_m strictly between Turan points, =0 at them")
    from scipy.optimize import minimize
    def min_mp(p, m, k, restarts=120):
        best = np.inf
        rng = np.random.default_rng(7)
        for _ in range(restarts):
            x0 = rng.random(k); x0 /= x0.sum()
            cons = [{'type': 'eq', 'fun': lambda w: w.sum()-1},
                    {'type': 'eq', 'fun': lambda w, pt=p: pof(w)-pt}]
            r = minimize(lambda w: tCm(w, m), x0, bounds=[(0, 1)]*k, constraints=cons,
                         method='SLSQP', options={'maxiter': 400, 'ftol': 1e-12})
            if r.success and abs(pof(r.x)-p) < 1e-7:
                best = min(best, tCm(r.x, m))
        return best
    for m in (3, 5, 7):
        # at Turan p=2/3 (r=3): slack ~0 ; between (p=0.6): strictly positive
        at = min_mp(2/3, m, 3) - gnum(2/3, m)
        bet = min(min_mp(0.60, m, 3), min_mp(0.60, m, 4)) - gnum(0.60, m)
        ok(f"m={m}: Turan slack~0 ({at:+.2e}) and inter-Turan gap>0 ({bet:+.4f})",
           abs(at) < 1e-5 and bet > 1e-3)


def S3_P2():
    print("S3. P2: Tr(M^m) >= g_m(p) over random simplex (odd m=3..13)")
    rng = np.random.default_rng(1)
    for m in (3, 5, 7, 9, 11, 13):
        mn = np.inf
        for _ in range(60000):
            k = rng.integers(2, 9); w = rng.random(k); w /= w.sum(); p = pof(w)
            if p <= 0.5: continue
            mn = min(mn, tCm(w, m) - gnum(p, m))
        ok(f"m={m:2d}: min margin {mn:+.2e}", mn > -1e-9)


# ----- two-value symbolic machinery -----
r, a = sp.symbols('r a', positive=True)
b = 1 - r*a; p = 1 - r*a**2 - b**2; q = 1 - p
tr2 = a*(r-1); det2 = -r*a*b; disc = tr2**2 - 4*det2
lam = (tr2 + sp.sqrt(disc))/2; eta = (sp.sqrt(disc) - tr2)/2
def TrM2(m): return -(r-1)*a**m + lam**m - eta**m
def gm2(m): return p**m - p*q**(m-1)
def D2(m): return TrM2(m) - gm2(m)


def S4_closedform():
    print("S4. two-value closed form vs direct matrix powers")
    worst = 0.0
    rng = np.random.default_rng(5)
    for _ in range(40):
        rv = int(rng.integers(2, 7)); av = float(rng.uniform(1/(rv+1), 1/rv)); bv = 1-rv*av
        w = [av]*rv + [bv]
        for m in (3, 5, 7, 9):
            cf = float(TrM2(m).subs({r: rv, a: av}))
            worst = max(worst, abs(cf - tCm(w, m)))
    ok("Tr(M^m) = -(r-1)a^m + lam^m - eta^m", worst < 1e-9, f"max dev {worst:.1e}")


def S5_recursion_and_base():
    print("S5. recursion identity (exact) + base case D_3 = 2 a r b (a-b)^2")
    for m in (3, 5, 7):
        lhs = sp.simplify(D2(m+2) - a**2*D2(m))
        rhs = sp.simplify(lam**m*(lam**2-a**2) - eta**m*(eta**2-a**2)
                          - p**m*(p**2-a**2) + p*q**(m-1)*(q**2-a**2))
        ok(f"recursion identity m={m}", sp.simplify(lhs - rhs) == 0)
    ok("D_3 == 2 a r b (a-b)^2", sp.simplify(sp.factor(D2(3)) - 2*a*r*b*(a-b)**2) == 0)


def _scan2(expr):
    f = sp.lambdify((r, a), expr, 'numpy'); mn = np.inf
    for rv in range(2, 13):
        av = np.linspace(1/(rv+1)+1e-6, 1/rv-1e-9, 250)
        mn = min(mn, float(np.min(f(rv, av))))
    return mn


def S6_condition_d_fails():
    print("S6. section-9 compensation (d) FAILS for the (2,2)=0 block")
    comp_d = p**2*(lam**2-p**2) - q**2*(a**2-q**2)
    mn = _scan2(comp_d)
    ok(f"min p^2(lam^2-p^2)-q^2(a^2-q^2) = {mn:+.2e} < 0  (so naive sec-9 transfer is refuted)", mn < -1e-5)


def S7_corrected_route():
    print("S7. corrected route: conditions + Z(m)>=0 + g(m) nondecreasing")
    A = lam*(lam**2-a**2) - p*(p**2-a**2); B = a**2 - eta**2; C = a**2 - q**2
    for nm, e in [("(a) eta<=a", a-eta), ("(b) p>=a", p-a), ("(c) lam>=p", lam-p),
                  ("(aux) p>=q", p-q), ("q<=a", a-q), ("eta<=q", q-eta),
                  ("A>=0", A), ("B>=0", B), ("C>=0", C)]:
        mn = _scan2(e); ok(f"{nm}  (min {mn:+.2e})", mn > -1e-9)
    # Z(m) >= 0 and g(m)=Z/p^{m-1} nondecreasing in odd m, base g(3)>=0
    Zf = {m: sp.lambdify((r, a), p**(m-1)*A + eta**m*B - p*q**(m-1)*C, 'numpy') for m in range(3, 18, 2)}
    pf = sp.lambdify((r, a), p, 'numpy')
    zmin = np.inf; mono_viol = 0; g3min = np.inf
    for rv in range(2, 13):
        av = np.linspace(1/(rv+1)+1e-6, 1/rv-1e-9, 200)
        ms = sorted(Zf)
        gs = [Zf[m](rv, av)/pf(rv, av)**(m-1) for m in ms]
        for arr in [Zf[m](rv, av) for m in ms]:
            zmin = min(zmin, float(np.min(arr)))
        g3min = min(g3min, float(np.min(gs[0])))
        for i in range(len(gs)-1):
            mono_viol += int(np.any(gs[i+1] < gs[i] - 1e-12))
    ok(f"Z(m)>=0 (min {zmin:+.2e})", zmin > -1e-9)
    ok(f"base g(3)>=0 (min {g3min:+.2e})", g3min > -1e-9)
    ok(f"g(m)=Z(m)/p^(m-1) nondecreasing in odd m (violations {mono_viol})", mono_viol == 0)


def S8_end_to_end():
    print("S8. END-TO-END 2-value inequality, direct matrix powers, r=2..40, odd m<=21")
    mn = np.inf; viol = 0
    for rv in range(2, 41):
        for av in np.linspace(1/(rv+1)+1e-7, 1/rv-1e-12, 100):
            bv = 1-rv*av; w = np.array([av]*rv + [bv]); pv = 1-np.sum(w*w)
            for m in range(3, 22, 2):
                val = tCm(w, m) - gnum(pv, m); mn = min(mn, val)
                if val < -1e-9: viol += 1
    ok(f"min margin {mn:+.2e}, violations {viol}", viol == 0)


def S9_m3_reduction():
    print("S9. m=3 simplex reduction: Schur identity forces <=2 distinct part sizes")
    wi, wj, pp = sp.symbols('w_i w_j p')
    Fi = 2*wi**2 - 2*wi + pp; Fj = 2*wj**2 - 2*wj + pp
    ok("(w_i-w_j)(F_i-F_j) == 2(w_i-w_j)^2(w_i+w_j-1)",
       sp.simplify((wi-wj)*(Fi-Fj) - 2*(wi-wj)**2*(wi+wj-1)) == 0)


def main():
    for fn in (S1_identity, S2_scallop, S3_P2, S4_closedform, S5_recursion_and_base,
               S6_condition_d_fails, S7_corrected_route, S8_end_to_end, S9_m3_reduction):
        fn()
    print("\nAll extremal-structure checks passed.")


if __name__ == "__main__":
    main()
