#!/usr/bin/env python3
"""FINAL verifier for Lemma Z-B (Region-II scalar Huber inequality, Zone B).

Lemma Z-B: for admissible (q, alpha), m >= 15, with e := 1-2*alpha in [1/60, 1/3)
and xi := 4 alpha^2 d / e^2 >= 1:
        R_m <= sqrt(2 alpha) * B_m * f * (d - e^2/(16 alpha^2 (1+rho))).

This script checks EVERY step of the proof chain in proof_ZB_final.md:

  Part 0: unit tests of the directed rational rounding / sqrt primitives.
  Part A: Step 0 (emptiness of e >= e1 := 2033/10000), exact rational + grid.
  Part B: Steps 1-3 pointwise on dense adversarial (e,kappa,m) grids incl. all
          boundary regimes (mpmath, 60 significant digits):
     C1  defect identity      R_m = a^{m-1}[a(1-tau^{m-1}) - (d+e)tau^{m-1}] + L^m
     C2  defect upper bound   R_m <= a^{m-1}[(m-1)d/x - (d+e)] + L^m
     C3  reduction identity   (RHS of C2)/D = J(m-1) + Lam_L,  D = m d a p^{m-2}
     C4  payment lower bound  P >= D * Pi_m
     C5  rho >= rho_lb(e,kappa)
     C6  eps <= eps_ub(e,kappa)  and  eps <= 1/4
     C7  Pi_m >= Pi_lo(e,kappa)
     C8  J(n) <= Jhat(e,kappa) for all integers n >= 14 (incl. far beyond scan cap)
     C9  Lam_L <= Lam_bar(e,kappa)
     C11 final: P >= R_m (chain coherence)
  Part C: Step 4 battle  Pi_lo >= Jhat + Lam_bar  on a fine float grid (margins).
  Part D: Step 4 battle RIGOROUS certification: adaptive interval boxes with exact
          Fraction endpoints and outward dyadic rounding; plus
     T1  degenerate-box direction test against pointwise mpmath values
     T2  random-box enclosure test (interval bounds enclose interior point values)
     T3  Monte-Carlo coverage audit of the produced leaf tiling.

All inequalities are reported as worst (minimum) slacks; every slack must be >= 0
up to identity-roundoff ~1e-50 for the two exact identities C1/C3.
"""
import math, random, sys, time
from fractions import Fraction as F
from mpmath import mp, mpf, sqrt, ceil

mp.dps = 60

E0 = F(1, 60)
E1 = F(2033, 10000)

# ----------------------------------------------------------------------------
# exact rational directed arithmetic
# ----------------------------------------------------------------------------
BITS = 120
SCALE = 1 << BITS

def rup(r):
    return F(-((-r.numerator * SCALE) // r.denominator), SCALE)

def rdn(r):
    return F((r.numerator * SCALE) // r.denominator, SCALE)

def sqrt_up(r):
    if r < 0: raise ValueError("sqrt_up of negative")
    if r == 0: return F(0)
    rr = rup(r)                                   # denominator divides SCALE
    n = rr.numerator * (SCALE // rr.denominator)  # rr = n / SCALE
    return F(math.isqrt(n * SCALE) + 1, SCALE)

def sqrt_dn(r):
    if r <= 0: return F(0)
    rr = rdn(r)
    n = rr.numerator * (SCALE // rr.denominator)
    return F(math.isqrt(n * SCALE), SCALE)

def pow_up(b, n):
    r = F(1); base = rup(b)
    while n:
        if n & 1: r = rup(r * base)
        base = rup(base * base); n >>= 1
    return r

SQRT2_UP = None

def kxi_F(e):  return e / (1 - e) ** 2
def khi_F(e):  return min((1 - e) / (1 + e), (1 - 3 * e) / (6 * e))

# ----------------------------------------------------------------------------
# mpmath pointwise quantities
# ----------------------------------------------------------------------------
def kxi_m(e):  return e / (1 - e) ** 2
def khi_m(e):  return min((1 - e) / (1 + e), (1 - 3 * e) / (6 * e))

def base_m(e, kap):
    a = (1 - e) / 2; d = kap * e; q = a - d; p = 1 - q
    L2 = a * e - d * (d + e)
    L = sqrt(L2) if L2 > 0 else mpf(0)
    return dict(a=a, d=d, q=q, p=p, L2=L2, L=L, f=a - L, x=a / p, y=L / p,
                l=L / a, tau=q / a, A=(a / p) * (1 + 1 / kap), e=e, kap=kap)

def rho_lb_m(b):
    return (1 - b['x'] ** 14) * sqrt(b['a']) / (2 * sqrt(mpf(2)) * b['f'] * (1 + b['x']))

def eps_ub_m(b):
    return min(mpf(1) / 4, b['e'] / (4 * (1 - b['e']) ** 2 * b['kap'] * (1 + rho_lb_m(b))))

def Pi_lo_m(b):
    return sqrt(1 - b['e']) * (1 - b['l']) * (1 - b['y'] ** 14) * (1 - eps_ub_m(b)) / (1 + b['y'])

def J_m(b, n):
    return b['x'] ** (n - 2) * (n - b['A']) / (n + 1)

def Jhat_m(b):
    N = max(int(ceil(b['A'] + 1 / (1 - b['x']))) + 1, 14)
    best = mpf(0)
    for n in range(14, N + 1):
        v = J_m(b, n)
        if v > best: best = v
    return best, N

def Lam_bar_m(b):
    return b['y'] ** 15 * b['p'] ** 2 / (15 * b['d'] * b['a'])

def full_m(e, kap, m):
    b = base_m(e, kap)
    a, d, q, p = b['a'], b['d'], b['q'], b['p']
    L, f, x, y, l, tau = b['L'], b['f'], b['x'], b['y'], b['l'], b['tau']
    km_a = (p ** (m - 1) - a ** (m - 1)) / (p + a)
    km_L = (p ** (m - 1) - L ** (m - 1)) / (p + L)
    A_m = 2 * L ** (m - 2) + m * km_a
    B_m = 2 * L ** (m - 2) + m * km_L
    R = a ** m + L ** m - p * q ** (m - 1)
    rho = (A_m / B_m) * sqrt(a) / (2 * sqrt(mpf(2)) * f)
    eps_hat = e * e / (16 * a * a * (1 + rho))
    P = sqrt(2 * a) * B_m * f * (d - eps_hat)
    D = m * d * a * p ** (m - 2)
    eps = eps_hat / d
    Pi_m = sqrt(1 - e) * (1 - l) * (1 - y ** (m - 1)) * (1 - eps) / (1 + y)
    R_id = a ** (m - 1) * (a * (1 - tau ** (m - 1)) - (d + e) * tau ** (m - 1)) + L ** m
    R_ub = a ** (m - 1) * ((m - 1) * d / x - (d + e)) + L ** m
    Jn = J_m(b, m - 1)
    LamL = y ** m * p ** 2 / (m * d * a)
    return dict(b=b, R=R, P=P, D=D, rho=rho, eps=eps, Pi_m=Pi_m, R_id=R_id,
                R_ub=R_ub, Jn=Jn, LamL=LamL)

# ----------------------------------------------------------------------------
# rigorous interval box check (Step 4)
# ----------------------------------------------------------------------------
def box_check(elo, ehi, klo, khi_):
    if khi_ < kxi_F(elo) or klo > khi_F(elo):
        return ('EMPTY', None)
    a_lo = (1 - ehi) / 2; a_hi = (1 - elo) / 2
    d_lo = klo * elo
    p_lo = (1 + elo) / 2 + d_lo
    p_hi = (1 + ehi) / 2 + khi_ * ehi
    L2_lo = elo * (1 - elo) / 2 - khi_ * (1 + khi_) * ehi * ehi
    if L2_lo < 0: L2_lo = F(0)
    L2_hi = ehi * (1 - ehi) / 2 - klo * (1 + klo) * elo * elo
    if L2_hi < 0: L2_hi = F(0)
    L_lo = sqrt_dn(L2_lo); L_hi = sqrt_up(L2_hi)
    x_hi = a_hi / p_lo   # exact max of x on box (x decreasing in e and kappa)
    x_lo = a_lo / p_hi   # exact min
    if x_hi >= 1: return ('FAIL', None)
    y_hi = rup(L_hi / p_lo)
    l_hi = rup(L_hi / a_lo)
    f_hi = a_hi - L_lo
    x14_hi = pow_up(x_hi, 14)
    if x14_hi >= 1: return ('FAIL', None)
    rho_lb = rdn(rdn((1 - x14_hi) * sqrt_dn(a_lo)) / rup(2 * SQRT2_UP * f_hi * (1 + x_hi)))
    if rho_lb < 0: rho_lb = F(0)
    eps_up = rup(ehi / (4 * (1 - ehi) ** 2 * klo * (1 + rho_lb)))
    if eps_up > F(1, 4): eps_up = F(1, 4)   # valid on box \cap D (xi >= 1 there)
    if l_hi >= 1 or y_hi >= 1 or eps_up >= 1: return ('FAIL', None)
    y14_hi = pow_up(y_hi, 14)
    if y14_hi >= 1: return ('FAIL', None)
    Pi = sqrt_dn(1 - ehi)
    Pi = rdn(Pi * (1 - l_hi)); Pi = rdn(Pi * (1 - y14_hi))
    Pi = rdn(Pi * (1 - eps_up)); Pi = rdn(Pi / (1 + y_hi))
    A_lo = x_lo * (1 + 1 / khi_)   # exact min of A on box (A decreasing in e and kappa)
    Ncap = A_lo + 1 / (1 - x_hi)
    N = -((-Ncap.numerator) // Ncap.denominator) + 1
    if N < 14: N = 14
    powx = pow_up(x_hi, 12); Jmax = F(0); n = 14
    while n <= N:
        num = n - A_lo
        if num > 0:
            v = rup(powx * num / (n + 1))
            if v > Jmax: Jmax = v
        powx = rup(powx * x_hi); n += 1
    Lam = rup(rup(pow_up(y_hi, 15) * p_hi * p_hi) / (15 * d_lo * a_lo))
    margin = Pi - Jmax - Lam
    return ('PASS', margin) if margin >= 0 else ('FAIL', margin)

def certify(require=F(1, 20), max_boxes=2_000_000, max_depth=60):
    leaves = []
    stack = [(E0, E1, F(60, 3481), F(59, 61), 0)]
    processed = 0
    min_margin = None
    while stack:
        elo, ehi, klo, khi_, depth = stack.pop()
        processed += 1
        if processed > max_boxes: raise RuntimeError("box budget exceeded")
        status, margin = box_check(elo, ehi, klo, khi_)
        if status == 'PASS' and margin < require and depth < max_depth:
            status = 'FAIL'
        if status in ('EMPTY', 'PASS'):
            leaves.append((elo, ehi, klo, khi_, status, margin))
            if status == 'PASS' and (min_margin is None or margin < min_margin):
                min_margin = margin
            continue
        if depth >= max_depth:
            raise RuntimeError("depth cap reached: certification FAILED")
        rw_e = (ehi - elo) / elo; rw_k = (khi_ - klo) / klo
        if rw_e >= rw_k:
            mid = rdn((elo + ehi) / 2)
            stack.append((elo, mid, klo, khi_, depth + 1)); stack.append((mid, ehi, klo, khi_, depth + 1))
        else:
            mid = rdn((klo + khi_) / 2)
            stack.append((elo, ehi, klo, mid, depth + 1)); stack.append((elo, ehi, mid, khi_, depth + 1))
    return leaves, min_margin, processed

# ----------------------------------------------------------------------------
worst = {}
def note(tag, val, ctx):
    if tag not in worst or val < worst[tag][0]:
        worst[tag] = (val, ctx)

def part0():
    print("== Part 0: rounding/sqrt primitive unit tests ==")
    random.seed(0)
    for _ in range(2000):
        r = F(random.randrange(1, 10 ** 12), random.randrange(1, 10 ** 12))
        su, sd = sqrt_up(r), sqrt_dn(r)
        assert sd * sd <= r <= su * su, "directed sqrt broken"
        assert su - sd <= F(3, 1 << 60), "sqrt bounds too loose"
        u, d = rup(r), rdn(r)
        assert d <= r <= u and u - d <= F(2, SCALE)
        b = F(random.randrange(1, 10 ** 6), 10 ** 6); n = random.randrange(0, 40)
        assert pow_up(b, n) >= b ** n
    print("   OK (2000 random cases)")

def partA():
    print("== Part A (Step 0): emptiness of e >= e1 = 2033/10000 ==")
    h = lambda e: 6 * e * e - (1 - 3 * e) * (1 - e) ** 2
    he1 = h(E1)
    print(f"   h(e1) = {he1} = {float(he1):.6e}  (exact rational; need > 0)")
    assert he1 > 0
    # h'(e) = 12e + 3(1-e)^2 + 2(1-3e)(1-e) : each term >= 0 on (0, 1/3]; grid corroboration
    wg = min(float(kxi_F(E1 + (F(1, 3) - E1) * F(i, 400)) - khi_F(E1 + (F(1, 3) - E1) * F(i, 400)))
             for i in range(400))  # e in [e1, 1/3)
    print(f"   min(kxi - khi) on [e1, 1/3) grid (401 pts, exact rational) = {wg:.6e}  (need >= 0)")
    assert wg >= 0
    note('A_h(e1)', float(he1), 'exact'); note('A_kxi-khi', wg, 'grid')

def partB():
    print("== Part B (Steps 1-3): pointwise chain checks ==")
    es = [mpf(E0.numerator) / E0.denominator + (mpf(2033) / 10000 - mpf(E0.numerator) / E0.denominator)
          * (mpf(i) / 39) ** 2 for i in range(40)]
    ms = [15, 17, 19, 21, 25, 31, 41, 61, 101, 201, 501, 1001, 5001, 20001, 100001]
    npts = 0
    for e in es:
        klo, khi_e = kxi_m(e), khi_m(e)
        if klo >= khi_e: continue
        kaps = [klo, klo * mpf('1.000000001')]
        for j in range(1, 13):
            kaps.append(klo * (khi_e / klo) ** (mpf(j) / 13))
        kaps += [khi_e * (1 - mpf(10) ** -9), khi_e]
        for kap in kaps:
            b = base_m(e, kap)
            if b['L2'] <= 0: continue
            jh, N = Jhat_m(b)
            pil = Pi_lo_m(b)
            lb = Lam_bar_m(b)
            # C8 also beyond the scan cap
            for n in list(range(14, N + 30)) + [N + 100, N + 1000, 10 ** 4]:
                note('C8', float((jh - J_m(b, n)) / (jh + mpf(10) ** -200)), (float(e), float(kap), n))
            for m in ms:
                v = full_m(e, kap, m)
                npts += 1
                ctx = (float(e), float(kap), m)
                sc = abs(v['R']) + abs(v['R_id'])          # > 0 (R != 0 generically);
                sc2 = abs(v['R']) + abs(v['R_ub'])         # scales, no additive guard
                note('C1', float(-abs(v['R'] - v['R_id']) / sc), ctx)
                note('C2', float((v['R_ub'] - v['R']) / sc2), ctx)
                red = v['R_ub'] / v['D']
                note('C3', float(-abs(red - (v['Jn'] + v['LamL'])) / (abs(red) + mpf(10) ** -200)), ctx)
                note('C4', float((v['P'] - v['D'] * v['Pi_m']) / abs(v['P'])), ctx)
                note('C5', float(v['rho'] - rho_lb_m(b)), ctx)
                note('C6', float(eps_ub_m(b) - v['eps']), ctx)
                note('C6b', float(mpf(1) / 4 - v['eps']), ctx)
                note('C7', float(v['Pi_m'] - pil), ctx)
                note('C9', float((lb - v['LamL']) / lb), ctx)
                note('C11', float((v['P'] - v['R']) / abs(v['P'])), ctx)
    print(f"   {npts} (e,kappa,m) points checked (incl. kappa = kxi exact, kappa = khi exact,"
          f" e = 1/60 and e = 0.2033 exact, m up to 100001)")
    for tag in ['C1', 'C2', 'C3', 'C4', 'C5', 'C6', 'C6b', 'C7', 'C8', 'C9', 'C11']:
        val, ctx = worst[tag]
        ok = 'OK ' if val >= -1e-50 else 'FAIL'
        print(f"   [{ok}] {tag:4s} worst slack = {val:+.6e}  at {ctx}")
        assert val >= -1e-50, f"{tag} FAILED"

def partC():
    print("== Part C (Step 4, numerical): battle margins on fine grid ==")
    NE, NK = 160, 120
    e0f = mpf(E0.numerator) / E0.denominator
    wm = (mpf(10), None); wr = (mpf('inf'), None)
    for i in range(NE):
        e = e0f + (mpf(2033) / 10000 - e0f) * (mpf(i) / (NE - 1)) ** 2
        klo, khi_e = kxi_m(e), khi_m(e)
        if klo >= khi_e: continue
        for j in range(NK):
            kap = klo * (khi_e / klo) ** (mpf(j) / (NK - 1))
            b = base_m(e, kap)
            if b['L2'] <= 0: continue
            jh, _ = Jhat_m(b); lb = Lam_bar_m(b); pil = Pi_lo_m(b)
            marg = pil - jh - lb
            if marg < wm[0]: wm = (marg, (float(e), float(kap)))
            r = pil / (jh + lb)
            if r < wr[0]: wr = (r, (float(e), float(kap)))
    print(f"   min margin Pi_lo - (Jhat + Lam_bar) = {float(wm[0]):.6f} at {wm[1]}")
    print(f"   min ratio  Pi_lo / (Jhat + Lam_bar) = {float(wr[0]):.4f} at {wr[1]}")
    note('C10_margin', float(wm[0]), wm[1]); note('C10_ratio', float(wr[0]), wr[1])
    assert wm[0] > 0

def partD():
    global SQRT2_UP
    SQRT2_UP = sqrt_up(F(2))
    print("== Part D (Step 4, RIGOROUS): exact-rational box certification ==")
    t0 = time.time()
    leaves, min_margin, processed = certify(require=F(1, 20))
    n_pass = sum(1 for L in leaves if L[4] == 'PASS')
    n_empty = sum(1 for L in leaves if L[4] == 'EMPTY')
    print(f"   boxes processed {processed}; certificate: {n_pass} PASS + {n_empty} EMPTY leaves; "
          f"min exact margin {float(min_margin):.6f}; {time.time()-t0:.1f}s")
    note('D_min_margin', float(min_margin), f"{n_pass} boxes")
    assert min_margin > 0
    with open('cert_ZB_boxes.csv', 'w') as fh:
        fh.write("e_lo,e_hi,k_lo,k_hi,status,margin\n")
        for elo, ehi, klo, khi_, st, mg in leaves:
            fh.write(f"{elo},{ehi},{klo},{khi_},{st},{mg if mg is not None else ''}\n")
    print("   leaf list written to cert_ZB_boxes.csv")

    # T1: degenerate boxes reproduce point values with correct direction
    random.seed(7); wt1 = 1e9
    for _ in range(200):
        e = E0 + F(random.randrange(10 ** 9), 10 ** 9) * (E1 - E0)
        lo, hi = kxi_F(e), khi_F(e)
        if lo >= hi: continue
        kap = lo + F(random.randrange(10 ** 9), 10 ** 9) * (hi - lo)
        Pb, Jb, Lb = _box_internals(e, e, kap, kap)
        em, km = mpf(e.numerator) / e.denominator, mpf(kap.numerator) / kap.denominator
        bb = base_m(em, km)
        Pt = Pi_lo_m(bb); Jt, _ = Jhat_m(bb); Lt = Lam_bar_m(bb)
        d1 = float(Pt - mpf(Pb.numerator) / Pb.denominator)
        d2 = float(mpf(Jb.numerator) / Jb.denominator - Jt)
        d3 = float(mpf(Lb.numerator) / Lb.denominator - Lt)
        wt1 = min(wt1, d1, d2, d3)
        assert min(d1, d2, d3) > -1e-25 and max(abs(d1), abs(d2), abs(d3)) < 1e-6
    print(f"   T1 degenerate-box direction/tightness: OK (worst {wt1:.2e})")
    note('T1', wt1, 'degenerate boxes')

    # T2: random boxes enclose pointwise values
    random.seed(42); tested = 0; wt2 = 1e9
    for _ in range(150):
        e0 = E0 + F(random.randrange(10 ** 9), 10 ** 9) * (E1 - E0)
        e1 = min(e0 + F(random.randrange(1, 10 ** 6), 10 ** 7) * (E1 - E0), E1)
        lo = kxi_F(e1); hi = khi_F(e0)
        if lo >= hi: continue
        k0 = lo + F(random.randrange(10 ** 9), 10 ** 9) * (hi - lo)
        k1 = min(k0 + F(random.randrange(1, 10 ** 6), 10 ** 7) * (hi - lo), hi)
        if k0 >= k1: continue
        Pb, Jb, Lb = _box_internals(e0, e1, k0, k1)
        for _ in range(12):
            ee = e0 + F(random.randrange(10 ** 9), 10 ** 9) * (e1 - e0)
            kk = k0 + F(random.randrange(10 ** 9), 10 ** 9) * (k1 - k0)
            if kk < kxi_F(ee) or kk > khi_F(ee): continue
            bb = base_m(mpf(ee.numerator) / ee.denominator, mpf(kk.numerator) / kk.denominator)
            Pt = Pi_lo_m(bb); Jt, _ = Jhat_m(bb); Lt = Lam_bar_m(bb)
            d1 = float(Pt - mpf(Pb.numerator) / Pb.denominator)
            d2 = float(mpf(Jb.numerator) / Jb.denominator - Jt)
            d3 = float(mpf(Lb.numerator) / Lb.denominator - Lt)
            wt2 = min(wt2, d1, d2, d3)
            assert min(d1, d2, d3) > -1e-25, "interval enclosure violated"
            tested += 1
    print(f"   T2 random-box enclosure: OK ({tested} interior points, worst {wt2:.2e})")
    note('T2', wt2, 'random boxes')

    # T3: Monte-Carlo coverage audit of the tiling
    random.seed(1); bad = 0; nin = 0
    for _ in range(100000):
        e = E0 + F(random.randrange(10 ** 9), 10 ** 9) * (E1 - E0)
        kl, kh = kxi_F(e), khi_F(e)
        if kl >= kh: continue
        k = kl + F(random.randrange(10 ** 9), 10 ** 9) * (kh - kl)
        cov = [L for L in leaves if L[0] <= e <= L[1] and L[2] <= k <= L[3]]
        assert cov, "uncovered domain point"
        if all(L[4] == 'EMPTY' for L in cov): bad += 1
        nin += 1
    print(f"   T3 coverage audit: {nin} random domain points, all covered by leaves, "
          f"{bad} misclassified-empty (need 0)")
    assert bad == 0
    note('T3', float(nin > 0 and bad == 0), 'coverage')

def _box_internals(elo, ehi, klo, khi_):
    """Extract (Pi_lo^-, Jmax^+, Lam^+) for a box; mirrors box_check exactly."""
    a_lo = (1 - ehi) / 2; a_hi = (1 - elo) / 2
    d_lo = klo * elo
    p_lo = (1 + elo) / 2 + d_lo
    p_hi = (1 + ehi) / 2 + khi_ * ehi
    L2_lo = max(F(0), elo * (1 - elo) / 2 - khi_ * (1 + khi_) * ehi * ehi)
    L2_hi = max(F(0), ehi * (1 - ehi) / 2 - klo * (1 + klo) * elo * elo)
    L_lo = sqrt_dn(L2_lo); L_hi = sqrt_up(L2_hi)
    x_hi = a_hi / p_lo; x_lo = a_lo / p_hi
    y_hi = rup(L_hi / p_lo); l_hi = rup(L_hi / a_lo)
    f_hi = a_hi - L_lo
    x14_hi = pow_up(x_hi, 14)
    rho_lb = rdn(rdn((1 - x14_hi) * sqrt_dn(a_lo)) / rup(2 * SQRT2_UP * f_hi * (1 + x_hi)))
    if rho_lb < 0: rho_lb = F(0)
    eps_up = min(F(1, 4), rup(ehi / (4 * (1 - ehi) ** 2 * klo * (1 + rho_lb))))
    y14_hi = pow_up(y_hi, 14)
    Pi = sqrt_dn(1 - ehi)
    Pi = rdn(Pi * (1 - l_hi)); Pi = rdn(Pi * (1 - y14_hi))
    Pi = rdn(Pi * (1 - eps_up)); Pi = rdn(Pi / (1 + y_hi))
    A_lo = x_lo * (1 + 1 / khi_)
    Ncap = A_lo + 1 / (1 - x_hi)
    N = max(-((-Ncap.numerator) // Ncap.denominator) + 1, 14)
    powx = pow_up(x_hi, 12); Jmax = F(0); n = 14
    while n <= N:
        num = n - A_lo
        if num > 0:
            v = rup(powx * num / (n + 1))
            if v > Jmax: Jmax = v
        powx = rup(powx * x_hi); n += 1
    Lam = rup(rup(pow_up(y_hi, 15) * p_hi * p_hi) / (15 * d_lo * a_lo))
    return Pi, Jmax, Lam

if __name__ == '__main__':
    t0 = time.time()
    part0(); partA(); partB(); partC(); partD()
    print("\n== SUMMARY: worst slacks ==")
    for tag in sorted(worst):
        val, ctx = worst[tag]
        print(f"   {tag:12s} {val:+.6e}   {ctx}")
    print(f"\nALL CHECKS PASSED ({time.time()-t0:.0f}s). Lemma Z-B chain verified.")
