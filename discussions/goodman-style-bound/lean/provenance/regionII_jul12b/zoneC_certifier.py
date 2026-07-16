#!/usr/bin/env python3
"""Exact rational-arithmetic certificate for Zone C-moderate of regionII_corrected_solution.tex.

CLAIM CERTIFIED: for all admissible (q, alpha, m) with
    e = 1-2 alpha in [1/60, 1/3 - 1/1000],   xi <= 1,   m >= 15,   R_m > 0,
an admissible dual certificate pays: lambda = 2 rho_lo xi when this is at
most 1, and lambda = 1 otherwise; hence R_m <= C_m psi(xi, rho).
(The remaining sliver e in (1/3 - 1/1000, 1/3) is the Turan-corner lemma,
proved separately in the paper.)

INGREDIENTS (all proved in the paper; notation of regionII_corrected_solution.tex):

(a) Exact three-geometric defect (uses L^2 = pq - alpha^2 exactly):
      R_m/(alpha^3 p^{m-2}) = (1/alpha) x^{m-2} + (l^2/alpha) y^{m-2}
                               - (pq/alpha^3) s^{m-2},   s = q/p,  y < s < x < 1,
    and pq/alpha^3 = 1/alpha + l^2/alpha identically.

(b) Secant positivity gate: R_m > 0 implies (x/s)^{m-2} > 1 + G2 with
      G2 := l^2 (1 - (y/s)^{13})   (m >= 15), hence, using
      ln(x/s) = ln(alpha/q) <= d/q and ln(1+t) >= t - t^2/2,
      m - 2 > q (G2 - G2^2/2) / d =: Mhat(d).

(c) Payments, m-free-gated by rho_lo := (1-x^14) sqrt(alpha)/(2 sqrt2 f (1+x)) <= rho:
      if 2 rho_lo xi <= 1:  payment/(alpha^3 p^{m-2}) >= cI * m,
         cI = 2 (1-x^14)(1-y^14) kappa^2 (1+4xi)/((1+x)(1+y)(1+2xi));
      if 2 rho_lo xi >  1:  payment/(alpha^3 p^{m-2}) >= cII * m,
         cII = sqrt(2 alpha)(1-y^14) f d (4xi+1)/(alpha^3 (1+y)(4xi+2)).

(d) Tail: both positive defect terms decrease in m, payment increases; so if
      (1/alpha)_up x_up^{m-2} + (l^2/alpha)_up y_up^{m-2} <= c_lo * m
    at some m, all larger m pass.

(e) kappa -> 0 bottom-out (k1 = 0 boxes): pointwise, R_m > 0 forces
      m - 2 > Mhat(d) >= q_lo (G2 - G2^2/2)_lo / (kappa e2) =: C0/kappa,
    so defect <= (1/alpha)_up x_up^{m-2} <= c1_up exp(-u_lo C0/kappa), while
    payment >= c0_lo kappa^2 m >= c0_lo C0 kappa
    (case I; the box is arranged to be case I).  Since
    exp(-a/kappa)/kappa is increasing for kappa <= a (the implementation uses
    the stronger gate kappa <= a/2), a single check at kappa = k2 certifies all
    kappa in (0, k2].

All arithmetic is fractions.Fraction; sqrt via integer isqrt bracketing;
exp(-t) upper-bracketed by 1/(partial sum of e^t).  No floating point.
Run:  python3 zoneC_certifier.py    (exit 0 iff certified)
"""
from __future__ import annotations

from fractions import Fraction as F
from math import isqrt

E_LO = F(1, 60)
E_HI = F(1, 3) - F(1, 1000)   # corner sliver handled by the Turan-corner lemma
MAX_DEPTH = 64
MCAP = 500000
DEN = 10**12
STATS = {"verified": 0, "skipped": 0, "bottom": 0, "maxdepth": 0, "maxM": 0}
SCALE = 10**30


def sqrt_lo(t: F) -> F:
    if t <= 0:
        return F(0)
    n = (t.numerator * SCALE * SCALE) // t.denominator
    return F(isqrt(n), SCALE)


def sqrt_up(t: F) -> F:
    if t <= 0:
        return F(0)
    n = (t.numerator * SCALE * SCALE) // t.denominator
    return F(isqrt(n) + 1, SCALE)


def rdown(t: F, den: int = DEN) -> F:
    return F((t.numerator * den) // t.denominator, den)


def rup(t: F, den: int = DEN) -> F:
    return F(-((-t.numerator * den) // t.denominator), den)


def exp_neg_up(t: F) -> F:
    """Upper bound for exp(-t), t >= 0 (rational)."""
    assert t >= 0
    t = rdown(t, 10**9)
    if t > 400:
        t = F(400)  # exp(-400) still astronomically small; keep fractions sane
    s, term = F(1), F(1)
    k = 1
    while term > F(1, 10**50) and k < 500:
        term = term * t / k
        s += term
        k += 1
    return F(1) / s


def pow_up(base: F, n: int) -> F:
    """Upper bound of base^n (0<=base<=1) with directed rounding each step."""
    r, b = F(1), rup(base)
    while n:
        if n & 1:
            r = rup(r * b)
        b = rup(b * b)
        n >>= 1
    return r


def pow_dn(base: F, n: int) -> F:
    r, b = F(1), rdown(base)
    while n:
        if n & 1:
            r = rdown(r * b)
        b = rdown(b * b)
        n >>= 1
    return r


def kappa_xi(e: F) -> F:
    return e / (1 - e) ** 2


def kappa_bar(e: F) -> F:
    return min((1 - e) / (1 + e), (1 - 3 * e) / (6 * e))


class Box:
    """Conservative interval data for a box [e1,e2] x [k1,k2]."""

    def __init__(self, e1, e2, k1, k2):
        self.e1, self.e2, self.k1, self.k2 = e1, e2, k1, k2
        self.a_lo, self.a_up = (1 - e2) / 2, (1 - e1) / 2
        self.d_lo, self.d_up = k1 * e1, k2 * e2
        self.q_lo = max(self.a_lo - self.d_up, F(1, 3))
        self.q_up = self.a_up - self.d_lo
        self.p_lo, self.p_up = 1 - self.q_up, 1 - self.q_lo
        self.x_lo = (1 - e2) / (1 + e2 + 2 * k2 * e2)
        self.x_up = (1 - e1) / (1 + e1 + 2 * k1 * e1)
        self.s_lo, self.s_up = self.q_lo / self.p_up, self.q_up / self.p_lo
        self.L2_lo = max(F(0), self.a_lo * e1 - self.d_up * (self.d_up + e2))
        self.L2_up = min(self.a_up * e2, self.q_up**2)
        self.L_lo = sqrt_lo(self.L2_lo)
        self.L_up = min(sqrt_up(self.L2_up), self.q_up)
        self.y_up = min(self.L_up / self.p_lo, F(1, 2), self.s_up)
        self.l2_lo = self.L2_lo / (self.a_up**2)
        self.l2_up = min(self.L2_up / (self.a_lo**2), F(1))
        self.delta_lo = (1 - 3 * e2) / 6
        # Lemma "Frontier-gap inequalities": f >= d + delta pointwise.
        self.f_lo = max(self.a_lo - self.L_up, self.d_lo + self.delta_lo)
        self.f_up = self.a_up - self.L_lo
        self.xi_lo = (1 - e2) ** 2 * k1 / e2
        self.xi_up = min(F(1), (1 - e1) ** 2 * k2 / e1)
        self.x14_lo = rdown(self.x_lo, 10**6) ** 14
        self.x14_up = min(F(1), rup(self.x_up, 10**6) ** 14)
        self.y14_up = min(F(1), rup(self.y_up, 10**6) ** 14)
        # u = 1 - x
        self.u_lo = 1 - self.x_up
        # G2 lower bound
        ys_up = min(rup(self.y_up / self.s_lo, 10**6), F(1))
        self.G2_lo = self.l2_lo * (1 - ys_up**13)
        # rho_lo bracket
        self.rho_lo_up = (1 - self.x14_lo) * sqrt_up(self.a_up) / \
            (2 * sqrt_lo(F(2)) * self.f_lo * (1 + self.x_lo))
        self.rho_lo_lo = (1 - self.x14_up) * sqrt_lo(self.a_lo) / \
            (2 * sqrt_up(F(2)) * self.f_up * (1 + self.x_up))
        # payment coefficients
        self.cI = 2 * (1 - self.x14_up) * (1 - self.y14_up) * k1 * k1 * \
            (1 + 4 * self.xi_lo) / ((1 + self.x_up) * (1 + self.y_up) * (1 + 2 * self.xi_lo))
        self.cII = sqrt_lo(2 * self.a_lo) * (1 - self.y14_up) * self.f_lo * self.d_lo * \
            (4 * self.xi_lo + 1) / (self.a_up**3 * (1 + self.y_up) * (4 * self.xi_lo + 2))
        # cI without kappa^2 (for the bottom-out, pointwise kappa)
        self.cI0 = 2 * (1 - self.x14_up) * (1 - self.y14_up) / \
            ((1 + self.x_up) * (1 + self.y_up))

    def c_lo(self):
        use_I = 2 * self.rho_lo_up * self.xi_up <= 1
        use_II = 2 * self.rho_lo_lo * self.xi_lo > 1
        if use_I:
            return self.cI
        if use_II:
            return self.cII
        return min(self.cI, self.cII)


def verify_box(e1: F, e2: F, k1: F, k2: F, depth: int = 0) -> bool:
    STATS["maxdepth"] = max(STATS["maxdepth"], depth)
    if k1 >= min(kappa_xi(e2), kappa_bar(e1)):
        STATS["skipped"] += 1
        return True
    B = Box(e1, e2, k1, k2)
    if B.f_lo <= 0 or B.s_lo <= 0 or B.s_lo >= B.x_up:
        return subdivide(e1, e2, k1, k2, depth)

    if k1 == 0:
        return bottom_out(B, depth)

    c_lo = B.c_lo()
    if c_lo <= 0:
        return subdivide(e1, e2, k1, k2, depth)

    # positivity gate (secant): m-2 > q_lo (G2 - G2^2/2)_lo / d_up
    G2p = B.G2_lo - B.G2_lo**2 / 2
    Mplus = 15
    if G2p > 0:
        Mplus = max(15, 2 + int(B.q_lo * G2p / B.d_up) + 1)
    if Mplus > MCAP:
        # positive defect needs m > MCAP; tail from Mplus via battle at Mplus:
        Mplus = MCAP  # fall through to loop which starts at MCAP and uses tail

    c1_up = 1 / B.a_lo
    c3_up = B.l2_up / B.a_lo
    c2_lo = B.p_lo * B.q_lo / (B.a_up**3)
    xb_up, yb_up, sb_lo = rup(B.x_up), rup(B.y_up), rdown(B.s_lo)

    m = Mplus
    xp = pow_up(xb_up, m - 2)
    yp = pow_up(yb_up, m - 2)
    sp = pow_dn(sb_lo, m - 2)
    while m <= MCAP + 1:
        head = c1_up * xp + c3_up * yp
        if head <= c_lo * m:
            STATS["maxM"] = max(STATS["maxM"], m)
            STATS["verified"] += 1
            return True
        if head - c2_lo * sp > c_lo * m:
            return subdivide(e1, e2, k1, k2, depth)
        xp = rup(xp * xb_up)
        yp = rup(yp * yb_up)
        sp = rdown(sp * sb_lo)
        m += 1
    return subdivide(e1, e2, k1, k2, depth)


def bottom_out(B: Box, depth: int) -> bool:
    """kappa in (0, k2]: certify via pointwise forcing m-2 > C0/kappa and
    case-I payment c0 kappa^2 m (require the box to be case I for all kappa <= k2)."""
    k2, e2 = B.k2, B.e2
    # case-I gate must hold across the box: 2 rho_lo xi <= 1 with xi <= xi_up
    if not (2 * B.rho_lo_up * B.xi_up <= 1):
        return subdivide(B.e1, B.e2, B.k1, k2, depth)
    G2p = B.G2_lo - B.G2_lo**2 / 2
    if G2p <= 0:
        return subdivide(B.e1, B.e2, B.k1, k2, depth)
    C0 = B.q_lo * G2p / e2              # m - 2 > C0/kappa pointwise
    a = B.u_lo * C0                     # defect <= c1_up exp(-a/kappa)
    if not (k2 <= a / 2):               # stronger than the range k <= a for exp(-a/k)/k
        return subdivide(B.e1, B.e2, B.k1, k2, depth)
    # single check at kappa = k2:  c1_up exp(-a/k2) <= cI0 * k2^2 * 15... payment
    # >= cI0 kappa^2 (1+4xi)/(1+2xi) m >= cI0 kappa^2 m >= cI0 kappa^2 (C0/kappa)
    # -- use m > C0/kappa for the payment too: payment >= cI0 kappa C0. Better.
    c1_up = 1 / B.a_lo
    lhs = c1_up * exp_neg_up(a / k2)
    rhs = B.cI0 * k2 * C0               # payment >= cI0 * kappa^2 * m >= cI0 kappa C0
    # monotonicity: exp(-a/k)*k^{-1} increasing in k for k <= a: check k2 <= a: yes (<= a/2)
    if lhs <= rhs:
        STATS["bottom"] += 1
        STATS["verified"] += 1
        return True
    return subdivide(B.e1, B.e2, B.k1, k2, depth)


def subdivide(e1, e2, k1, k2, depth) -> bool:
    if depth >= MAX_DEPTH:
        print(f"UNRESOLVED BOX: e in [{float(e1):.10f},{float(e2):.10f}], "
              f"kappa in [{float(k1):.4e},{float(k2):.4e}]")
        return False
    em = (e1 + e2) / 2
    km = (k1 + k2) / 2 if k1 > 0 else k2 / 2
    esplit = (e2 - e1) / e1
    ksplit = (k2 - k1) / k1 if k1 > 0 else F(2)
    if esplit >= ksplit:
        return verify_box(e1, em, k1, k2, depth + 1) & verify_box(em, e2, k1, k2, depth + 1)
    return verify_box(e1, e2, k1, km, depth + 1) & verify_box(e1, e2, km, k2, depth + 1)


def main() -> None:
    import sys
    sys.setrecursionlimit(10**6)
    ok = verify_box(E_LO, E_HI, F(0), F(1), 0)
    print(f"boxes verified: {STATS['verified']} (bottom-out: {STATS['bottom']}), "
          f"skipped: {STATS['skipped']}, max depth: {STATS['maxdepth']}, "
          f"max battle m: {STATS['maxM']}")
    print("ZONE-C-MODERATE CERTIFIED on e <= 1/3 - 1/1000 (exact rational arithmetic)"
          if ok else "CERTIFICATION FAILED")
    raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    main()
