#!/usr/bin/env python3
"""Verification companion to paper_region2_v1.tex (Region-II scalar Huber inequality).

Three layers of checks:
  1. EXACT rational identity checks (fractions module; proof-grade for the
     finitely many algebraic identities used in the paper).
  2. Numerical verification of every inequality step in the zone lemmas
     (mpmath, 60+ dps; NOT a proof -- a safety net against transcription errors).
  3. Global margin scan of the target R_m <= C_m psi(xi, rho) and of the two
     dual certificates on adversarial grids (numerical evidence).

Usage:
    python3 regionII_scalar_checker.py            # layers 1+2 (fast)
    python3 regionII_scalar_checker.py --scan     # + layer 3

Notation follows paper_region2_v1.tex:
  alpha = (1-e)/2, d = kappa*e, q = alpha-d, p = 1-q, L^2 = alpha*e - d(d+e),
  x = alpha/p, tau = q/alpha, y = L/p, ell = L/alpha, u = 1-x, T = m*e,
  A_m = 2L^{m-2}+m k_m(alpha), B_m = 2L^{m-2}+m k_m(L),
  k_m(t) = (p^{m-1}-t^{m-1})/(p+t), R_m = alpha^m+L^m-p q^{m-1},
  C_m = B_m f sqrt(2 alpha) e^2/(4 alpha^2), xi = 4 alpha^2 d/e^2,
  rho = (A_m/B_m) sqrt(alpha)/(2 sqrt2 f), f = alpha - L,
  psi(xi,rho) = min_{0<=v<=1} [rho v^2 + (xi-v+v^2)_+].
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F

from mpmath import mp, mpf, sqrt, log, exp

mp.dps = 60

FAILURES = []


def report(name: str, ok: bool, detail: str = "") -> None:
    print(f"[{'OK ' if ok else 'FAIL'}] {name}" + (f" -- {detail}" if detail else ""))
    if not ok:
        FAILURES.append(name)


# ---------------------------------------------------------------------------
# Layer 1: exact rational identities


def exact_checks() -> None:
    # chart identities and algebraic identities of Section 3, on rational samples
    for e in [F(1, 100), F(1, 60), F(1, 10), F(1, 5), F(3, 10)]:
        for kap in [F(1, 100), F(1, 10), F(1, 3), F(2, 3), F(19, 20)]:
            alpha = (1 - e) / 2
            d = kap * e
            q = alpha - d
            p = 1 - q
            if not (q > F(1, 3)):
                continue
            L2 = p * q - alpha * alpha
            assert L2 == alpha * e - d * (d + e), "L^2 identity"
            assert p == alpha + d + e, "p identity"
            # ceiling algebra: alpha^2+q*alpha-q = (e/2)(kappa(1+e)-(1-e))
            assert alpha * alpha + q * alpha - q == (e / 2) * (kap * (1 + e) - (1 - e))
            # 2q - p = 3(delta - d), delta = (1-3e)/6  [so p < 2q iff d < delta]
            delta = (1 - 3 * e) / 6
            assert 2 * q - p == 3 * (delta - d)
            # q^2 - L^2 = 3 alpha delta - 2 alpha d + 2 d^2 + d e
            assert q * q - L2 == 3 * alpha * delta - 2 * alpha * d + 2 * d * d + d * e
            # xi in chart coordinates
            assert 4 * alpha * alpha * d == (1 - e) ** 2 * kap * e  # xi*e^2
    report("chart + corner identities (exact rational)", True)

    # defect form R_m = alpha^{m-1}(alpha - p tau^{m-1}) + L^m needs tau=q/alpha:
    for e in [F(1, 60), F(1, 7)]:
        for kap in [F(1, 9), F(4, 7)]:
            alpha = (1 - e) / 2
            d = kap * e
            q = alpha - d
            p = 1 - q
            # work with L^2 rational; use even powers only: verify the identity
            # alpha^m - p q^{m-1} = alpha^{m-1}(alpha - p (q/alpha)^{m-1}) exactly
            for m in [5, 15, 21]:
                lhs = alpha**m - p * q ** (m - 1)
                rhs = alpha ** (m - 1) * (alpha - p * (q / alpha) ** (m - 1))
                assert lhs == rhs
    report("defect form identity (exact rational)", True)

    # certificate identities: C_m*xi = sqrt(2a) B_m f d and C_m rho xi^2 = 2 a^3 A_m d^2/e^2
    # (identities in B_m, f, alpha, d, e as formal quantities; check by symbols)
    import sympy as sp

    a_, d_, e_, f_, Am_, Bm_ = sp.symbols("alpha d e f A_m B_m", positive=True)
    Cm = Bm_ * f_ * sp.sqrt(2 * a_) * e_**2 / (4 * a_**2)
    xi = 4 * a_**2 * d_ / e_**2
    rho = (Am_ / Bm_) * sp.sqrt(a_) / (2 * sp.sqrt(2) * f_)
    assert sp.simplify(Cm * xi - sp.sqrt(2 * a_) * Bm_ * f_ * d_) == 0
    assert sp.simplify(Cm * rho * xi**2 - 2 * a_**3 * Am_ * d_**2 / e_**2) == 0
    # lambda = 2 rho xi dual value
    lam = 2 * rho * xi
    val = sp.simplify(Cm * (lam * xi - lam**2 / (4 * (rho + lam))))
    target = sp.simplify(2 * a_**3 * Am_ * d_**2 / e_**2 * (1 + 4 * xi) / (1 + 2 * xi))
    assert sp.simplify(val - target) == 0
    # k_m(-t) - k_m(t) = 2t(p^{m-1}-t^{m-1})/(p^2-t^2) >= 0 (audit gap G1)
    p_, t_ = sp.symbols("p t", positive=True)
    for m in [5, 9, 15]:
        km = lambda z: (p_ ** (m - 1) - z ** (m - 1)) / (p_ + z)
        idm = sp.simplify(km(-t_) - km(t_) - 2 * t_ * (p_ ** (m - 1) - t_ ** (m - 1)) / (p_**2 - t_**2))
        assert idm == 0
    report("certificate + k_m identities (sympy exact)", True)


# ---------------------------------------------------------------------------
# shared numerics


def quantities(e, kappa, m):
    e = mpf(e)
    kappa = mpf(kappa)
    a = (1 - e) / 2
    d = kappa * e
    q = a - d
    p = 1 - q
    L2 = a * e - d * (d + e)
    if L2 < 0 or q <= mpf(1) / 3:
        return None
    L = sqrt(L2)
    f = a - L
    x = a / p
    y = L / p
    ell = L / a
    tau = q / a
    km_a = (p ** (m - 1) - a ** (m - 1)) / (p + a)
    km_L = (p ** (m - 1) - L ** (m - 1)) / (p + L)
    A = 2 * L ** (m - 2) + m * km_a
    B = 2 * L ** (m - 2) + m * km_L
    R = a**m + L**m - p * q ** (m - 1)
    C = B * f * sqrt(2 * a) * e * e / (4 * a * a)
    xi = 4 * a * a * d / (e * e)
    rho = (A / B) * sqrt(a) / (2 * sqrt(2) * f)
    return dict(e=e, kappa=kappa, m=m, a=a, d=d, q=q, p=p, L=L, f=f, x=x, y=y,
                ell=ell, tau=tau, A=A, B=B, R=R, C=C, xi=xi, rho=rho)


def psi_val(xi, rho):
    if xi <= 0:
        return mpf(0)
    if xi < mpf(1) / 4:
        xic = (2 * rho + 1) / (4 * (rho + 1) ** 2)
        if xi < xic:
            vm = (1 - sqrt(1 - 4 * xi)) / 2
            return rho * vm * vm
    return xi - 1 / (4 * (1 + rho))


# ---------------------------------------------------------------------------
# Layer 2: zone lemma chains (ported from the working notes; each named step
# corresponds to a display in paper_region2_v1.tex)


def zoneA_chain() -> None:
    """Zone A (Lemma zoneA): e<=1/60, xi>=1."""
    worst = {}

    def note(k, v):
        worst[k] = min(worst.get(k, mpf(1)), v)

    E0 = mpf(1) / 60
    es = [mpf(10) ** x for x in [-9, -7, -5, -4, -3, mpf("-2.2"), mpf("-1.9")]] + [E0]
    for e in es:
        if e > E0:
            continue
        kmax = (1 - e) / (1 + e)
        kq = (1 - 3 * e) / (6 * e)
        klo = e / (1 - e) ** 2
        khi = min(kmax, kq)
        if klo >= khi:
            continue
        for kf in [mpf(f) / 100 for f in [0, 1, 10, 30, 50, 70, 90, 100]]:
            kappa = klo + (khi - klo) * kf
            for m in [15, 21, 41, 101, 501, 5001, 100001, 2000001]:
                V = quantities(e, kappa, m)
                if V is None or V["R"] <= 0:
                    continue
                eps = e * e / (16 * V["a"] ** 2 * (1 + V["rho"]) * V["d"])
                T = m * e
                z = (m - 2) * (1 - V["x"])
                # posA
                note("posA", V["kappa"] * (m - 1) - V["x"] * (1 + V["kappa"]) + (mpf("2.04") * e) ** 6)
                note("posA-2", V["kappa"] - mpf("0.93") / (m - 1))
                # epsA
                note("epsA", min(mpf(1) / 4, mpf("0.278") * T) - eps)
                # payment reduction (allow 1e-40 fuzz for underflowing 2L^{m-2})
                pay = sqrt(2 * V["a"]) * V["B"] * V["f"] * (V["d"] - e * e / (16 * V["a"] ** 2 * (1 + V["rho"])))
                pay_lb = sqrt(1 - e) * m * V["d"] * V["a"] * V["p"] ** (m - 2) * (1 - V["ell"]) * (
                    1 - V["y"] ** (m - 1)) * (1 - eps) / (1 + V["y"])
                note("payLB", (pay - pay_lb) / pay + mpf(10) ** -40)
                # defect reduction
                R_ub = V["a"] ** (m - 1) * ((m - 1) * V["d"] / V["x"] - (V["d"] + e)) + (V["a"] * e) ** (mpf(m) / 2)
                note("defUB", (R_ub - V["R"]) / abs(V["R"]))
                # battle ingredients
                note("aux-a", mpf("0.0822") * z - mpf("2.034") * (1 + kappa) * e)
                note("aux-b", mpf("0.1684") * z - mpf("0.278") * T)
                note("aux-c", (2 + 1 / kappa) / m - mpf("11.08") * e / (z + mpf("7.8") * e))
                # final
                note("FINAL", (pay - V["R"]) / pay)
    ok = all(v >= 0 for v in worst.values())
    report("Zone A chain (numerical, all steps)", ok,
           "; ".join(f"{k}:{float(v):.2e}" for k, v in sorted(worst.items())))


def zoneCsmall_chain() -> None:
    """Zone C small-e (Lemma zoneC-small): e<=1/60, xi<=1."""
    worst = {}

    def note(k, v):
        worst[k] = min(worst.get(k, mpf(1)), v)

    E0 = mpf(1) / 60
    for e in [mpf(10) ** x for x in [-8, -6, -4, -3, mpf("-2.2")]] + [E0]:
        if e > E0:
            continue
        kxi = e / (1 - e) ** 2
        for kf in [mpf(f) / 100 for f in [1, 10, 30, 60, 90, 100]]:
            kappa = kxi * kf
            m0 = int(mpf("0.93") / kappa) | 1
            for m in [max(15, m0 - 2), m0 + 2, 2 * m0 + 1, 10 * m0 + 1]:
                V = quantities(e, kappa, m)
                if V is None or V["R"] <= 0 or V["xi"] > 1:
                    continue
                t = (m - 1) * log(1 / V["tau"]) - log(1 / V["x"])
                z = kappa * m
                T = m * e
                note("C-mT", T - mpf("0.899"))
                note("C-m55", m - 55)
                # paper claims the branch 2*rho*xi > 1 is EMPTY on this zone:
                note("C-empty", 1 - 2 * V["rho"] * V["xi"])
                note("C-rhobound", mpf("0.3782") - V["rho"])
                pay = 2 * V["a"] ** 3 * V["A"] * kappa**2
                Dub = V["a"] ** m * min(mpf(1), max(t, mpf(0))) + V["L"] ** m
                note("C-defUB", (Dub - V["R"]) / V["R"])
                note("C-t-ub", e * (mpf("2.0351") * z - mpf("1.9048")) - t)
                note("C-battle", mpf("0.39") * kappa**2 * m
                     - exp(-mpf("1.8355") * T) * min(mpf(1), max(t, mpf(0))))
                note("C-FINAL", (pay - V["R"]) / pay)
    ok = all(v >= 0 for v in worst.values())
    report("Zone C small-e chain (numerical, all steps)", ok,
           "; ".join(f"{k}:{float(v):.2e}" for k, v in sorted(worst.items())))


# ---------------------------------------------------------------------------
# Layer 3: global scan


def corner_chain() -> None:
    """Turan-corner lemma (paper Lemma turan): delta < 1/2000, 0 < d < delta."""
    worst = {}

    def note(k, v):
        worst[k] = min(worst.get(k, mpf(1)), v)

    for dexp in [mpf("-3.31"), -4, -5, -7, -9]:
        delta = mpf(10) ** dexp
        if delta > mpf(1) / 2000:
            continue
        e = mpf(1) / 3 - 2 * delta
        for df in [mpf(x) / 1000 for x in [50, 300, 600, 900, 999, 1000]]:
            d = delta * df * (1 - mpf(10) ** -12)
            kappa = d / e
            V = quantities(e, kappa, m=15)
            if V is None:
                continue
            a, q, p, L = V["a"], V["q"], V["p"], V["L"]
            x, s, y, ell = V["x"], q / p, V["y"], V["ell"]
            # standing bounds
            note("T-x", mpf("0.50113") - x)
            note("T-q2L2-lo", (q * q - L * L) - mpf("0.66") * delta)
            note("T-q2L2-up", mpf("1.003") * delta - (q * q - L * L))
            note("T-f", V["f"] - mpf("1.498") * delta)
            note("T-f-up", mpf("2.004") * delta - V["f"])
            note("T-ell", (1 - ell) - 0)
            note("T-ell-up", mpf("6.1") * delta - (1 - ell))
            G2 = ell * ell * (1 - (y / s) ** 13)
            note("T-G2", G2 - 37 * delta)
            for m in [15, 21, 61, 301, 5001]:
                W = quantities(e, kappa, m)
                R = W["R"]
                N = d - (q * q - L * L) * ell ** (m - 1) / (q + L)
                note("T-N", 10 * m * delta**2 - N)
                D = (x ** (m - 2) + ell * ell * y ** (m - 2)
                     - (p * q / (a * a)) * s ** (m - 2)) / a
                if N > 0:
                    note("T-MVT", (m - 2) * x ** (m - 3) * N / (p * a) - D)
                if R > 0:
                    note("T-force", (m - 2) * d - mpf("12.3") * delta)
                    xi = W["xi"]
                    x14, y14 = x**14, y**14
                    cI = 2 * (1 - x14) * (1 - y14) * kappa**2 * (1 + 4 * xi) / \
                        ((1 + x) * (1 + y) * (1 + 2 * xi))
                    cII = sqrt(2 * a) * (1 - y14) * W["f"] * d * (4 * xi + 1) / \
                        (a**3 * (1 + y) * (4 * xi + 2))
                    note("T-cI", cI - mpf("7.9") * d * d)
                    note("T-cII", cII - mpf("10.9") * delta * d)
                    note("T-BATTLE", min(cI, cII) * m - D)
    ok = all(v >= 0 for v in worst.values())
    report("Turan-corner chain (numerical, all steps)", ok,
           "; ".join(f"{k}:{float(v):.2e}" for k, v in sorted(worst.items())))


def global_scan() -> None:
    worst = (mpf(1), None)
    both_fail = 0
    tested = 0
    import itertools
    es = [mpf(10) ** x for x in [-10, -8, -6, -5, -4, -3, -2, mpf("-1.5"), -1]] + \
         [mpf(x) / 100 for x in [15, 20, 25, 28, 30, 32, 33]]
    for e in es:
        if e >= mpf(1) / 3:
            continue
        kmax = (1 - e) / (1 + e)
        kq = (1 - 3 * e) / (6 * e)
        khi = min(kmax, kq)
        for kf in [mpf(f) / 1000 for f in [1, 5, 20, 80, 200, 400, 600, 800, 950, 999]]:
            kappa = khi * kf
            for m in [15, 17, 21, 31, 61, 151, 501, 2001, 10001, 100001, 1000001]:
                V = quantities(e, kappa, m)
                if V is None or V["R"] <= 0:
                    continue
                tested += 1
                paym = V["C"] * psi_val(V["xi"], V["rho"])
                rel = (paym - V["R"]) / paym
                if rel < worst[0]:
                    worst = (rel, (float(e), float(kappa), m))
                lam = min(mpf(1), 2 * V["rho"] * V["xi"])
                p1 = V["C"] * (lam * V["xi"] - lam**2 / (4 * (V["rho"] + lam)))
                p2 = V["C"] * (V["xi"] - 1 / (4 * (1 + V["rho"])))
                if p1 < V["R"] and p2 < V["R"]:
                    both_fail += 1
    report("global scan: target margin", worst[0] > 0,
           f"{tested} positive-defect pts, min rel margin {float(worst[0]):.3e} at {worst[1]}")
    report("global scan: certificate coverage", both_fail == 0,
           f"points where both certificates fail: {both_fail}")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--scan", action="store_true")
    args = ap.parse_args()
    exact_checks()
    zoneA_chain()
    zoneCsmall_chain()
    corner_chain()
    if args.scan:
        global_scan()
    print()
    if FAILURES:
        print("FAILURES:", FAILURES)
        raise SystemExit(1)
    print("All checks passed.")


if __name__ == "__main__":
    main()
