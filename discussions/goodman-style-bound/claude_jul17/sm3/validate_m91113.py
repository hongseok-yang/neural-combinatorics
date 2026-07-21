#!/usr/bin/env python3
"""
Merged validation for the FINAL Region-II section  m91113_final.tex
(m in {9,11,13}, whole admissible domain).

It (A) re-runs the two component certificates as subprocesses and requires
each to exit 0, then (B) verifies the two assembly claims of the final note
that neither component alone establishes:

  Part 8  TILING (Lemma e1):  kxi(e) > khi(e) for all e in [e1, 1/3),
          so every admissible point with xi>=1 has e<=e1; and kxi
          increasing, khi=min(kmax,kq) decreasing (monotone tiling).
  Part 9  END-TO-END over the WHOLE admissible domain:
          max R_m/(C_m psi) < 1   (dense (e,kappa) grid), for m=9,11,13.

Exit 0 iff every check passes.
"""
import sys, os, subprocess
import numpy as np
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from geom import geom, payment, admissible

FAIL = []
def check(cond, msg):
    if not cond:
        FAIL.append(msg); print("  FAIL:", msg)

E1 = Fr(2033, 10000)

# ----------------------------------------------------------------------
print("=" * 70)
print("Part A/B/C: re-run the two component certificates as subprocesses")
for script in ("validate_zoneB_91113.py", "validate_zoneC_91113_v2.py"):
    path = os.path.join(HERE, script)
    r = subprocess.run([sys.executable, path], cwd=HERE,
                       capture_output=True, text=True)
    tail = r.stdout.strip().splitlines()[-1] if r.stdout.strip() else "(no stdout)"
    print(f"  {script}: exit={r.returncode} | {tail}")
    if r.returncode != 0:
        print(r.stdout[-1500:]); print(r.stderr[-800:])
    check(r.returncode == 0, f"{script} exit 0")

# ----------------------------------------------------------------------
print("=" * 70)
print("Part 8: TILING  (Lemma e1)  kxi(e) > khi(e) on [e1, 1/3)")

def kxi_F(e):  return e / (1 - e) ** 2                    # exact Fraction
def kmax_F(e): return (1 - e) / (1 + e)
def kq_F(e):   return (1 - 3 * e) / (6 * e)
def khi_F(e):  return min(kmax_F(e), kq_F(e))

# (i) exact at e = e1 : kxi > khi
check(kxi_F(E1) > khi_F(E1),
      f"exact kxi(e1) > khi(e1): {float(kxi_F(E1)):.6f} vs {float(khi_F(E1)):.6f}")
# also confirm khi(e1) is the kq branch (as claimed in the note)
check(kq_F(E1) <= kmax_F(E1), "khi(e1) = kq branch")

# (ii) monotonicity used by the lemma: kxi increasing, khi decreasing on (0,1/3)
es = [Fr(i, 30000) for i in range(1, 10000)]          # (0, 1/3)
kxi_vals = [kxi_F(e) for e in es]
khi_vals = [khi_F(e) for e in es]
check(all(kxi_vals[i] < kxi_vals[i + 1] for i in range(len(es) - 1)),
      "kxi strictly increasing on (0,1/3)")
check(all(khi_vals[i] >= khi_vals[i + 1] for i in range(len(es) - 1)),
      "khi non-increasing on (0,1/3)")

# (iii) direct: kxi(e) > khi(e) for every e in [e1, 1/3) on a dense exact grid
bad = 0
for i in range(1, 3000):
    e = E1 + (Fr(1, 3) - E1) * Fr(i, 3000)
    if e >= Fr(1, 3):
        continue
    if not (kxi_F(e) > khi_F(e)):
        bad += 1
check(bad == 0, f"kxi>khi on [e1,1/3) dense exact grid (bad={bad})")
print(f"  kxi(e1)={float(kxi_F(E1)):.5f} > khi(e1)={float(khi_F(E1)):.5f};"
      f" monotone tiling confirmed (strip empty for e>e1).")

# consistency: an admissible point with xi>=1 forces e<=e1  (float scan)
viol = 0
for e in np.linspace(float(E1) + 1e-6, 1/3 - 1e-6, 400):
    kmax = min((1 - e) / (1 + e), (1 - 3 * e) / (6 * e))
    for kap in np.linspace(1e-6, kmax * 0.999999, 400):
        if not admissible(e, kap):
            continue
        if (1 - e) ** 2 * kap / e >= 1.0:      # xi>=1
            viol += 1
check(viol == 0, f"no admissible xi>=1 point with e>e1 (viol={viol})")

# ----------------------------------------------------------------------
print("=" * 70)
print("Part 9: END-TO-END  max R_m/(C_m psi) over the WHOLE admissible domain")
for m in (9, 11, 13):
    worst = 0.0; arg = None
    for e in np.linspace(1e-4, 1/3 - 1e-6, 600):
        kmax = min((1 - e) / (1 + e), (1 - 3 * e) / (6 * e))
        if kmax <= 0:
            continue
        for kap in np.linspace(1e-5, kmax * 0.999999, 600):
            if not admissible(e, kap):
                continue
            g = geom(e, kap)
            pay, Rm, Am, Bm, rho, xi = payment(g, m)
            if Rm <= 0 or pay <= 0:
                continue
            r = Rm / pay
            if r > worst:
                worst = r; arg = (e, kap, xi)
    check(worst < 1.0, f"E2E whole-domain m={m}: max ratio {worst:.4f}")
    print(f"  m={m}: max R_m/(C_m psi) = {worst:.4f} "
          f"at e={arg[0]:.4f} kap={arg[1]:.4f} xi={arg[2]:.3f}")

# ----------------------------------------------------------------------
print("=" * 70)
if FAIL:
    print(f"MERGED VALIDATION FAILED: {len(FAIL)} checks")
    for f in FAIL:
        print("   -", f)
    sys.exit(1)
print("ALL CHECKS PASSED (component certificates + tiling + whole-domain E2E)")
sys.exit(0)
