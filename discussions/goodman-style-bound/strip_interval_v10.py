#!/usr/bin/env python3
"""Rigorous interval verification of the strip criterion, v10: piecewise
Riemann bounds on both the deficit (upper sums; integrand monotone decreasing)
and the two surplus bands (lower sums), plus the hybrid zone-A pairing of v4+.

All arithmetic exact rational.
"""
from fractions import Fraction as F
import sys

def verify_pair(m, r, maxdepth=14, Jsig=5, Ksub=10, KD=10, KB=12):
    n = m - 2*r
    nu = F(n, m)
    half = F(1, 2)
    third = F(1, 3)
    gamma = F(r, m)

    def cell_ok(q1, q2, l1, l2, depth):
        if l1 >= q2 + gamma:
            return True
        sa_lo, sa_up = half - q2, half - q1
        sb_lo, sb_up = nu - q2, nu - q1
        if 2*(n-1)*(l2 - q1) >= (2*r + 1):
            return subdivide(q1, q2, l1, l2, depth)
        if sb_up <= sa_lo:
            return True
        s_lin_lo = (2*m*sa_lo - (r-1)*l2)/(m + r - 1)
        sigmax = min(2*sa_lo, sb_up)
        # sigma = sa_up is admissible only if the linearised pairing condition
        # holds at sa_up for the whole cell:
        if m*(2*sa_lo - sa_up) >= (r-1)*(l2 + sa_up):
            sigmas = [sa_up]
        else:
            sigmas = []
        auto = len(sigmas)
        if not sigmas and s_lin_lo <= sa_up:
            return subdivide(q1, q2, l1, l2, depth) if depth < maxdepth else False
        if s_lin_lo > sa_up:
            sigmas.append(min(s_lin_lo, sigmax))
            auto = 2
            if sigmax > s_lin_lo:
                gap = sigmax - s_lin_lo
                for j in range(1, Jsig + 1):
                    sigmas.append(s_lin_lo + j*gap/Jsig)
                for dv in (gap/24, gap/96):
                    sigmas.insert(-1, sigmax - dv)
                sigmas.sort()

        def zoneA_exact(s0, s1):
            if s1 <= s0:
                return True
            for i in range(Ksub):
                t0 = s0 + i*(s1 - s0)/Ksub
                t1 = s0 + (i+1)*(s1 - s0)/Ksub
                w_lo = 2*sa_lo - t1
                if w_lo <= 0:
                    return False
                if ((l2 + t0)**m)*(w_lo**(r-1)) < (t1**(r-1))*((l2 + 2*sa_up - t0)**m):
                    return False
            return True

        okA = [True]*auto
        for j in range(auto, len(sigmas)):
            okA.append(okA[-1] and zoneA_exact(sigmas[j-1], sigmas[j]))

        for j in range(len(sigmas) - 1, -1, -1):
            if not okA[j]:
                continue
            sig = sigmas[j]
            if sig >= sb_up:
                return True
            if 1 - F(m, n)*(q1 + sig) <= 0:
                return True
            # deficit: KD-piece upper sum (integrand decreasing in s)
            D = F(0)
            for i in range(KD):
                t0 = sig + i*(sb_up - sig)/KD
                t1 = sig + (i+1)*(sb_up - sig)/KD
                br = 1 - F(m, n)*(q1 + t0)
                if br <= 0:
                    continue
                D += (sb_up**(r-1))*(t1 - t0)*((q2 + t0)**(n-1))*br/((l1 + t0)**m)
            if D == 0:
                return True
            # surplus: piecewise lower sums
            S = F(0)
            WL = min(2*sa_lo - sig, sa_lo)
            if WL > 0:
                for i in range(1, KB):
                    t0 = i*WL/KB
                    t1 = (i+1)*WL/KB
                    pc = 1 - q2 - t1
                    qc = q2 + t1
                    if pc <= qc or pc <= 0:
                        continue
                    cp = 1 - F(n, m)*(qc**(n-1))/(pc**n)
                    if cp <= 0:
                        continue
                    S += F(m, n)*(pc**n)*cp*(t1 - t0)*(t0**(r-1))/((l2 + t1)**m)
                if S >= D:
                    return True
            dmax = 2*gamma - (q2 - q1)
            if dmax > 0:
                for i in range(1, KB):
                    d0 = i*dmax/KB
                    d1 = (i+1)*dmax/KB
                    S += F(m, n)*d0*((nu + d0)**(n-1))*(d1 - d0)*((sb_up + d0)**(r-1)) \
                         / ((l2 + sb_up + d1)**m)
                    if S >= D:
                        return True
            if S >= D:
                return True
        if depth >= maxdepth:
            return False
        return subdivide(q1, q2, l1, l2, depth)

    def subdivide(q1, q2, l1, l2, depth):
        if (q2 - q1)*3 >= (l2 - l1)*2:
            qm = (q1 + q2)/2
            return cell_ok(q1, qm, l1, l2, depth+1) and cell_ok(qm, q2, l1, l2, depth+1)
        lm = (l1 + l2)/2
        return cell_ok(q1, q2, l1, lm, depth+1) and cell_ok(q1, q2, lm, l2, depth+1)

    return cell_ok(F(0), third, F(0), half, 0)


def main():
    mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 201
    mmin = int(sys.argv[2]) if len(sys.argv) > 2 else 45
    fails = []
    for m in range(mmin, mmax + 1, 2):
        rs = [r for r in range(2, (m-1)//4 + 1) if m - 2*r > 2*r]
        bad = [r for r in rs if not verify_pair(m, r)]
        if bad:
            fails.append((m, bad))
            print(f"m={m}: FAILED r={bad} ***", flush=True)
        else:
            print(f"m={m}: ok ({len(rs)} r's)", flush=True)
    print(f"\nFailures: {fails if fails else 'NONE'}")
    if not fails:
        print(f"STRIP CRITERION VERIFIED: all residual (m,r), {mmin} <= m <= {mmax}, (q,l) in [0,1/3]x[0,1/2].")


if __name__ == "__main__":
    main()
