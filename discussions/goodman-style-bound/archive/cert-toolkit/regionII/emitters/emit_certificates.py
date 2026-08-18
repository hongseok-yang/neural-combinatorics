#!/usr/bin/env python3
"""Emit deterministic Region-II certificate trees as Lean data.

This program deliberately proves nothing.  It replays the corrected July 12b
subdivision strategies and serializes every split and terminal leaf.  Lean
independently checks tree coverage and every terminal inequality.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
import sys
from typing import Optional

sys.dont_write_bytecode = True


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'provenance' / 'regionII_jul12b'
OUTPUT = ROOT / 'OddCycleBound' / 'RegionII' / 'Certificate' / 'Generated.lean'


def load_source(name: str):
    spec = spec_from_file_location(name, SOURCE / f'{name}.py')
    if spec is None or spec.loader is None:
        raise RuntimeError(f'cannot load {name}')
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


zb = load_source('zoneB_certifier')
zc = load_source('zoneC_certifier')


@dataclass(frozen=True)
class Node:
    token: str
    left: Optional['Node'] = None
    right: Optional['Node'] = None


def split(token: str, left: Node, right: Node) -> Node:
    return Node(token, left, right)


def leaf(token: str) -> Node:
    return Node(token)


def zone_b_tree():
    stats = {'verified': 0, 'skipped': 0, 'maxdepth': 0}

    def verify(e1: F, e2: F, k1: F, k2: F, depth: int = 0) -> Node:
        stats['maxdepth'] = max(stats['maxdepth'], depth)
        if k2 <= zb.kappa_xi(e1):
            stats['skipped'] += 1
            return leaf('bSkipZoneC')
        if k1 >= zb.kappa_bar(e1):
            stats['skipped'] += 1
            return leaf('bSkipOutside')

        x_min = zb.x_of(e2, k2)
        x_max = zb.x_of(e1, k1)
        lam_min = 1 - x_max
        a_min = x_min * (1 + k2) / k2
        a_max = x_max * (1 + k1) / k1

        l2_up = 2 * e2 / (1 - e2)
        l_up = zb.sqrt_up(l2_up)
        if l_up >= 1:
            return subdivide(e1, e2, k1, k2, depth)
        l14_up = min(F(1), l2_up**7)

        t_rho = F(1737, 100) * (1 + k1) * e1
        rho_lo = (1 - zb.exp_neg_up(t_rho)) / 4
        eps_up = min(F(1, 4), e2 / (4 * (1 - e2) ** 2 * k1 * (1 + rho_lo)))

        pi_lo = zb.sqrt_lo(1 - e2) * (1 - l_up) * (1 - l14_up) * (1 - eps_up) / (1 + l_up)
        if pi_lo <= 0:
            return subdivide(e1, e2, k1, k2, depth)

        lam_up = (x_max**13 * (2 * e2 / (1 - e2)) ** 6
                  * zb.sqrt_up(2 * e2 / (1 - e2))
                  * (1 - e1) ** 2 / (15 * e1))
        k1_up = x_max**14 * max(F(0), 14 - a_min) / 15
        only_k14 = a_max < 14 and 15 * (14 - a_max) * lam_min >= a_max + 1
        if only_k14:
            k_up = k1_up
        else:
            phi_min = (2 * (1 - e2) * e1 * (1 + k2) ** 2
                       / (k2 * (1 + e2 + 2 * k2 * e2) ** 2))
            w_lo = max(F(0), (zb.sqrt_lo(phi_min * phi_min + 4 * phi_min) - phi_min) / 2)
            k_up = max(k1_up, zb.exp_neg_up(phi_min + 2 * w_lo))

        if pi_lo >= k_up / (x_min * x_min) + lam_up:
            stats['verified'] += 1
            return leaf('bVerified')
        return subdivide(e1, e2, k1, k2, depth)

    def subdivide(e1: F, e2: F, k1: F, k2: F, depth: int) -> Node:
        if depth >= zb.MAX_DEPTH:
            raise RuntimeError(f'unresolved Zone-B box: {e1,e2,k1,k2}')
        if (e2 - e1) / e1 >= (k2 - k1) / k1:
            em = (e1 + e2) / 2
            return split('splitE', verify(e1, em, k1, k2, depth + 1),
                         verify(em, e2, k1, k2, depth + 1))
        km = (k1 + k2) / 2
        return split('splitK', verify(e1, e2, k1, km, depth + 1),
                     verify(e1, e2, km, k2, depth + 1))

    tree = verify(zb.E_LO, zb.E_HI, zb.kappa_xi(zb.E_LO), F(1), 0)
    expected = {'verified': 23, 'skipped': 3, 'maxdepth': 8}
    if stats != expected:
        raise RuntimeError(f'Zone-B regression changed: {stats} != {expected}')
    return tree, stats


def zone_c_tree():
    stats = {'verified': 0, 'skipped': 0, 'bottom': 0, 'maxdepth': 0, 'maxM': 0}

    def verify(e1: F, e2: F, k1: F, k2: F, depth: int = 0) -> Node:
        stats['maxdepth'] = max(stats['maxdepth'], depth)
        if k1 >= min(zc.kappa_xi(e2), zc.kappa_bar(e1)):
            stats['skipped'] += 1
            return leaf('cSkip')
        b = zc.Box(e1, e2, k1, k2)
        if b.f_lo <= 0 or b.s_lo <= 0 or b.s_lo >= b.x_up:
            return subdivide(e1, e2, k1, k2, depth)
        if k1 == 0:
            return bottom_out(b, depth)

        c_lo = b.c_lo()
        if c_lo <= 0:
            return subdivide(e1, e2, k1, k2, depth)
        g2p = b.G2_lo - b.G2_lo**2 / 2
        mplus = 15
        if g2p > 0:
            mplus = max(15, 2 + int(b.q_lo * g2p / b.d_up) + 1)
        if mplus > zc.MCAP:
            mplus = zc.MCAP

        c1_up = 1 / b.a_lo
        c3_up = b.l2_up / b.a_lo
        c2_lo = b.p_lo * b.q_lo / (b.a_up**3)
        xb_up, yb_up, sb_lo = zc.rup(b.x_up), zc.rup(b.y_up), zc.rdown(b.s_lo)
        m = mplus
        xp = zc.pow_up(xb_up, m - 2)
        yp = zc.pow_up(yb_up, m - 2)
        sp = zc.pow_dn(sb_lo, m - 2)
        while m <= zc.MCAP + 1:
            head = c1_up * xp + c3_up * yp
            if head <= c_lo * m:
                stats['maxM'] = max(stats['maxM'], m)
                stats['verified'] += 1
                return leaf(f'cVerified {m}')
            if head - c2_lo * sp > c_lo * m:
                return subdivide(e1, e2, k1, k2, depth)
            xp = zc.rup(xp * xb_up)
            yp = zc.rup(yp * yb_up)
            sp = zc.rdown(sp * sb_lo)
            m += 1
        return subdivide(e1, e2, k1, k2, depth)

    def bottom_out(b, depth: int) -> Node:
        k2, e2 = b.k2, b.e2
        if not 2 * b.rho_lo_up * b.xi_up <= 1:
            return subdivide(b.e1, b.e2, b.k1, k2, depth)
        g2p = b.G2_lo - b.G2_lo**2 / 2
        if g2p <= 0:
            return subdivide(b.e1, b.e2, b.k1, k2, depth)
        c0 = b.q_lo * g2p / e2
        a = b.u_lo * c0
        if not k2 <= a / 2:
            return subdivide(b.e1, b.e2, b.k1, k2, depth)
        lhs = (1 / b.a_lo) * zc.exp_neg_up(a / k2)
        rhs = b.cI0 * k2 * c0
        if lhs <= rhs:
            stats['bottom'] += 1
            stats['verified'] += 1
            return leaf('cBottom')
        return subdivide(b.e1, b.e2, b.k1, k2, depth)

    def subdivide(e1: F, e2: F, k1: F, k2: F, depth: int) -> Node:
        if depth >= zc.MAX_DEPTH:
            raise RuntimeError(f'unresolved Zone-C box: {e1,e2,k1,k2}')
        esplit = (e2 - e1) / e1
        ksplit = (k2 - k1) / k1 if k1 > 0 else F(2)
        if esplit >= ksplit:
            em = (e1 + e2) / 2
            return split('splitE', verify(e1, em, k1, k2, depth + 1),
                         verify(em, e2, k1, k2, depth + 1))
        km = (k1 + k2) / 2 if k1 > 0 else k2 / 2
        return split('splitK', verify(e1, e2, k1, km, depth + 1),
                     verify(e1, e2, km, k2, depth + 1))

    tree = verify(zc.E_LO, zc.E_HI, F(0), F(1), 0)
    expected = {'verified': 2997, 'skipped': 87, 'bottom': 5,
                'maxdepth': 28, 'maxM': 1716}
    if stats != expected:
        raise RuntimeError(f'Zone-C regression changed: {stats} != {expected}')
    return tree, stats


def flatten(root: Node) -> list[str]:
    result: list[str] = []
    stack = [root]
    while stack:
        node = stack.pop()
        result.append(node.token)
        if node.left is not None and node.right is not None:
            stack.append(node.right)
            stack.append(node.left)
    return result


def lean_array(name: str, tokens: list[str]) -> str:
    body = '\n'.join(f'  .{token},' for token in tokens)
    return f'def {name} : Array RegionCertToken := #[\n{body}\n]\n'


def main() -> None:
    btree, bstats = zone_b_tree()
    ctree, cstats = zone_c_tree()
    text = '''import OddCycleBound.RegionII.Certificate.Tree

/-! Deterministically generated by `cert_scripts/regionII/emit_certificates.py`. -/

namespace OddCycleBound.RegionII.Certificate

'''
    text += lean_array('zoneBTokens', flatten(btree)) + '\n'
    text += lean_array('zoneCTokens', flatten(ctree))
    text += '\nend OddCycleBound.RegionII.Certificate\n'
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(text, encoding='utf-8', newline='\n')
    print(f'Zone B: {bstats}; tokens={len(flatten(btree))}')
    print(f'Zone C: {cstats}; tokens={len(flatten(ctree))}')
    print(f'wrote {OUTPUT}')


if __name__ == '__main__':
    main()
