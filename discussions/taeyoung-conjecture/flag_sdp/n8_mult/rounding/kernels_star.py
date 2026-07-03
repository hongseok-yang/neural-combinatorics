"""
kernels_star.py -- exact star-defect kernel vectors forced on the Q blocks
by the bipartite equality variety of Delta2.

Derivation (see README_ROUNDING.md):  Delta2 == 0 on EVERY bipartite-
supported graphon (theta_{1,2,4} and C5 both contain odd cycles).  Expanding
the averaging identity at T_2 along "star-deletion" deformations
W_t = T_2 minus u x (v_1 u ... u v_r), |u| = t^a, |v_i| = t, with a large:

  * order-by-order, all slack rows K_{a,b} - star are forced to 0
    (the 21 non-multipartite K-star classes), because the R-side budget
    (2p-1)<R,Gram6(W_t)> is O(t^{2a+2}) structurally while the reachable
    configurations sit at orders < 2a+2;
  * every Q-Gram cell below the threshold is a square that must vanish:
    for each block whose type sigma embeds as
        sigma = K(blk) - star(r*, S)
    (blk: 2-colouring of the type vertices, r* a centre vertex, S a set of
    opposite-side vertices deleted against r*), and each k >= 0, the vector

        phi[blk, r*, S, k] = flag distribution at T_2 where k "defect"
        extras sit on the side opposite to r*, non-adjacent to r* (and
        otherwise behaving like bulk points of that side), remaining
        extras iid bulk,

    is a forced kernel vector:  Q_b phi = 0 for every exact certificate
    that vanishes on the K-star equality rows.  (k=0, S=empty is the
    balanced T_2 vector already harvested.)

Only Q blocks (ground 8) acquire vectors; the R-side cells vanish
structurally at the relevant orders given the already-harvested kernels.
"""
import itertools
from fractions import Fraction

import numpy as np

import common
import build_tables as bt


def _configs(m, edges):
    """Yield (blk, rstar, S) with sigma = K(blk) - star(rstar, S)."""
    E = set((min(a, b), max(a, b)) for (a, b) in edges)

    def adj(i, j):
        return (min(i, j), max(i, j)) in E
    for blk in itertools.product((0, 1), repeat=m):
        for rstar in range(m):
            opp = [j for j in range(m) if blk[j] != blk[rstar]]
            for r in range(len(opp) + 1):
                for S in itertools.combinations(opp, r):
                    Sset = set(S)
                    ok = True
                    for i in range(m):
                        for j in range(i + 1, m):
                            want = (blk[i] != blk[j]) and not (
                                (i == rstar and j in Sset) or
                                (j == rstar and i in Sset))
                            if adj(i, j) != want:
                                ok = False
                                break
                        if not ok:
                            break
                    if ok:
                        yield blk, rstar, tuple(sorted(Sset))


def _extra_patterns(m, blk, rstar, states):
    """Adjacency of each extra (state in 'A','B','D') to the roots and to
    each other.  Returns (root_adj list per extra, side list per extra)."""
    X = blk[rstar]
    side = []
    rad = []
    for st in states:
        if st == "A":
            s = 0
        elif st == "B":
            s = 1
        else:
            s = 1 - X
        side.append(s)
        rad.append([(blk[i] != s) and not (st == "D" and i == rstar)
                    for i in range(m)])
    return rad, side


def star_vec(bm, blk, rstar, S, y):
    """Exact Fraction vector for one config at defect mass y:
    extras iid with P(A-bulk)=1/2, P(B-bulk of the r*-opposite side scaled)
    ... concretely: side X = blk[rstar]; states: X-bulk mass 1/2,
    (1-X)-bulk mass 1/2 - y, defect cell D mass y (side 1-X, non-adjacent
    to r*).  The span over y of these evaluations equals the span of all
    forced y^k-derivative coefficient vectors."""
    m = bm["m"]
    n = (8 - m) // 2
    if m == 2:
        nf, FIDX = bt.NF2, bt.FIDX2
    elif m == 4:
        nf, FIDX = bt.NF4, bt.FIDX1
    elif m == 6:
        nf, FIDX = 64, None
    else:
        return None
    X = blk[rstar]
    # state 'A' = side X bulk, 'B' = side 1-X bulk, 'D' = defect cell
    wts = {"A": Fraction(1, 2), "B": Fraction(1, 2) - y, "D": y}

    def side_of(st):
        return X if st == "A" else 1 - X

    v = [Fraction(0)] * nf
    inner_pairs = list(itertools.combinations(range(n), 2))
    for states in itertools.product("ABD", repeat=n):
        w = Fraction(1)
        for st in states:
            w *= wts[st]
        if w == 0:
            continue
        side = [side_of(st) for st in states]
        rad = [[(blk[i] != side[t]) and not (states[t] == "D" and i == rstar)
                for i in range(m)] for t in range(n)]
        if m == 2:
            pat = 0
            for t in range(n):
                if rad[t][0]:
                    pat |= 1 << (2 * t)
                if rad[t][1]:
                    pat |= 1 << (2 * t + 1)
            for i, (a, b) in enumerate(inner_pairs):
                if side[a] != side[b]:
                    pat |= 1 << (6 + i)
            v[FIDX[pat]] += w
        elif m == 4:
            pat = 0
            for i in range(4):
                if rad[0][i]:
                    pat |= 1 << i
                if rad[1][i]:
                    pat |= 1 << (4 + i)
            if side[0] != side[1]:
                pat |= 1 << 8
            v[FIDX[pat]] += w
        else:
            pat = 0
            for i in range(6):
                if rad[0][i]:
                    pat |= 1 << i
            v[pat] += w
    return v


YS = [Fraction(0), Fraction(1, 8), Fraction(1, 4), Fraction(3, 8),
      Fraction(1, 2)]


def harvest_star(metaQ):
    """Per Q block, list of exact star-defect evaluation vectors (may
    contain duplicates / vectors already in the balanced span;
    span-reduce later)."""
    out = []
    for bm in metaQ:
        m = bm["m"]
        vecs = []
        if m != 0:
            n = (8 - m) // 2
            seen = set()
            for blk, rstar, S in _configs(m, bm["edges"]):
                for y in YS[:n + 1]:
                    v = star_vec(bm, blk, rstar, S, y)
                    if v is None:
                        continue
                    key = tuple(v)
                    if key in seen:
                        continue
                    seen.add(key)
                    vecs.append(v)
        out.append(vecs)
    return out


if __name__ == "__main__":
    import pickle
    cl, coef, SQ, metaQ, pl, res = common.load_everything()
    SV = harvest_star(metaQ)
    print("star-defect vectors per block (first 20):",
          [len(v) for v in SV[:20]])
    with open(common.os.path.join(common.DATA, "star_vecs.pkl"), "wb") as f:
        pickle.dump(SV, f)
    print("saved star_vecs.pkl")
