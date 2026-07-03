"""
common.py -- shared loading utilities for the exact rounding of the
multiplier flag SDP certificate (Delta2 >= c + SOS_8 + (2p-1) SOS_6).

Layout of blocks:
  Q blocks (170, ground 8): [m=0 (nf=11)] + [m=2 nonedge, m=2 edge (nf=120)]
     + [11 x m=4 (nf=272), build_tables.TYPES4 order]
     + [156 x m=6 (nf=64), flagalg.enumerate_types(6) order].
  R blocks (14, ground 6):  [m'=0 (nf=4)] + [m'=2 nonedge/edge (nf=20)]
     + [11 x m'=4 (nf=16), TYPES4 order].
"""
import os, sys, pickle
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
MULTDIR = os.path.dirname(HERE)
N8DIR = os.path.join(os.path.dirname(MULTDIR), "n8")
sys.path.insert(0, MULTDIR)
sys.path.insert(0, N8DIR)

import multlib as ml
import n8lib
import build_tables as bt
import solve8

DATA = os.path.join(HERE, "data")
os.makedirs(DATA, exist_ok=True)

SNAP = os.path.join(DATA, "snapshot_result.pkl")

_cache = {}


def load_everything():
    """cl, coef, SQ (list of 170 sparse tables), metaQ, pl (mult payload),
    result snapshot."""
    if "all" in _cache:
        return _cache["all"]
    cl, coef, SQ, metaQ = solve8.load_blocks("m0m2m4m6")
    pl = ml.build(verbose=False)
    with open(SNAP, "rb") as f:
        res = pickle.load(f)
    _cache["all"] = (cl, coef, SQ, metaQ, pl, res)
    return _cache["all"]


def tri_of(Q):
    """our tri convention: k=TRI(i,j)=j(j+1)/2+i (i<=j); off-diag entries
    store M_ij+M_ji, so <Q,M> = S[h] . tri_of(Q) with tri_of(Q)[k]=Q_ij."""
    nf = Q.shape[0]
    tri = np.empty(nf * (nf + 1) // 2)
    for j in range(nf):
        for i in range(j + 1):
            tri[bt.TRI(i, j)] = Q[i, j]
    return tri


def slacks_float(coef, SQ, MultS, Qs, Rs):
    total = np.zeros(len(coef))
    for Sb, Q in zip(SQ, Qs):
        total += Sb @ tri_of(Q)
    for Mb, R in zip(MultS, Rs):
        total += Mb @ tri_of(R)
    return coef - total
