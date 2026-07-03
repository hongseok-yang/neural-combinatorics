"""
flagfast.py
===========
Optimized flag multiplication-table builder (drop-in for
flagalg.flag_multiplication_tables) with precomputed flag-key lookup and
adjacency caching.  Produces IDENTICAL tables to flagalg (verified in
test_flagfast) but fast enough for N=7.
"""
import itertools
import numpy as np
import networkx as nx
import flagalg as fa


def build_tables(sigma, ell, N, graphs):
    m = sigma.number_of_nodes()
    r = ell - m
    flags = fa.enumerate_flags(sigma, ell)
    flag_keys = [fa._flag_key_fixing_type(
        tuple(sorted((min(u, v), max(u, v)) for u, v in F.edges())), m, ell)
        for F in flags]
    key_to_idx = {k: i for i, k in enumerate(flag_keys)}
    nf = len(flags)
    sigma_ordered = set(tuple(sorted(e)) for e in sigma.edges())

    # precompute permutations of extra positions (for flag canonicalization)
    extra_pos = list(range(m, ell))
    extra_perms = list(itertools.permutations(range(r)))

    Mtabs = []
    for H in graphs:
        A = fa._adj(H)
        V = list(range(A.shape[0]))
        Mt = np.zeros((nf, nf))
        denom = 0
        for s in itertools.permutations(V, m):
            # induced labeled subgraph on s must equal sigma
            sedge = set()
            good = True
            for a in range(m):
                for b in range(a + 1, m):
                    if A[s[a], s[b]]:
                        sedge.add((a, b))
            if sedge != sigma_ordered:
                continue
            rest = [v for v in V if v not in s]
            # precompute flag index for each ordered r-subset of rest
            for A_ in itertools.permutations(rest, r):
                ia = _flag_idx(A, s, A_, m, ell, r, extra_perms, key_to_idx)
                remaining = [v for v in rest if v not in A_]
                for B_ in itertools.permutations(remaining, r):
                    ib = _flag_idx(A, s, B_, m, ell, r, extra_perms, key_to_idx)
                    Mt[ia, ib] += 1.0
                    denom += 1
        if denom > 0:
            Mt /= denom
        Mtabs.append(Mt)
    return flags, flag_keys, Mtabs


def _flag_idx(A, s, ext, m, ell, r, extra_perms, key_to_idx):
    verts = list(s) + list(ext)
    # edges of induced flag on verts, positions 0..ell-1
    E = []
    for a in range(ell):
        va = verts[a]
        for b in range(a + 1, ell):
            if A[va, verts[b]]:
                E.append((a, b))
    # canonical key permuting extra positions (m..ell-1) only
    best = None
    for perm in extra_perms:
        mapping = list(range(m)) + [m + perm[k] for k in range(r)]
        newE = tuple(sorted((min(mapping[u], mapping[v]), max(mapping[u], mapping[v]))
                            for (u, v) in E))
        if best is None or newE < best:
            best = newE
    return key_to_idx[best]
