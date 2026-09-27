#!/usr/bin/env python3
"""Independent exact audit and optional Lean-witness export.

No import from either original checker is used. Graph normalization is generated
by breadth-first search using adjacent vertex transpositions. Matrix positivity
is checked by rational LDL^T factorization and exact entrywise reconstruction.
Targets and root-probability polynomials are expanded by convolution, not by the
original subset-enumeration routine. Only Python's standard library is used.

This is an arithmetic verifier, not a Lean proof. See the blueprint for the
separate soundness statements that the Lean kernel must eventually check.
"""
from __future__ import annotations
import argparse
from collections import deque
from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path

N = 6
EDGES = [(i, j) for i in range(N) for j in range(i + 1, N)]
INDEX = {e: j for j, e in enumerate(EDGES)}
K = 1 << len(EDGES)
NAMES = ('mean_two', 'mean_three', 'negative_majority', 'positive_majority')
DEN = 90315258984881964711936


def check(ok, message):
    if not ok:
        raise AssertionError(message)


def mask(es):
    value = 0
    for i, j in es:
        check(0 <= i < N and 0 <= j < N and i != j, 'invalid edge')
        bit = 1 << INDEX[tuple(sorted((i, j)))]
        check(not value & bit, 'repeated formal edge')
        value |= bit
    return value


def relabel(g, p):
    ans = 0
    for bit, (i, j) in enumerate(EDGES):
        if (g >> bit) & 1:
            ans |= 1 << INDEX[tuple(sorted((p[i], p[j])))]
    return ans


def normal_forms():
    normal = [-1] * K
    witness = [None] * K
    representatives = []
    swaps = []
    for a in range(5):
        p = list(range(N))
        p[a], p[a + 1] = p[a + 1], p[a]
        swaps.append(p)
    for representative in range(K):
        if normal[representative] != -1:
            continue
        representatives.append(representative)
        normal[representative] = representative
        witness[representative] = list(range(N))
        todo = deque([representative])
        while todo:
            g = todo.popleft()
            for swap in swaps:
                h = relabel(g, swap)
                if normal[h] == -1:
                    normal[h] = representative
                    witness[h] = [witness[g][swap[i]] for i in range(N)]
                    todo.append(h)
                else:
                    check(normal[h] == representative, 'overlapping components')
    for g in range(K):
        check(sorted(witness[g]) == list(range(N)), 'not a permutation')
        check(relabel(g, witness[g]) == normal[g], 'incorrect relabelling witness')
    check(len(representatives) == 156, 'unexpected number of normal forms')
    return normal, witness, representatives


def plus(*terms):
    result = {}
    for coefficient, poly in terms:
        for g, c in poly.items():
            result[g] = result.get(g, 0) + coefficient * c
    return {g: c for g, c in result.items() if c}


def product(p, q):
    ans = {}
    for a, ca in p.items():
        for b, cb in q.items():
            check(not a & b, 'polynomial multiplication repeats a formal edge')
            ans[a | b] = ans.get(a | b, 0) + ca * cb
    return {g: c for g, c in ans.items() if c}


def parity_polynomials(es):
    even, odd = {0: 1}, {}
    for edge in es:
        monomial = {mask([edge]): 1}
        even, odd = plus((1, even), (1, product(odd, monomial))), plus((1, odd), (1, product(even, monomial)))
    return even, odd


def one(es):
    return {mask(es): 1}


def targets():
    ans = {}
    for s, name in ((2, 'mean_two'), (3, 'mean_three')):
        pe = [(i, j) for i in range(s) for j in (s, s + 1, s + 2)] + [(s, s + 1), (s, s + 2)]
        ze = [(i, j) for i in range(s) for j in (s + 1, s + 2)]
        pe_pair, ze_pair = parity_polynomials(pe), parity_polynomials(ze)
        ans[name] = plus((1, pe_pair[0]), (-1, ze_pair[0]))
        if s == 3:
            f0 = plus((2, pe_pair[0]), (-1, ze_pair[0]))
            f1 = plus((2, pe_pair[1]), (-1, ze_pair[1]))
    p = plus((1, one([(0, 1)])), (1, one([(0, 2)])), (1, one([(1, 2)])), (-1, one([(0, 1), (0, 2), (1, 2)])))
    pf0 = product(p, f0)
    r4 = parity_polynomials([(0, 1), (1, 2), (2, 3), (0, 3)])[0]
    m = one([(0, 1)])
    tau = one([(0, 1), (0, 2), (1, 2)])
    a = one([(0, 1), (2, 3)])
    mtau = one([(0, 1), (2, 3), (2, 4), (3, 4)])
    p3 = one([(0, 1), (1, 2), (2, 3)])
    ans['negative_majority'] = plus((3, f0), (-3, r4), (1, f1), (-1, pf0), (-13, m), (-1, tau), (-12, a), (4, mtau), (-12, p3))
    ans['positive_majority'] = plus((6, f0), (-6, r4), (1, f1), (1, pf0), (-19, m), (-23, tau), (12, a), (-4, mtau), (-24, p3))
    return ans


def feature_blocks():
    out = [(0, 0, 3, [[(0, 1)], [(0, 1), (0, 2)], [(0, 1), (0, 2), (1, 2)]])]
    for r, types in ((1, [0]), (2, [0, 1])):
        free = [(i, j) for i in range(r) for j in (r, r + 1)] + [(r, r + 1)]
        idx = {tuple(sorted(e)): k for k, e in enumerate(free)}
        def flip(i):
            return r + 1 if i == r else r if i == r + 1 else i
        pats = []
        for bits in range(1, 1 << len(free)):
            chosen = [edge for k, edge in enumerate(free) if (bits >> k) & 1]
            exchanged = sum(1 << idx[tuple(sorted((flip(i), flip(j))))] for i, j in chosen)
            if bits <= exchanged:
                pats.append(chosen)
        out.extend((r, t, 2, pats) for t in types)
    for r, types in ((3, [0, 1, 3, 7]), (4, [0, 1, 3, 7, 11, 12, 13, 15, 30, 31, 63])):
        pats = [[(i, r) for i in range(r) if (bits >> i) & 1] for bits in range(1, 1 << r)]
        out.extend((r, t, 1, pats) for t in types)
    check([len(x[3]) for x in out] == [3, 5, 19, 19] + [7]*4 + [15]*11, 'wrong bases')
    return out


def rational_ldl(A):
    n = len(A)
    check(all(len(row) == n for row in A), 'not square')
    check(all(A[i][j] == A[j][i] for i in range(n) for j in range(n)), 'not symmetric')
    L = [[F(int(i == j)) for j in range(n)] for i in range(n)]
    d = []
    for j in range(n):
        pivot = F(A[j][j]) - sum((L[j][k]**2 * d[k] for k in range(j)), F(0))
        check(pivot > 0, 'nonpositive Schur pivot')
        d.append(pivot)
        for i in range(j + 1, n):
            L[i][j] = (F(A[i][j]) - sum((L[i][k]*d[k]*L[j][k] for k in range(j)), F(0))) / pivot
    for i in range(n):
        for j in range(n):
            value = sum((L[i][k]*d[k]*L[j][k] for k in range(n)), F(0))
            check(value == A[i][j], 'LDL reconstruction failed')
    return L, d


def roots_polynomial(r, t):
    poly = {0: 1}
    for bit, edge in enumerate(combinations(range(r), 2)):
        sign = 1 if (t >> bit) & 1 else -1
        poly = product(poly, {0: 1, mask([edge]): sign})
    return poly


def rooted_expansion(blocks, matrices):
    poly = {}
    for (r, t, free, patterns), A in zip(blocks, matrices):
        root = roots_polynomial(r, t)
        x = [one(p) for p in patterns]
        def shifted(p):
            return [(i if i < r else i + free, j if j < r else j + free) for i, j in p]
        y = [one(shifted(p)) for p in patterns]
        factor = 1 << (6 - r * (r - 1) // 2)
        for i in range(len(patterns)):
            for j in range(len(patterns)):
                part = product(root, product(x[i], y[j]))
                poly = plus((1, poly), (factor*A[i][j], part))
    return poly


def normalize(poly, norm):
    answer = [0] * K
    for g, coefficient in poly.items():
        answer[norm[g]] += coefficient
    return answer


def pair(q):
    return [str(q.numerator), str(q.denominator)]


def lean_list(xs, depth=0):
    if isinstance(xs, list):
        if not xs:
            return '[]'
        sep = ',\n' + '  ' * (depth + 1) if isinstance(xs[0], list) else ', '
        return '[' + sep.join(lean_list(x, depth + 1) for x in xs) + ']'
    return str(xs) if xs >= 0 else f'({xs})'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificates', type=Path)
    parser.add_argument('--export', type=Path, help='Export optional literal Lean and JSON witnesses.')
    args = parser.parse_args()
    default = Path(__file__).resolve().parents[1] / 'certificates'
    if not default.is_dir():
        default = Path(__file__).resolve().parent
    folder = args.certificates or default
    norm, witnesses, reps = normal_forms()
    print(f'PASS: {K} explicit relabelling witnesses; {len(reps)} normal forms.')
    bs = feature_blocks()
    ts = targets()
    all_ldl = {}
    all_matrices = {}
    total_pivots, total_entries, total_coefficients = 0, 0, 0
    for name in NAMES:
        obj = json.loads((folder / f'{name}_sos.json').read_text())
        check(obj['target'] == name and obj['graph_order'] == N and int(obj['denominator']) == DEN, 'schema mismatch')
        mats = [[[int(x) for x in row] for row in A] for A in obj['matrices']]
        check(len(mats) == len(bs) == 19, 'block count')
        check([len(A) for A in mats] == obj['block_dims'] == [len(b[3]) for b in bs], 'block size')
        ldl = []
        for A in mats:
            L, d = rational_ldl(A)
            ldl.append({'lower': [[pair(x) for x in row] for row in L], 'diagonal': [pair(x) for x in d]})
            total_pivots += len(d)
            total_entries += len(A)**2
        lhs = normalize({g: 64*DEN*c for g, c in ts[name].items()}, norm)
        rhs = normalize(rooted_expansion(bs, mats), norm)
        check(lhs == rhs, 'graph-polynomial identity failed: ' + name)
        total_coefficients += K
        all_ldl[name] = ldl
        all_matrices[name] = mats
        print(f'PASS: {name}: 19 rational LDL factorizations; all {K} normalized coefficients equal.')
    check(total_pivots == 956 and total_entries == 13708, 'count mismatch')
    print(f'PASS: {total_pivots} positive rational pivots and {total_entries} matrix-entry reconstruction identities.')
    print(f'PASS: {total_coefficients} normalized coefficient slots (including all zero slots).')
    if args.export:
        out = args.export
        out.mkdir(parents=True, exist_ok=True)
        (out / 'ldl_witnesses.json').write_text(json.dumps({'denominator': str(DEN), 'factorizations_of_integer_numerators': all_ldl}, indent=1)+'\n')
        (out / 'normalization_witnesses.json').write_text(json.dumps({'normal_form': norm, 'permutation': witnesses}, indent=1)+'\n')
        schema = [{'roots':r,'root_type':t,'new_vertices':k,'features':p} for r,t,k,p in bs]
        (out / 'feature_schema.json').write_text(json.dumps(schema, indent=1)+'\n')
        preamble = '/- Literal certificate data only. No mathematical theorem is claimed by this file.\n   Generated by independent_audit.py; this file has not been compiled in Lean. -/\nimport Init\n\nnamespace EvenCycleApex.CertificateData\n\ndef denominator : Nat := '+str(DEN)+'\n\n'
        content = preamble
        for name, mats in all_matrices.items():
            content += f'def {name} : List (List (List Int)) :=\n  '+lean_list(mats)+'\n\n'
        content += 'end EvenCycleApex.CertificateData\n'
        (out / 'CertificateData.lean').write_text(content)
        print('Exported optional witnesses and literal Lean matrix data to', out)
    print('PASS: independent arithmetic audit complete. No Lean theorem was compiled or assumed.')


if __name__ == '__main__':
    main()
