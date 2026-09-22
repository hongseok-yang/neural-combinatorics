"""Convert an induced interval certificate to bounded integer witnesses.

Checks its complete identity with completion counts rather than host permutations.
Floating point proposes triangular preconditioners only; exact products and
strict diagonal dominance validate each proposal. The output is untrusted until
the corresponding Lean kernel checks and graphon assembly have passed.
"""

import argparse
from fractions import Fraction
import hashlib
import json
import math
import os
from pathlib import Path

os.environ['OPENBLAS_NUM_THREADS'] = '1'
os.environ['OMP_NUM_THREADS'] = '1'
os.environ['MKL_NUM_THREADS'] = '1'

from flint import fmpz_mat
import networkx as nx
import numpy as np

from verify_remaining_cases_induced import target_bernstein


def rows(matrix):
    return [[int(v) for v in row] for row in matrix.tolist()]


def choose(n, k):
    return math.comb(n, k) if 0 <= k <= n else 0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('certificate')
    parser.add_argument('output')
    args = parser.parse_args()
    source = Path(args.certificate)
    c = json.loads(source.read_text(encoding='utf-8'))
    common_path = Path('experiments/induced_six_common.json')
    common = json.loads(common_path.read_text(encoding='utf-8'))
    assert c['graph6'] == common['graph6']
    a, b = Fraction(c['left']), Fraction(c['right'])
    graph = nx.graph_atlas_g()[c['atlas']]
    target = target_bernstein(graph, a, b, 5)
    gram_q = [[[Fraction(v) for v in row] for row in block['matrix']] for block in c['gram_blocks']]
    multipliers = [[Fraction(v) for v in row] for row in c['multipliers']]
    slacks = [[Fraction(v) for v in row] for row in c['slacks']]
    values = [v for block in gram_q for row in block for v in row]
    values += [v for row in slacks for v in row] + target
    values += [v*t for row in multipliers for v in row for t in (1,a,b)]
    denominator = math.lcm(*(v.denominator for v in values))
    scaled = lambda v: int(v*denominator) if (v*denominator).denominator == 1 else None
    grams = [[[scaled(v) for v in row] for row in block] for block in gram_q]
    assert all(v is not None for block in grams for row in block for v in row)

    positivity = []
    expansions = []
    totals = [[0,0,0] for _ in range(156)]
    rights = []
    for ti, typ in enumerate(common['types']):
        nf = typ['flag_count']
        left, right = fmpz_mat(c['left_faces'][ti]), fmpz_mat(c['right_faces'][ti])
        change = fmpz_mat(c['gram_blocks'][2*ti]['change'])
        top = fmpz_mat([[change[i,j] for j in range(change.ncols())] for i in range(left.ncols())])
        bottom = fmpz_mat([[change[left.ncols()+i,j] for j in range(change.ncols())]
                          for i in range(right.ncols())])
        n0 = fmpz_mat(rows(left*top)+rows(right*bottom))
        n1 = fmpz_mat(c['gram_blocks'][2*ti+1]['change'])
        expanded = []
        for block, N in ((2*ti,n0),(2*ti+1,n1)):
            G = fmpz_mat(grams[block])
            assert G == G.transpose()
            n = G.nrows()
            approximate = np.array([[float(Fraction(v,denominator)) for v in row] for row in grams[block]])
            proposal = np.linalg.inv(np.linalg.cholesky(approximate).T)*10**6
            P = fmpz_mat([[round(proposal[i,j]) if i <= j else 0 for j in range(n)] for i in range(n)])
            K = G*P
            dominant = P.transpose()*K
            assert all(P[i,i] > 0 for i in range(n)) and dominant == dominant.transpose()
            margin = min(int(dominant[i,i])-sum(abs(int(dominant[i,j])) for j in range(n) if i != j)
                         for i in range(n))
            assert margin > 0
            positivity.append(dict(preconditioner=rows(P),intermediate=rows(K),dominant=rows(dominant),margin=margin))
            NG = N*G
            H = NG*N.transpose()
            expansions.append(dict(N=rows(N),NG=rows(NG),H=rows(H)))
            expanded.append(H)
        H0,H1 = expanded
        for i in range(nf):
            for j in range(nf):
                entries = [int(H0[i,j]),int(H0[i,nf+j]+H0[nf+i,j]+H1[i,j]),int(H0[nf+i,nf+j])]
                rights.append(entries)
                code = int(typ['encoded_counts'][i][j])
                for host in range(156):
                    count = code % common['histogram_base']
                    code //= common['histogram_base']
                    for u in range(3):
                        totals[host][u] += count*entries[u]
                assert code == 0
    edge_index = {tuple(e):i for i,e in enumerate(common['pairs'])}
    required = sum(1 << edge_index[tuple(sorted(e))] for e in graph.edges())
    target_counts = [0]*156
    for mask,(host,_) in enumerate(common['classification']):
        if mask & required == required:
            target_counts[host] += 1
    u = [[scaled(v) for v in row] for row in multipliers]
    ua = [[scaled(a*v) for v in row] for row in multipliers]
    ub = [[scaled(b*v) for v in row] for row in multipliers]
    z = [[scaled(v) for v in row] for row in slacks]
    target_scaled = [scaled(v) for v in target]
    assert all(v >= 0 for row in z for v in row)
    for host in range(156):
        for k in range(6):
            lhs = choose(5,k)*(denominator*target_counts[host]-target_scaled[k]*common['orbit_sizes'][host])
            rhs = sum(choose(3,k-j)*totals[host][j] for j in range(3))
            rhs += choose(5,k)*z[host][k]*common['orbit_sizes'][host]
            for g in range(11):
                plain,edge = common['four_hom_counts'][g][host],common['four_edge_hom_counts'][g][host]
                if k < 5:
                    rhs += choose(4,k)*(edge*u[g][k]-plain*ua[g][k])
                if k > 0:
                    rhs += choose(4,k-1)*(edge*u[g][k-1]-plain*ub[g][k-1])
            assert lhs == rhs, (host,k,lhs-rhs)
    result = dict(format='compact-induced-interval-integer-v1',atlas=c['atlas'],
                  interval=[c['left'],c['right']], source=str(source),
                  source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  common_source=str(common_path),common_sha256=hashlib.sha256(common_path.read_bytes()).hexdigest(),
                  denominator=denominator,gram_scaled=grams,positivity=positivity,
                  expansions=expansions,right=rights,group_totals=totals,
                  multipliers=u,left_multipliers=ua,right_multipliers=ub,slacks=z,
                  target_bernstein=target_scaled,target_code=required,target_counts=target_counts,
                  formal_status='Untrusted; full graphon theorem not yet Lean verified')
    output = Path(args.output)
    output.write_text(json.dumps(result,separators=(',',':'))+'\n',encoding='utf-8')
    print(f'All 28 exact PSD witnesses and 936 completion-based integer equations passed; '
          f'D={denominator}; {len(rights)} coordinates; wrote {output.stat().st_size} bytes',flush=True)


if __name__ == '__main__':
    main()
