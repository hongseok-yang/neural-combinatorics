#!/usr/bin/env python3
"""Exact, standard-library checker for the six-vertex signed-kernel inequality.

No floating-point arithmetic, numerical solver, or third-party package is used.
The checker expands the integral of each nonnegative weighted quadratic form
as a signed graph polynomial, and compares all graph coefficients exactly.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from itertools import combinations, permutations
import json
from pathlib import Path

if not __debug__:
    raise SystemExit('Run without -O: this program uses assertion checks.')

ORDER=6
EDGES=tuple(combinations(range(ORDER),2))
EDGE_INDEX={e:i for i,e in enumerate(EDGES)}
PERMUTATIONS=tuple(permutations(range(ORDER)))

def emask(edges):
    ans=0
    for x,y in edges:
        assert x!=y
        ans |= 1<<EDGE_INDEX[tuple(sorted((x,y))) ]
    return ans

def canonical_table():
    """Partition all 2^15 labelled graphs into their complete S_6 orbits."""
    moves=[[1<<EDGE_INDEX[tuple(sorted((p[i],p[j])))] for i,j in EDGES]
           for p in PERMUTATIONS]
    table=[-1]*(1<<len(EDGES)); representatives=[]; total=0
    for g in range(len(table)):
        if table[g]>=0: continue
        active=[i for i in range(len(EDGES)) if g>>i&1]
        orbit={sum(row[i] for i in active) for row in moves}
        assert min(orbit)==g
        assert all(table[h]<0 for h in orbit)
        for h in orbit: table[h]=g
        representatives.append(g);total+=len(orbit)
    assert total==32768 and len(representatives)==156 and all(x>=0 for x in table)
    return table,representatives

def expand(edges,parity):
    bits=[1<<EDGE_INDEX[tuple(sorted(e))] for e in edges]
    return {sum(bits[j] for j in range(len(bits)) if s>>j&1):1
            for s in range(1<<len(bits)) if s.bit_count()%2==parity}

def add(*terms):
    ans=defaultdict(int)
    for c,p in terms:
        for g,a in p.items():ans[g]+=c*a
    return {g:a for g,a in ans.items() if a}

def multiply_disjoint(p,q):
    ans=defaultdict(int)
    for g,a in p.items():
        for h,b in q.items():
            assert g&h==0,'A repeated edge is not a simple-graph monomial.'
            ans[g|h]+=a*b
    return dict(ans)

def target_polynomial(kind):
    if kind in ('mean_two','mean_three'):
        s=2 if kind=='mean_two' else 3; inn=(s,s+1,s+2)
        pe=[(i,j) for i in range(s) for j in inn]+[(inn[0],inn[1]),(inn[0],inn[2])]
        ze=[(i,j) for i in range(s) for j in (inn[1],inn[2])]
        return add((1,expand(pe,0)),(-1,expand(ze,0)))
    # Integrands of Pi_3 and D_3^2: three fixed apices 0,1,2.
    pe=[(i,j) for i in range(3) for j in (3,4,5)]+[(3,4),(3,5)]
    ze=[(i,j) for i in range(3) for j in (4,5)]
    Pi=[expand(pe,k) for k in (0,1)]
    Z=[expand(ze,k) for k in (0,1)]
    F=[add((2,Pi[k]),(-1,Z[k])) for k in (0,1)]
    majority={emask([e]):1 for e in combinations(range(3),2)}
    majority[emask(combinations(range(3),2))]=-1
    MF=multiply_disjoint(majority,F[0])
    R4=expand([(0,1),(1,2),(2,3),(3,0)],0)
    m={emask([(0,1)]):1}
    tau={emask([(0,1),(0,2),(1,2)]):1}
    a={emask([(0,1),(2,3)]):1}
    mtau={emask([(0,1),(2,3),(2,4),(3,4)]):1}
    p3={emask([(0,1),(1,2),(2,3)]):1}
    if kind=='negative_majority':
        return add((3,F[0]),(-3,R4),(1,F[1]),(-1,MF),
                   (-13,m),(-1,tau),(-12,a),(4,mtau),(-12,p3))
    if kind=='positive_majority':
        return add((6,F[0]),(-6,R4),(1,F[1]),(1,MF),
                   (-19,m),(-23,tau),(12,a),(-4,mtau),(-24,p3))
    raise ValueError('Unknown target')

def root_types(r):
    edges=tuple(combinations(range(r),2)); ei={e:i for i,e in enumerate(edges)}
    result=set()
    for m in range(1<<len(edges)):
        es=[edges[i] for i in range(len(edges)) if m>>i&1]
        result.add(min(sum(1<<ei[tuple(sorted((p[i],p[j])))] for i,j in es)
                       for p in permutations(range(r))))
    return sorted(result)

def two_extension_patterns(r):
    edges=[(i,j) for i in range(r) for j in (r,r+1)]+[(r,r+1)]
    ei={tuple(sorted(e)):i for i,e in enumerate(edges)}
    def exchange(i):return r+1 if i==r else r if i==r+1 else i
    swaps=[ei[tuple(sorted((exchange(i),exchange(j))))] for i,j in edges]
    reps=[]
    for m in range(1,1<<len(edges)):
        mm=sum(1<<swaps[j] for j in range(len(edges)) if m>>j&1)
        if m<=mm:reps.append([edges[j] for j in range(len(edges)) if m>>j&1])
    return reps

def blocks():
    # A block is (number of roots, literal root type, extension size, patterns).
    out=[(0,0,3,[[(0,1)],[(0,1),(0,2)],[(0,1),(0,2),(1,2)]])]
    out.append((1,0,2,two_extension_patterns(1)))
    out.extend((2,t,2,two_extension_patterns(2)) for t in (0,1))
    for r in (3,4):
        pats=[[(i,r) for i in range(r) if m>>i&1] for m in range(1,1<<r)]
        out.extend((r,t,1,pats) for t in root_types(r))
    assert [len(b[3]) for b in out]==[3,5,19,19]+[7]*4+[15]*11
    return out

def relocated(pattern,r,shift):
    def move(v):return v if v<r else v+shift
    return emask([(move(x),move(y)) for x,y in pattern])

def positive_definite(Q):
    """Bareiss elimination computes all leading principal determinants."""
    n=len(Q)
    assert all(len(row)==n for row in Q)
    assert all(Q[i][j]==Q[j][i] for i in range(n) for j in range(n))
    A=[row.copy() for row in Q];prev=1;minor_digits=[]
    for k in range(n):
        pivot=A[k][k]
        assert pivot>0,('Nonpositive leading principal minor',k,pivot)
        minor_digits.append(len(str(pivot)))
        if k==n-1:break
        for i in range(k+1,n):
            for j in range(i,n):
                numerator=A[i][j]*pivot-A[i][k]*A[k][j]
                q,rem=divmod(numerator,prev)
                assert rem==0,'Nonexact Bareiss division'
                A[i][j]=A[j][i]=q
        prev=pivot
    return minor_digits

def verify(path):
    obj=json.loads(path.read_text());den=int(obj['denominator'])
    assert den>0 and obj['target'] in ('negative_majority','positive_majority','mean_two','mean_three') and obj['graph_order']==6
    cert=[[[int(x) for x in row] for row in Q] for Q in obj['matrices']]
    bs=blocks();assert len(cert)==len(bs)==19
    canon,reps=canonical_table()
    lhs=defaultdict(int)
    for g,c in target_polynomial(obj['target']).items():lhs[canon[g]]+=64*den*c
    rhs=defaultdict(int);minor_count=0;largest=0
    for index,((r,t,k,pats),Q) in enumerate(zip(bs,cert)):
        assert len(Q)==len(pats)==obj['block_dims'][index]
        digs=positive_definite(Q);minor_count+=len(digs);largest=max(largest,max(digs))
        redges=list(combinations(range(r),2));nr=len(redges)
        root_terms=[]
        for subset in range(1<<nr):
            rm=emask([redges[i] for i in range(nr) if subset>>i&1])
            sign=(-1)**((subset & (((1<<nr)-1)^t)).bit_count())
            root_terms.append((rm,sign*(1<<(6-nr))))
        first=[relocated(p,r,0) for p in pats]
        second=[relocated(p,r,k) for p in pats]
        for i in range(len(pats)):
            for j in range(len(pats)):
                q=Q[i][j]
                if not q:continue
                assert first[i]&second[j]==0
                g=first[i]|second[j]
                for rm,c in root_terms:
                    assert g&rm==0
                    rhs[canon[g|rm]]+=c*q
        print(f'PD block {index+1:02d}: roots={r}, type={t}, size={len(pats)}')
    errors=[g for g in reps if lhs[g]!=rhs[g]]
    if errors:
        for g in errors[:20]:print('MISMATCH',g,lhs[g]-rhs[g])
    assert not errors,'The signed graph-polynomial identity is false.'
    assert minor_count==239
    print('All 32768 labelled six-vertex graphs are covered by 156 distinct orbits.')
    print('All 156 signed graph-polynomial coefficients agree exactly.')
    print(f'All {minor_count} leading principal minors are positive; largest integer has {largest} digits.')
    print(f'Common matrix denominator: {den}')
    print('PASS:',obj['target'],'is a sum of nonnegative weighted quadratic forms.')

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('certificates',nargs='*',type=Path)
    args=parser.parse_args()
    paths=args.certificates or [Path(__file__).with_name(name) for name in (
        'mean_two_sos.json','mean_three_sos.json',
        'negative_majority_sos.json','positive_majority_sos.json')]
    for path in paths:
        print('\nCERTIFICATE:',path.name)
        verify(path)
    print('\nPASS: all requested certificates verified with exact integer arithmetic.')
