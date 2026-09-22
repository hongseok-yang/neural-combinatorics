"""Independent exact verifier for the Atlas 130 and 203 lower intervals.

Trusted inputs: a JSON certificate, NetworkX's small graph atlas, and exact
integer/rational arithmetic. No solver, floating point, numerical cache, or
discovery module is imported. Rooted tables are rebuilt by all 720 ordered
six-point samples, independently of the discovery script's subset counting.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import itertools as it
import json
import math
from pathlib import Path

from flint import fmpq, fmpq_mat
import networkx as nx


def require(condition, message):
    if not condition:
        raise ValueError(message)


def multiply(a,b):
    result=[Fraction(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            result[i+j]+=x*y
    return result


def proper_partition_target(graph):
    """Sum (z)_k over independent set partitions, then put z=1/(1-p)."""
    n=len(graph)
    counts=Counter()
    def visit(v,classes):
        if v==n:
            counts[len(classes)]+=1
            return
        for cell in classes:
            if all(not graph.has_edge(v,u) for u in cell):
                cell.append(v); visit(v+1,classes); cell.pop()
        classes.append([v]); visit(v+1,classes); classes.pop()
    visit(0,[])
    result=[Fraction(0)]*(n+1)
    for k,count in counts.items():
        poly=[Fraction(count)]
        for _ in range(n-k):
            poly=multiply(poly,[1,-1])
        for j in range(k):
            poly=multiply(poly,[1-j,j])
        for i,value in enumerate(poly):
            result[i]+=value
    return result


def target_bernstein(graph,a,b,degree):
    power=proper_partition_target(graph)
    result=[Fraction(0)]*(degree+1)
    for j,value in enumerate(power):
        for k in range(j+1):
            term=value*math.comb(j,k)*a**(j-k)*(b-a)**k
            if k>degree:
                require(term==0,'target degree exceeds certificate degree')
            else:
                result[k]+=term
    return [sum((result[j]*Fraction(math.comb(k,j),math.comb(degree,j))
                 for j in range(k+1)),Fraction(0)) for k in range(degree+1)]


def matrix(rows):
    require(isinstance(rows,list) and len(rows)>0,'empty matrix')
    require(all(isinstance(row,list) and len(row)==len(rows[0]) for row in rows),'ragged matrix')
    return fmpq_mat([[fmpq(str(x)) for x in row] for row in rows])


def positive_definite(rows):
    q=matrix(rows)
    n=q.nrows()
    require(q.ncols()==n,'Gram factor must be square')
    require(q==q.transpose(),'Gram factor must be symmetric')
    # A separate exact Schur-complement implementation of Sylvester's test.
    for k in range(n):
        pivot=q[k,k]
        require(pivot>0,f'nonpositive exact Schur pivot {k}: {pivot}')
        for i in range(k+1,n):
            for j in range(k+1,n):
                q[i,j]-=q[i,k]*q[k,j]/pivot
    return matrix(rows)


def flag_definition(m,r):
    edges=[(i,j) for i,j in it.combinations(range(m+r),2) if j>=m]
    edge_index={edge:i for i,edge in enumerate(edges)}
    canonical=[]
    for pattern in range(1<<len(edges)):
        images=[]
        for permutation in it.permutations(range(m,m+r)):
            image=tuple(range(m))+permutation
            mask=0
            for k,(i,j) in enumerate(edges):
                if pattern>>k&1:
                    mask|=1<<edge_index[tuple(sorted((image[i],image[j])))]
            images.append(mask)
        canonical.append(min(images))
    flags=sorted(set(canonical))
    flag_index={mask:i for i,mask in enumerate(flags)}
    return edges,[flag_index[mask] for mask in canonical],len(flags)


def prepare_grams(certificate,types):
    output=[]
    require(len(certificate['gram_blocks'])==2*len(types),'wrong Gram block count')
    require(len(certificate['left_faces'])==len(types),'wrong left-face count')
    require(len(certificate['right_faces'])==len(types),'wrong right-face count')
    for index,(m,type_graph) in enumerate(types):
        nf=flag_definition(m,(6-m)//2)[2]
        l=matrix(certificate['left_faces'][index])
        r=matrix(certificate['right_faces'][index])
        require(l.nrows()==r.nrows()==nf,'face row dimension mismatch')
        block0,block1=certificate['gram_blocks'][2*index:2*index+2]
        q0,q1=positive_definite(block0['matrix']),positive_definite(block1['matrix'])
        c0,c1=matrix(block0['change']),matrix(block1['change'])
        require(c0.nrows()==l.ncols()+r.ncols() and c0.ncols()==q0.nrows(),'Q0 dimension mismatch')
        require(c1.nrows()==nf and c1.ncols()==q1.nrows(),'Q1 dimension mismatch')
        top=fmpq_mat([[c0[i,j] for j in range(c0.ncols())] for i in range(l.ncols())])
        bottom=fmpq_mat([[c0[l.ncols()+i,j] for j in range(c0.ncols())] for i in range(r.ncols())])
        aa,bb=l*top,r*bottom
        q00=aa*q0*aa.transpose()
        cross=aa*q0*bb.transpose()
        q01=cross+cross.transpose()+c1*q1*c1.transpose()
        q11=bb*q0*bb.transpose()
        output.append((q00,q01,q11))
    return output


def rebuild_counts(graph,types):
    """Rooted tables and injective counts, all with common denominator 6!."""
    adjacency=[[int(graph.has_edge(i,j)) for j in range(6)] for i in range(6)]
    configurations={}
    for m in (0,2,4):
        root_edges=list(it.combinations(range(m),2))
        types_by_mask={sum(1<<k for k,e in enumerate(root_edges) if typ.has_edge(*e)):i
                       for i,(mm,typ) in enumerate(types) if mm==m}
        configurations[m]=(root_edges,types_by_mask,flag_definition(m,(6-m)//2))
    counters=[Counter() for _ in types]
    injections=[]
    for permutation in it.permutations(range(6)):
        # Keep the relabelled adjacency for independent homomorphism counts.
        adj=[[adjacency[permutation[i]][permutation[j]] for j in range(6)] for i in range(6)]
        injections.append(adj)
        for m in (0,2,4):
            roots,type_map,(edges,lut,nf)=configurations[m]
            root_mask=sum(1<<k for k,(i,j) in enumerate(roots) if adj[i][j])
            if root_mask not in type_map:
                continue
            r=(6-m)//2
            flags=[]
            for offset in (0,r):
                vertices=list(range(m))+list(range(m+offset,m+offset+r))
                pattern=sum(1<<k for k,(i,j) in enumerate(edges) if adj[vertices[i]][vertices[j]])
                flags.append(lut[pattern])
            counters[type_map[root_mask]][tuple(flags)]+=1
    return counters,injections


def verify(path):
    certificate=json.loads(Path(path).read_text(encoding='utf-8'))
    require(certificate['format']=='six-point-induced-interval-v1','wrong certificate format')
    atlas=nx.graph_atlas_g()
    aid=certificate['atlas']
    require(aid in (130,203),'unsupported target')
    graph=atlas[aid]
    a,b=Fraction(certificate['left']),Fraction(certificate['right'])
    expected=(Fraction(1,2),Fraction(2,3)) if aid==130 else (Fraction(2,3),Fraction(3,4))
    require((a,b)==expected,'wrong claimed interval')
    degree=certificate['degree']
    require(degree==5,'unexpected polynomial degree')
    host_graphs=[g for g in atlas if len(g)==6]
    graph6=[nx.to_graph6_bytes(g,header=False).strip().decode() for g in host_graphs]
    require(certificate['graph6']==graph6,'host graph list incomplete or reordered')
    require(len(host_graphs)==156,'wrong six-vertex census')
    types=[(m,g) for m in (0,2,4) for g in atlas if len(g)==m]
    grams=prepare_grams(certificate,types)
    print(f'Atlas {aid}: all 28 rational Gram factors positive definite',flush=True)
    target=target_bernstein(graph,a,b,degree)
    expected_target=[0,0,0,1,-4,4,0] if aid==130 else [0,10,-63,148,-154,60,0]
    require(proper_partition_target(graph)==expected_target,'chromatic target mismatch')
    bases=[g for g in atlas if len(g)==4]
    multipliers=certificate['multipliers']
    slacks=certificate['slacks']
    require(len(multipliers)==11 and all(len(row)==degree for row in multipliers),'wrong multipliers')
    require(len(slacks)==156 and all(len(row)==degree+1 for row in slacks),'wrong slack array')
    multipliers=[[fmpq(v) for v in row] for row in multipliers]
    slacks=[[fmpq(v) for v in row] for row in slacks]
    require(all(v>=0 for row in slacks for v in row),'negative residual coefficient')
    target=[fmpq(str(x)) for x in target]
    qa,qb=fmpq(str(a)),fmpq(str(b))
    target_edges=list(graph.edges())
    checks=0
    for host_index,host in enumerate(host_graphs):
        counts,injections=rebuild_counts(host,types)
        h=fmpq(sum(all(adj[i][j] for i,j in target_edges) for adj in injections),720)
        gram_moments=[]
        for counter,matrices in zip(counts,grams):
            gram_moments.append([sum((count*q[i,j] for (i,j),count in counter.items()),fmpq(0))/720
                                 for q in matrices])
        base=[]; edge=[]
        for g in bases:
            edges=list(g.edges())
            base.append(fmpq(sum(all(adj[i][j] for i,j in edges) for adj in injections),720))
            edge.append(fmpq(sum(adj[4][5] and all(adj[i][j] for i,j in edges) for adj in injections),720))
        for k in range(degree+1):
            rhs=slacks[host_index][k]
            c00=fmpq((degree-k)*(degree-k-1),degree*(degree-1))
            c01=fmpq(k*(degree-k),degree*(degree-1))
            c11=fmpq(k*(k-1),degree*(degree-1))
            rhs+=sum((c00*x+c01*y+c11*z for x,y,z in gram_moments),fmpq(0))
            for j in range(11):
                if k<degree:
                    rhs+=fmpq(degree-k,degree)*(edge[j]-qa*base[j])*multipliers[j][k]
                if k>0:
                    rhs+=fmpq(k,degree)*(edge[j]-qb*base[j])*multipliers[j][k-1]
            require(h-target[k]==rhs,f'coefficient mismatch at graph {host_index}, Bernstein index {k}')
            checks+=1
    print(f'PASS Atlas {aid}: {checks} exact coefficient equations, '
          f'{sum(v==0 for row in slacks for v in row)} zero and '
          f'{sum(v>0 for row in slacks for v in row)} positive residual coefficients; '
          f'interval [{a},{b}]',flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('certificates',nargs='+')
    args=parser.parse_args()
    for path in args.certificates:
        verify(path)
