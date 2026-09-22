"""Exact reconstruction utilities for the new six-point interval searches."""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
import itertools as it
from pathlib import Path

import numpy as np
from scipy import linalg
from scipy import sparse
import sympy as sy
import networkx as nx
from flint import fmpq, fmpq_mat

from remaining_cases_flag_search import WORK, build, injection_vector
from remaining_cases_interval_search import lift_tri, bernstein_coefficients


def recover_face(q, cutoff=1e-7):
    values, vectors=np.linalg.eigh((q+q.T)/2)
    kernel=vectors[:,values<cutoff]
    n,k=kernel.shape
    if k==0:
        return np.eye(n,dtype=np.int64)
    _,_,piv=linalg.qr(kernel.T,pivoting=True,mode='economic')
    canonical=kernel@np.linalg.inv(kernel[piv[:k],:])
    rational=[[Fraction(float(x)).limit_denominator(144) for x in row] for row in canonical]
    error=np.max(np.abs(canonical-np.array(rational,dtype=float)))
    if error>2e-3:
        raise ValueError(f'Cannot recognize rational kernel: error {error}')
    null=sy.Matrix(rational).T.nullspace()
    columns=[]
    for v in null:
        den=sy.ilcm(*[x.q for x in v])
        columns.append([int(x*den) for x in v])
    face=np.array(columns,dtype=np.int64).T
    print(f'face {n}->{n-k}, reconstruction error {error:.2g}, max entry {np.max(np.abs(face))}',flush=True)
    return face


def harvest(aid):
    source=WORK/f'atlas{aid}_induced_interval_d5_CLARABEL.npz'
    data=np.load(source)
    faces={f'C{i}':recover_face(data[f'Q{i}'],cutoff=1e-5 if aid==130 else 1e-7) for i in range(28)}
    path=WORK/f'atlas{aid}_induced_faces.npz'
    np.savez(path,**faces)
    print(path)


def coefficient_system(aid, data, raw, faces):
    """Integer matrix A with graph/Bernstein coefficients A*x/den."""
    degree=int(raw['degree'])
    a,b=sy.Rational(str(raw['left'])),sy.Rational(str(raw['right']))
    den=math.lcm(720*degree*(degree-1),720*degree*int(sy.ilcm(a.q,b.q)))
    nH=len(data['graph6'])
    chunks=[]
    specs=[]
    x0=[]
    for bi,block in enumerate(data['blocks']):
        l,r=raw[f'L{bi}'],raw[f'R{bi}']
        for side in range(2):
            qi=2*bi+side
            change=faces[f'C{qi}']
            inverse=np.linalg.pinv(change.astype(float))
            q=inverse@raw[f'Q{qi}']@inverse.T
            nr=len(q)
            specs.append((qi,nr,len(x0),change))
            x0.extend(q[i,j] for j in range(nr) for i in range(j+1))
            if side==0:
                la=l@change[:l.shape[1],:]
                rb=r@change[l.shape[1]:,:]
                aa=lift_tri(block,la)
                bb=lift_tri(block,rb)
                ab=lift_tri(block,la+rb)-aa-bb
            else:
                ab=lift_tri(block,change)
            layers=[]
            factor=den//(block['den']*degree*(degree-1))
            for k in range(degree+1):
                layer=k*(degree-k)*ab
                if side==0:
                    layer=layer+(degree-k)*(degree-k-1)*aa+k*(k-1)*bb
                layers.append(layer*factor)
            # First stack by degree, then put graph first.
            joined=sparse.vstack(layers,format='csr')
            ordering=np.arange(nH*(degree+1)).reshape(degree+1,nH).T.ravel()
            chunks.append(joined[ordering,:])
    atlas=nx.graph_atlas_g()
    bases=[g for g in atlas if len(g)==4]
    tbase=np.array([np.rint(720*injection_vector(data,list(g.edges()))).astype(np.int64) for g in bases]).T
    tedge=np.array([np.rint(720*injection_vector(data,list(g.edges())+[(4,5)])).astype(np.int64) for g in bases]).T
    columns=[]
    weight_start=len(x0)
    for j in range(len(bases)):
        for power in range(degree):
            column=np.zeros((nH,degree+1),dtype=np.int64)
            fa=sy.Rational(den*(degree-power),720*degree)
            fb=sy.Rational(den*(power+1),720*degree)
            column[:,power]=int(fa)*tedge[:,j]-int(fa*a)*tbase[:,j]
            column[:,power+1]=int(fb)*tedge[:,j]-int(fb*b)*tbase[:,j]
            columns.append(column.ravel())
            x0.append(raw['multipliers'][j,power])
    chunks.append(sparse.csr_matrix(np.array(columns).T))
    matrix=sparse.hstack(chunks,format='csr',dtype=np.int64)
    graph=atlas[aid]
    s=sy.Symbol('s'); p=a+(b-a)*s
    chromatic=nx.chromatic_polynomial(graph); x=next(iter(chromatic.free_symbols))
    phi=sy.cancel((1-p)**6*chromatic.subs(x,1/(1-p)))
    target=bernstein_coefficients(phi,s,degree)
    h=np.rint(720*injection_vector(data,list(graph.edges()))).astype(int)
    rhs=[fmpq(int(v),720)-fmpq(str(z)) for v in h for z in target]
    return matrix,den,rhs,np.array(x0),specs,weight_start


def rational_psd(matrix):
    """Exact LDL with positive pivots; returns smallest pivot as a rational."""
    n=len(matrix)
    q=[[fmpq(x) for x in row] for row in matrix]
    pivots=[]
    for k in range(n):
        pivot=q[k][k]
        if pivot<=0:
            raise ValueError(f'nonpositive LDL pivot {k}: {pivot}')
        pivots.append(pivot)
        for i in range(k+1,n):
            factor=q[i][k]/pivot
            for j in range(i,n):
                q[j][i]=q[i][j]=q[i][j]-factor*q[k][j]
    return min(pivots)


def rationalize(aid, rounding=10**10):
    data=build(6)
    raw=np.load(WORK/f'atlas{aid}_induced_interval_d5_CLARABEL.npz')
    faces=np.load(WORK/f'atlas{aid}_induced_faces.npz')
    matrix,den,rhs,x0,specs,weight_start=coefficient_system(aid,data,raw,faces)
    critical=np.flatnonzero(raw['slack'].ravel()<1e-5)
    subset=matrix[critical,:].toarray()
    _, triangular,piv=linalg.qr(subset.astype(float),pivoting=True,mode='economic')
    rank=int(np.sum(np.abs(np.diag(triangular))>1e-7))
    columns=piv[:rank]
    _,_,rowperm=linalg.qr(subset[:,columns].T.astype(float),pivoting=True,mode='economic')
    rows=rowperm[:rank]
    square=fmpq_mat(subset[np.ix_(rows,columns)].tolist())
    values=[fmpq(int(round(float(v)*rounding)),rounding) for v in x0]
    def dot(row):
        return sum((int(v)*values[int(j)] for j,v in zip(row.indices,row.data)),fmpq(0))
    residual=[den*rhs[int(critical[i])]-dot(matrix[int(critical[i])]) for i in rows]
    correction=square.solve(fmpq_mat([[v] for v in residual]))
    for i,col in enumerate(columns):
        values[int(col)]+=correction[i,0]
    print(f'critical equations={len(critical)}, rank={rank}, correction max='
          f'{max(abs(float(v)) for v in correction.entries()):.3g}',flush=True)
    slacks=[rhs[i]-dot(matrix[i])/den for i in range(matrix.shape[0])]
    assert all(slacks[int(i)]==0 for i in critical), 'dependent critical equation is not exact'
    negative=[(i,str(v)) for i,v in enumerate(slacks) if v<0]
    if negative:
        raise ValueError(f'negative exact slacks: {negative[:5]}')
    grams=[]
    for qi,nr,start,change in specs:
        q=[[fmpq(0) for _ in range(nr)] for _ in range(nr)]
        k=start
        for j in range(nr):
            for i in range(j+1):
                q[i][j]=q[j][i]=values[k]; k+=1
        pivot=rational_psd(q)
        print(f'Gram {qi}, order {nr}, smallest exact LDL pivot ~ {float(pivot):.3g}',flush=True)
        grams.append(dict(change=change.tolist(),matrix=[[str(v) for v in row] for row in q]))
    certificate=dict(format='six-point-induced-interval-v1',atlas=aid,left=str(raw['left']),
                     right=str(raw['right']),degree=int(raw['degree']),
                     graph6=data['graph6'],gram_blocks=grams,
                     left_faces=[raw[f'L{i}'].tolist() for i in range(14)],
                     right_faces=[raw[f'R{i}'].tolist() for i in range(14)],
                     multipliers=[[str(values[weight_start+5*j+k]) for k in range(5)] for j in range(11)],
                     slacks=[[str(slacks[6*i+k]) for k in range(6)] for i in range(len(data['graph6']))])
    output=Path(__file__).resolve().parent/f'atlas{aid}_exact_lower_induced_interval.json'
    output.write_text(json.dumps(certificate,separators=(',',':'))+'\n',encoding='utf-8')
    print(f'EXACT reconstruction passed; {matrix.shape[0]} coefficients; wrote {output}',flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--atlas',type=int,required=True)
    parser.add_argument('--rationalize',action='store_true')
    args=parser.parse_args()
    if args.rationalize:
        rationalize(args.atlas)
    else:
        harvest(args.atlas)
