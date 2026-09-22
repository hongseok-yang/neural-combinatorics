"""Discover interval certificates using unconditional induced rooted squares.

The output of this module is numerical evidence only. Integer table rebuilding
and rational positive-semidefiniteness checks are required before acceptance.
"""
from __future__ import annotations

import argparse
import itertools as it
import math
import time

import cvxpy as cp
import networkx as nx
import numpy as np
import sympy as sy
from scipy import sparse

from remaining_cases_flag_search import WORK, build, branch_lut, injection_vector


def endpoint_face(block, colours):
    m, r, nf = block["m"], block["r"], block["nf"]
    edges, lut, _ = branch_lut(m, r)
    root_edges = list(it.combinations(range(m), 2))
    rows = set()
    for root in it.product(range(colours), repeat=m):
        mask = sum(1 << k for k, (i, j) in enumerate(root_edges) if root[i] != root[j])
        if mask != block["type_mask"]:
            continue
        v = [0] * nf
        for branch in it.product(range(colours), repeat=r):
            assignment = root + branch
            pat = sum(1 << k for k, (i, j) in enumerate(edges) if assignment[i] != assignment[j])
            v[lut[pat]] += 1
        rows.add(tuple(v))
    if not rows:
        return np.eye(nf, dtype=int)
    null = sy.Matrix(sorted(rows)).nullspace()
    columns = []
    for v in null:
        den = sy.ilcm(*[x.q for x in v])
        columns.append([int(x*den) for x in v])
    return np.array(columns, dtype=int).T


def bernstein_coefficients(expr, var, degree):
    poly = sy.Poly(sy.expand(expr), var)
    return [sum(poly.nth(j)*sy.Rational(math.comb(k,j), math.comb(degree,j))
                for j in range(k+1)) for k in range(degree+1)]


def lift_tri(block, transform):
    """Exact integer map from reduced symmetric Q entries to graph coefficients."""
    nf, nc = transform.shape
    # Full matrix-vectorization followed by sparse projection is inexpensive here.
    rows, cols, vals = [], [], []
    out = 0
    for j in range(nc):
        for i in range(j+1):
            q = np.outer(transform[:,i], transform[:,j])
            if i != j:
                q = q + q.T
            tri = [q[a,b] for b in range(nf) for a in range(b+1)]
            values = block["table"] @ np.array(tri)
            nz = np.flatnonzero(values)
            rows.extend(nz.tolist()); cols.extend([out]*len(nz)); vals.extend(values[nz].tolist())
            out += 1
    return sparse.csr_matrix((vals,(rows,cols)), shape=(block['table'].shape[0],nc*(nc+1)//2))


def search(atlas_id, left, right, degree, max_iters, solver_name, reduced=False):
    start = time.time()
    data = build(6)
    blocks = data["blocks"]
    a,b=sy.Rational(left), sy.Rational(right)
    s=sy.Symbol("s")
    p=a+(b-a)*s
    graph=nx.graph_atlas_g()[atlas_id]
    chromatic=nx.chromatic_polynomial(graph)
    x=next(iter(chromatic.free_symbols))
    phi=sy.cancel((1-p)**6*chromatic.subs(x,1/(1-p)))
    target=np.array(bernstein_coefficients(phi,s,degree),dtype=float)
    h=injection_vector(data,list(graph.edges()))
    nH=len(h)
    bases=[g for g in nx.graph_atlas_g() if len(g)==4]
    tbase=np.array([injection_vector(data,list(g.edges())) for g in bases]).T
    tedge=np.array([injection_vector(data,list(g.edges())+[(4,5)]) for g in bases]).T
    multipliers=cp.Variable((len(bases),degree))
    rhs=[]
    for k in range(degree+1):
        term=0
        if k<degree:
            term=term+(degree-k)/degree*(tedge-float(a)*tbase)@multipliers[:,k]
        if k>0:
            term=term+k/degree*(tedge-float(b)*tbase)@multipliers[:,k-1]
        rhs.append(term)
    allgrams=[]
    gramvariables=[]
    reductions=[]
    faces=[]
    face_data=np.load(WORK/f'atlas{atlas_id}_induced_faces.npz') if reduced else None
    for bi,block in enumerate(blocks):
        nf=block['nf']
        ca,cb=int(1/(1-a)),int(1/(1-b))
        assert a==1-sy.Rational(1,ca) and b==1-sy.Rational(1,cb)
        l=endpoint_face(block,ca)
        r=endpoint_face(block,cb)
        # Q0 acts on ((1-s)*l^T f, s*r^T f).
        n0,n1=l.shape[1],r.shape[1]
        expressions=[]
        for index,order in [(2*bi,n0+n1),(2*bi+1,nf)]:
            change=face_data[f'C{index}'] if reduced else np.eye(order,dtype=int)
            variable=cp.Variable((change.shape[1],change.shape[1]),symmetric=True)
            gramvariables.append(variable)
            reductions.append(change)
            expressions.append(change@variable@change.T)
        gram,gram1=expressions
        allgrams.extend([gram,gram1])
        faces.append((l,r))
        mapping=lift_tri(block,np.hstack([l,r]))/block['den']
        mapping1=block['table']/block['den']
        tri_indices=[(i,j) for j in range(n0+n1) for i in range(j+1)]
        small=[gram1[i,j] for j in range(nf) for i in range(j+1)]
        for k in range(degree+1):
            c00=(degree-k)*(degree-k-1)/(degree*(degree-1))
            c01=k*(degree-k)/(degree*(degree-1))
            c11=k*(k-1)/(degree*(degree-1))
            v=cp.hstack([gram[i,j]*(c00 if j<n0 else c11 if i>=n0 else c01)
                         for i,j in tri_indices])
            rhs[k]=rhs[k]+mapping@v+c01*mapping1@cp.hstack(small)
    margin=cp.Variable()
    constraints=[g>>margin*np.eye(g.shape[0]) if reduced else g>>0 for g in gramvariables]
    # Positive Bernstein coefficients provide nonnegative induced-density slack.
    slack=cp.Variable((nH,degree+1),nonneg=True)
    for k in range(degree+1):
        constraints.append(h-target[k]==rhs[k]+slack[:,k])
    # Maximize an interior slack margin, avoiding forced endpoint equalities.
    if reduced:
        previous=np.load(WORK/f'atlas{atlas_id}_induced_interval_d5_CLARABEL.npz')['slack']
        zero_mask=previous<1e-7
        constraints.extend([slack[zero_mask]==0,slack[~zero_mask]>=margin])
    else:
        constraints.append(slack[:,1:-1]>=margin)
    problem=cp.Problem(cp.Maximize(margin),constraints)
    print(f"Atlas {atlas_id} on [{a},{b}], degree {degree}: "
          f"{len(allgrams)} Gram blocks, {nH*(degree+1)} equations; setup {time.time()-start:.1f}s",flush=True)
    if solver_name=='CLARABEL':
        problem.solve(solver='CLARABEL',max_iter=max_iters,tol_gap_abs=1e-9,tol_gap_rel=1e-9,
                      tol_feas=1e-9,verbose=True)
    else:
        problem.solve(solver='SCS',max_iters=max_iters,eps=1e-7,verbose=True)
    print(f"NUMERICAL ONLY status={problem.status}, margin={margin.value}, elapsed={time.time()-start:.1f}s",flush=True)
    if allgrams[0].value is not None:
        suffix='_reduced' if reduced else ''
        filename=WORK/f"atlas{atlas_id}_induced_interval_d{degree}_{solver_name}{suffix}.npz"
        np.savez(filename,left=str(a),right=str(b),degree=degree,multipliers=multipliers.value,
                 slack=slack.value,margin=margin.value,**{f'Q{i}':g.value for i,g in enumerate(allgrams)},
                 **{f'V{i}':g.value for i,g in enumerate(gramvariables)},
                 **{f'C{i}':c for i,c in enumerate(reductions)},
                 **{f'L{i}':l for i,(l,r) in enumerate(faces)},**{f'R{i}':r for i,(l,r) in enumerate(faces)})
        print(filename,flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--atlas',type=int,required=True)
    parser.add_argument('--left',required=True)
    parser.add_argument('--right',required=True)
    parser.add_argument('--degree',type=int,default=5)
    parser.add_argument('--max-iters',type=int,default=100)
    parser.add_argument('--solver',default='CLARABEL',choices=['CLARABEL','SCS'])
    parser.add_argument('--reduced',action='store_true')
    args=parser.parse_args()
    search(args.atlas,args.left,args.right,args.degree,args.max_iters,args.solver,args.reduced)
