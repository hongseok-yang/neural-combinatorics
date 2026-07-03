"""
sdp.py
======
Assemble and solve the Razborov flag SDP, using the VERIFIED conventions:

  * induced density basis at level N: graphs = all N-vertex iso classes.
  * quantum graph -> coef vector:  coef[H] = sum_alpha q_alpha * t_inj(F_alpha,H).
  * flag multiplication tables M_sigma(H) from flagalg.flag_multiplication_tables.

Certificate SDP:
    maximize   c
    s.t.  for every N-vertex graph H:
              coef[H] - c  -  sum_sigma <Q_sigma, M_sigma(H)>  >= 0
          Q_sigma  PSD.
Because sum_H p(H,W)=1 and p(H,W)>=0 for every graphon, feasibility implies
    f(W) = sum_H p(H,W) coef[H]
         = c + sum_H p(H,W)[ <Q_sigma,M_sigma(H)> + slack_H ]  >= c,
using sum_H p(H,W)<Q,M_sigma(H)> >= 0 (verified separately) and slack>=0.
So c is a valid certified lower bound on f over ALL graphons.

Optional multiplier: add  (p - 1/2) * sum_sigma <R_sigma, M_sigma(H)>  with
R_sigma>=0 -- valid because (p-1/2)>=0 is NOT always true, so we instead add
the multiplier only in the form that stays valid: we require the extra term to
be a nonneg-combination times a nonneg scalar.  Since p-1/2 can be negative,
the standard trick is to ADD a term  (p - 1/2)*g(W) where g(W)>=0 and to keep
the whole certificate an identity that is >= c for ALL W.  We implement the
"p>=1/2 branch" separately and the "p<=1/2 branch" is trivially nonneg, so the
multiplier variant certifies Delta2 >= c only on the p>=1/2 region by adding
(2p-1)>=0 times a nonneg flag combination -- see solve() docstring.
"""
import sys, os
import numpy as np
import cvxpy as cp

sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
import flagalg as fa
from test_identities import t_inj_in_graph


def coef_vector(quantum_graph, N, graphs):
    """quantum_graph: list of (coef, F_edges, F_nv).  Return coef[H]=sum coef*
    t_inj(F,H)."""
    m = len(graphs)
    c = np.zeros(m)
    for (q, E, nv) in quantum_graph:
        for i, H in enumerate(graphs):
            c[i] += q * t_inj_in_graph(E, nv, H)
    return c


def build_flag_data(N, type_specs):
    """type_specs: list of (m, edges) describing types.  Returns:
        graphs, [(sigma, flags, flag_keys, Mtabs), ...].
    ell chosen so 2*ell - m = N  =>  ell = (N+m)/2  (requires N+m even)."""
    graphs = fa.all_graphs_by_nauty_signature(N)
    blocks = []
    for (m, edges) in type_specs:
        assert (N + m) % 2 == 0, f"N+m must be even; N={N},m={m}"
        ell = (N + m) // 2
        sigma = fa.make_type(m, edges)
        flags, flag_keys, Mtabs = fa.flag_multiplication_tables(sigma, ell, N, graphs)
        blocks.append(dict(m=m, edges=edges, ell=ell, sigma=sigma,
                           flags=flags, flag_keys=flag_keys, Mtabs=Mtabs))
    return graphs, blocks


def solve(cvec, graphs, blocks, multiplier_blocks=None, p_vec=None,
          solver="CLARABEL", verbose=False):
    """Solve the max-lower-bound SDP.

    cvec[H]           : target coef vector.
    blocks            : flag blocks (each a dict with 'Mtabs').
    multiplier_blocks : optional flag blocks whose contribution is multiplied by
                        (2*p_H - 1)  where p_H = t(K2,H).  Valid ONLY as a
                        certificate on the region p>=1/2 (since (2p-1)>=0 there
                        and R>=0 => the term is >=0).  We report both.
    p_vec[H]          : t(K2,H) per graph (needed for multiplier).

    Returns dict with status, c (bound), and Q matrices.
    """
    nH = len(graphs)
    Qs = []
    constr = []
    for blk in blocks:
        nf = len(blk["flags"])
        Q = cp.Variable((nf, nf), symmetric=True)
        constr.append(Q >> 0)
        Qs.append(Q)
    Rs = []
    if multiplier_blocks:
        for blk in multiplier_blocks:
            nf = len(blk["flags"])
            R = cp.Variable((nf, nf), symmetric=True)
            constr.append(R >> 0)
            Rs.append(R)

    c = cp.Variable()
    for hidx in range(nH):
        expr = cvec[hidx] - c
        for Q, blk in zip(Qs, blocks):
            expr = expr - cp.sum(cp.multiply(Q, blk["Mtabs"][hidx]))
        if multiplier_blocks:
            mult = (2 * p_vec[hidx] - 1)
            for R, blk in zip(Rs, multiplier_blocks):
                expr = expr - mult * cp.sum(cp.multiply(R, blk["Mtabs"][hidx]))
        constr.append(expr >= 0)

    prob = cp.Problem(cp.Maximize(c), constr)
    prob.solve(solver=solver, verbose=verbose)
    out = dict(status=prob.status, c=(c.value if c.value is not None else None),
               Q=[Q.value for Q in Qs], R=[R.value for R in Rs])
    return out


def t_K2_in_graph(H):
    return t_inj_in_graph([(0, 1)], 2, H)
