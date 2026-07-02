"""
Exact gradient KERNEL of Delta2 at W_m via the homomorphism-density edge-deletion formula.

For any graph F and graphon W,
  d/dt t(F, W + tZ)|_0 = sum_{e in E(F)} t_{F\e}^{(pin e)}(Z, W)
where the pinned density fixes the two endpoints of e at (x,y), multiplies by Z(x,y),
and integrates the rest against W. Summing over edges gives the gradient KERNEL:
  grad t(F,.)(x,y) = sum_{e=(u,v) in E(F)} hom-density of F\e with vertices u,v pinned at x,y,
                     integrated over the OTHER vertices against W (symmetrized in x<->y).

We build this on the block chart symbolically with sympy. For W_m: masses 1/m, M=J-I.
Gradient kernel g(x,y) is a symmetric function; by S_m symmetry it is block-constant:
 value g_diag when x,y in same block, g_off when different blocks.

We compute grad Delta2 = grad t(Theta) - (2p-1) grad t(C5) - 2 t(C5) * grad p.
(product rule on the (2p-1) t(C5) term; grad(2p-1)=2 grad p, grad p kernel = 1 identically
 since p = int W, so grad p(x,y) = 1.)
"""
import sympy as sp

def build(m):
    # symbolic block matrix M (symmetric), masses 1/m
    r = m
    a, b = sp.symbols('a b')  # a = diag value, b = off value (we linearize around a=0,b=1)
    # We'll represent M entries as symbols and differentiate, then evaluate at frontier.
    Ms = sp.zeros(r,r)
    syms = {}
    for i in range(r):
        for j in range(i, r):
            s = sp.Symbol(f'M_{i}_{j}')
            syms[(i,j)] = s
            Ms[i,j]=s; Ms[j,i]=s
    w = sp.Matrix([sp.Rational(1,m)]*r)
    D = sp.diag(*w)
    MD = Ms*D
    T2 = MD*Ms
    T4 = MD*MD*MD*Ms
    p = (w.T*Ms*w)[0]
    # Delta2 = sum_ij w_i w_j M_ij (T2_ij - (2p-1)) T4_ij
    Delta2 = sp.Integer(0)
    for i in range(r):
        for j in range(r):
            Delta2 += w[i]*w[j]*Ms[i,j]*(T2[i,j]-(2*p-1))*T4[i,j]
    Delta2 = sp.expand(Delta2)
    return syms, Ms, w, Delta2

def eval_frontier(expr, syms, m):
    subs = {}
    for (i,j),s in syms.items():
        subs[s] = 0 if i==j else 1
    return sp.simplify(expr.subs(subs))

for m in [3,4]:
    syms, Ms, w, Delta2 = build(m)
    # gradient wrt entry M_ij. For i<j, entry appears as M_ij and M_ji (both = same symbol),
    # so dDelta2/dM_ij (treating symmetric symbol) already accounts for both since we set Ms[i,j]=Ms[j,i]=s.
    # The L2 gradient kernel value g_ij satisfies: dDelta2 = sum_{i<=j} (dDelta2/dsym_ij) dsym_ij.
    # In kernel terms, a perturbation Z with Z_ij on block(i,j): the entry sym_ij = M_ij, and
    #   Delta2 as function of sym; but note off-diagonal block (i,j) with i!=j has measure 2 w_i w_j
    #   (both (i,j) and (j,i)), diagonal block measure w_i^2.
    # So kernel value g_ij = (dDelta2/dsym_ij) / (measure of the symbol's support).
    #   diagonal i=i: measure w_i^2 = 1/m^2
    #   off i<j: the symbol sym_ij controls BOTH ordered pairs, total measure 2 w_i w_j = 2/m^2
    dii = sp.diff(Delta2, syms[(0,0)])
    dij = sp.diff(Delta2, syms[(0,1)])
    dii0 = eval_frontier(dii, syms, m)
    dij0 = eval_frontier(dij, syms, m)
    g_diag = dii0 / (sp.Rational(1,m)**2)      # divide by w_i^2
    g_off  = dij0 / (2*sp.Rational(1,m)**2)    # divide by 2 w_i w_j
    print(f"m={m}:")
    print(f"  dDelta2/dM_ii at frontier = {dii0}   -> g_diag = {sp.nsimplify(g_diag)} = {float(g_diag):.8f}")
    print(f"  dDelta2/dM_ij at frontier = {dij0}   -> g_off  = {sp.nsimplify(g_off)} = {float(g_off):.8f}")
