"""
Symbolic Delta2 on the exact frontier + its degenerate axis, using a 3-block step graphon
that stays on the balanced-tripartite orbit but with a single scalar deformation toward
a complete-graph / bipartite structure. Concretely we look at the 1-parameter and
2-parameter families that pass through the frontier and are the 'tightest' directions,
and show Delta2 has a clean nonneg form.

Family A (edge-density-preserving symmetric structure): 3 blocks equal mass 1/3,
  M = [[d, o, o],[o,d,o],[o,o,d]]  (fully symmetric: diagonal d, offdiag o).
  This is the S3-symmetric slice. Frontier at (d,o)=(0,1). p = (1/3)d + (2/3)o.
  Compute Delta2(d,o) exactly and analyze on 0<=d,o<=1, p>=1/2.
"""
import sympy as sp
d,o=sp.symbols('d o',nonnegative=True)
M=sp.Matrix([[d,o,o],[o,d,o],[o,o,d]])
w=sp.Rational(1,3); D=w*sp.eye(3); wv=sp.Matrix([w,w,w])
p=sp.expand((wv.T*M*wv)[0,0])
MD=M*D; T2=MD*M; T4=MD*MD*MD*M; alpha=2*p-1
Delta=sp.Integer(0)
for i in range(3):
    for j in range(3):
        Delta+=w*w*M[i,j]*(T2[i,j]-alpha)*T4[i,j]
Delta=sp.expand(Delta)
Delta=sp.factor(Delta)
print("S3-symmetric slice: p =", p)
print("Delta2(d,o) =", Delta)
print()
# eigenvalues of M D on this slice: lam1 = w(d+2o)=p... check
lamd=sp.simplify(w*(d+2*o)); lamn=sp.simplify(w*(d-o))
print("eigenvalues: lam_top=",lamd," (mult1), lam=",lamn," (mult2)")
print("=> exactly {+,-,-} degenerate when d<o.")
print()
# Delta2 sign on region p>=1/2 i.e. d+2o>=3/2, 0<=d,o<=1:
Df=sp.factor(Delta)
print("factored Delta2:", Df)
