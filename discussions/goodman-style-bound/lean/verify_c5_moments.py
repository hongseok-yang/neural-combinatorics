import numpy as np, sympy as sp

# ---------- numeric validation of the moment formulas on a random graphon ----------
rng = np.random.default_rng(1)
n = 6
M = rng.random((n, n)); U = (M + M.T) / 2
ones = np.ones(n)
T = U / n
J = np.outer(ones, ones) / n
P = np.eye(n) - J
B = J - T
A = P @ T @ P
inner = lambda f, g: (f @ g) / n
deg = T @ ones
q = inner(ones, ones * 0 + deg)          # mean(deg) = ⟨1,deg⟩
g = deg - q * ones
def s(j):                                # s_j = ⟨g, A^j g⟩
    v = g.copy()
    for _ in range(j): v = A @ v
    return inner(g, v)
def pathFun(j):
    v = ones.copy()
    for _ in range(j): v = T @ v
    return v
def vcomp(k):
    v = ones.copy()
    for _ in range(k): v = B @ v
    return v
xden = lambda j: inner(ones, pathFun(j))
pcomp = lambda k: inner(ones, vcomp(k))
ip = lambda f, h: inner(f, h)
s0, s1, s2 = s(0), s(1), s(2)

# my hand-derived moment formulas
pc1 = 1 - q
pc2 = (1-q)**2 + s0
pc3 = (1-q)**3 + 2*(1-q)*s0 - s1
pc4 = (1-q)*pc3 + ((1-q)**2 + s0)*s0 - (1-q)*s1 + s2
ip13 = q*pc3 + (-((1-q)**2 + s0)*s0 + (1-q)*s1 - s2)
ip22 = (q**2+s0)*pc2 + (-q*(1-q)*s0 + q*s1 - (1-q)*s1 + s2)
ip31 = (q**3+2*q*s0+s1)*(1-q) + (-(q**2+s0)*s0 - q*s1 - s2)

print("pc1:", np.isclose(pc1, pcomp(1)), " pc2:", np.isclose(pc2, pcomp(2)),
      " pc3:", np.isclose(pc3, pcomp(3)), " pc4:", np.isclose(pc4, pcomp(4)))
print("ip13:", np.isclose(ip13, ip(pathFun(1), vcomp(3))),
      " ip22:", np.isclose(ip22, ip(pathFun(2), vcomp(2))),
      " ip31:", np.isclose(ip31, ip(pathFun(3), vcomp(1))))

# necklace check: ccomp5 = tr(B^5)
ccomp5 = np.trace(np.linalg.matrix_power(B, 5))
neck = pcomp(4) - ip(pathFun(1),vcomp(3)) + ip(pathFun(2),vcomp(2)) - ip(pathFun(3),vcomp(1)) \
       + xden(4) - np.trace(np.linalg.matrix_power(T,5))
print("necklace ccomp5:", np.isclose(ccomp5, neck))

# ---------- symbolic check: E5 - g5 == cert5 expr ----------
Q, S0, S1, S2 = sp.symbols('q s0 s1 s2')
pc1 = 1 - Q
pc2 = (1-Q)**2 + S0
pc3 = (1-Q)**3 + 2*(1-Q)*S0 - S1
pc4 = (1-Q)*pc3 + ((1-Q)**2 + S0)*S0 - (1-Q)*S1 + S2
ip13 = Q*pc3 + (-((1-Q)**2 + S0)*S0 + (1-Q)*S1 - S2)
ip22 = (Q**2+S0)*pc2 + (-Q*(1-Q)*S0 + Q*S1 - (1-Q)*S1 + S2)
ip31 = (Q**3+2*Q*S0+S1)*(1-Q) + (-(Q**2+S0)*S0 - Q*S1 - S2)
E5 = pc4 - ip13 + ip22 - ip31
P_ = 1 - Q
g5 = P_**5 - P_*(1-P_)**4
cert5 = 4*S0**2 + 4*S2 + (8*Q-5)*S1 + (12*Q**2 - 15*Q + 5)*S0
print("E5 - g5 == cert5 :", sp.expand(E5 - g5 - cert5) == 0)
