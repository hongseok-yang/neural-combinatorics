import numpy as np

rng = np.random.default_rng(0)

def check(n, m):
    # symmetric U in [0,1], uniform prob measure (weight 1/n each)
    A = rng.random((n, n)); U = (A + A.T) / 2
    one = np.ones(n)
    # operators as matrices: T_U f = (1/n) U f ;  J f = (1/n) ones f
    T = U / n
    J = np.ones((n, n)) / n
    B = J - T
    inner = lambda f, g: (f * g).sum() / n          # ∫ f g
    # cc_m = operator trace of B^m
    cc = np.trace(np.linalg.matrix_power(B, m)) * 1.0  # tr of operator = matrix trace
    # path iterates
    def Tpow_1(j):   # T_U^j 1
        v = one.copy()
        for _ in range(j): v = T @ v
        return v
    def Bpow_1(k):   # B^k 1
        v = one.copy()
        for _ in range(k): v = B @ v
        return v
    pc = lambda k: inner(one, Bpow_1(k))             # ⟨1, B^k 1⟩
    cden = np.trace(np.linalg.matrix_power(T, m)) * 1.0   # c_m = tr(T_U^m)
    # my formula
    rhs = pc(m - 1) + sum((-1)**j * inner(Tpow_1(j), Bpow_1(m - 1 - j)) for j in range(1, m)) \
          + (-1)**m * cden
    return cc, rhs

for n in [3, 4, 5]:
    for m in [3, 5, 7, 9]:
        cc, rhs = check(n, m)
        print(f"n={n} m={m}: cc={cc:.6f} formula={rhs:.6f} match={abs(cc-rhs)<1e-9}")
