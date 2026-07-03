"""
A1 refined: bipartite equality manifold forces correction to vanish on all
bipartite graphons.  Surviving columns (vanish when t(C5)=0 / bipartite):
    m3  = diag(T3)-t(C3)
    m5  = diag(T5)-t(C5)
    m7  = MDR - <d,R>
    m8  = (d-p)Z
    m11 = (d-p)t(C3)
    m13 = (diag(T2)-t(C2))Z
(plus p-multiples of each).  Indices in frame basis: [2,4,6,7,10,12].

Step 1: verify these vanish on random bipartite step graphons; verify the
        excluded ones do NOT (=> they are forced to zero).
Step 2: solve T_k pinning restricted to allowed columns (with p-expansion).
Step 3: if solvable, run cutting-plane LP in the restricted space with the
        pinning equalities imposed; adversarial verification.
"""
import sys
sys.path.insert(0, "/private/tmp/cancel")
import numpy as np
from scipy.optimize import linprog, minimize
from frame import F_data, make_families

ALLOWED = [2, 4, 6, 7, 10, 12]
PEXPAND = True   # allow alpha_i(p) = a + b p + c p^2

def cols(dat):
    Mb = dat["basis"][:, ALLOWED]
    if PEXPAND:
        p = dat["p"]
        Mb = np.concatenate([Mb, p * Mb, p * p * Mb], axis=1)
    return Mb

def random_bipartite(rng, n1, n2):
    n = n1 + n2
    w = rng.random(n) + 0.1; w /= w.sum()
    M = np.zeros((n, n))
    M[:n1, n1:] = rng.random((n1, n2))
    M = M + M.T
    return w, M

def step1(rng):
    worst_allowed, worst_excluded = 0.0, 0.0
    for _ in range(50):
        w, M = random_bipartite(rng, int(rng.integers(1, 4)), int(rng.integers(1, 4)))
        dat = F_data(w, M)
        worst_allowed = max(worst_allowed, np.abs(dat["basis"][:, ALLOWED]).max())
        excl = [i for i in range(dat["basis"].shape[1]) if i not in ALLOWED]
        worst_excluded = max(worst_excluded, np.abs(dat["basis"][:, excl]).max())
        assert np.abs(dat["F"]).max() < 1e-14
    print(f"step1: max|allowed cols| on bipartite = {worst_allowed:.3e} (want 0); "
          f"max|excluded cols| = {worst_excluded:.3e} (nonzero => excluded forced to 0)")

def pinning(eps=1e-5, kmax=6):
    rowsA, rowsb = [], []
    for k in range(3, kmax + 1):
        M = 1.0 - np.eye(k); w0 = np.full(k, 1.0 / k)
        for j in range(1, k):
            eta = np.zeros(k); eta[0] = 1.0; eta[j] = -1.0
            dp = F_data(w0 + eps * eta, M); dm = F_data(w0 - eps * eta, M)
            dF = (dp["F"] - dm["F"]) / (2 * eps)
            dM = (cols(dp) - cols(dm)) / (2 * eps)
            for z in range(k):
                rowsA.append(dM[z]); rowsb.append(-dF[z])
    return np.array(rowsA), np.array(rowsb)

def solve_lp(rows_M, rows_F, Aeq, beq):
    nb = rows_M.shape[1]
    A_ub = np.concatenate([-rows_M, np.ones((rows_M.shape[0], 1))], axis=1)
    A_eq = np.concatenate([Aeq, np.zeros((Aeq.shape[0], 1))], axis=1)
    c = np.zeros(nb + 1); c[-1] = -1.0
    bounds = [(-50, 50)] * nb + [(None, None)]
    res = linprog(c, A_ub=A_ub, b_ub=rows_F, A_eq=A_eq, b_eq=beq,
                  bounds=bounds, method="highs")
    return (res.x[:nb], res.x[-1]) if res.success else (None, None)

def adversarial(alpha, rng, n_restarts=50):
    found = []
    for _ in range(n_restarts):
        n = int(rng.integers(2, 7))
        x0 = np.concatenate([rng.normal(0, 1, n), rng.normal(0, 2, (n*(n+1))//2)])
        iu = np.triu_indices(n)
        def unpack(x):
            a = x[:n]; s = np.clip(x[n:], -30, 30)
            w = np.exp(a - a.max()); w /= w.sum()
            Ms = np.zeros((n, n)); Ms[iu] = 1/(1+np.exp(-s))
            return w, Ms + Ms.T - np.diag(np.diag(Ms))
        def obj(x):
            dat = F_data(*unpack(x))
            return float(np.min(dat["F"] + cols(dat) @ alpha))
        res = minimize(obj, x0, method="Nelder-Mead",
                       options=dict(maxiter=4000, fatol=1e-13, xatol=1e-11))
        if res.fun < -1e-9:
            w, M = unpack(res.x)
            found.append((res.fun, w, M))
    return found

def main():
    rng = np.random.default_rng(11)
    step1(rng)
    Aeq, beq = pinning()
    sol, res_, rank, sv = np.linalg.lstsq(Aeq, beq, rcond=None)
    r = Aeq @ sol - beq
    print(f"step2: pinning system {Aeq.shape}, rank {rank}, max resid {np.abs(r).max():.3e}")
    if np.abs(r).max() > 1e-7:
        print("  -> T_k pinning UNSOLVABLE in bipartite-admissible basis. ROUTE DEAD.")
        return
    print("  -> solvable; nullspace dim =", Aeq.shape[1] - rank)
    pool = [F_data(w, M) for (w, M) in make_families(rng, 300)]
    for rnd in range(25):
        rows_M = np.concatenate([cols(d) for d in pool])
        rows_F = np.concatenate([d["F"] for d in pool])
        alpha, t = solve_lp(rows_M, rows_F, Aeq, beq)
        if alpha is None:
            print(f"round {rnd}: LP infeasible (with pinning equalities). ROUTE DEAD."); return
        print(f"round {rnd}: slack t = {t:.3e}, |alpha|_inf = {np.abs(alpha).max():.3f}")
        if t < -1e-8:
            print("  -> LP says max slack < 0 on finite pool: ROUTE DEAD."); return
        found = adversarial(alpha, rng)
        if not found:
            print("  adversarial found no violation. CANDIDATE alpha (allowed cols, x3 p-powers):")
            print("  ", np.array2string(alpha, precision=6))
            np.save("/private/tmp/cancel/alpha_candidate.npy", alpha)
            return
        worst = min(f[0] for f in found)
        print(f"  adversarial: {len(found)} violators, worst {worst:.3e}")
        for f, w, M in found:
            pool.append(F_data(w, M))
    print("rounds exhausted; still finding violators -> inconclusive/likely dead")

if __name__ == "__main__":
    main()
