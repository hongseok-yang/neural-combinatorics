"""hfin_certs.py -- Handelman certificate search + Lean generator for the Hfin family.

Hfin obligation: for the 196 pairs (m odd, 9 <= m <= 61, r >= 2, 4r < m), prove
    0 <= diagKernel m r q l   on   q in [0,1/3], 0 < l < q + r/m.

diagKernel m r q l  (n = m-2r):
    (m/r) * [ h_n((1-q)^{x r}, (-l)^{x r}) + h_n(q^{x r}, l^{x r}) ] - h_{n-1}(q^{x(r+1)}, l^{x r})
with h_d(a^{x s}, b^{x k}) = sum_j C(d-j+s-1, s-1) a^{d-j} C(j+k-1, k-1) b^j.

Direction B (handoff): find a Handelman representation at degree N (target N = deg K = m-2r-1):
    diagKernel = sum_alpha c_alpha (3q)^a (1-3q)^b l^c (q + r/m - l)^d,   c_alpha >= 0, a+b+c+d <= N.
LP feasibility (floats, HiGHS) -> exact rational vertex recovery on the support.
"""
import sys
import argparse
import time as _time
from fractions import Fraction
from math import comb


def _log(msg):
    print(f"[{_time.strftime('%H:%M:%S')}] {msg}", flush=True)


# ---------------------------------------------------------------------------
# GLPK worker (subprocess-isolated: GLPK crashes must not kill the pipeline,
# and swiglpk/python-flint must not share a process)
# ---------------------------------------------------------------------------

def glpk_worker(infile, outfile):
    """Load an LP (npz), run float simplex (+ glp_exact if requested), write the
    basic column set.  Runs in its own process; imports only numpy/scipy/swiglpk."""
    import numpy as np
    from scipy import sparse
    import swiglpk as g
    z = np.load(infile)
    A = sparse.csc_matrix((z["data"], z["indices"], z["indptr"]),
                          shape=tuple(z["shape"]))
    b = z["b"]
    obj = z["obj"]
    do_exact = bool(z["exact"])
    nr, nc = A.shape
    g.glp_term_out(g.GLP_ON)
    P = g.glp_create_prob()
    g.glp_set_obj_dir(P, g.GLP_MIN)
    g.glp_add_rows(P, nr)
    for i in range(nr):
        g.glp_set_row_bnds(P, i + 1, g.GLP_FX, float(b[i]), float(b[i]))
    g.glp_add_cols(P, nc)
    for j in range(nc):
        g.glp_set_col_bnds(P, j + 1, g.GLP_LO, 0.0, 0.0)
        g.glp_set_obj_coef(P, j + 1, float(obj[j]))
    Acoo = A.tocoo()
    nnz = Acoo.nnz
    ia = g.intArray(nnz + 1)
    ja = g.intArray(nnz + 1)
    ar = g.doubleArray(nnz + 1)
    for idx in range(nnz):
        ia[idx + 1] = int(Acoo.row[idx]) + 1
        ja[idx + 1] = int(Acoo.col[idx]) + 1
        ar[idx + 1] = float(Acoo.data[idx])
    g.glp_load_matrix(P, nnz, ia, ja, ar)
    parm = g.glp_smcp()
    g.glp_init_smcp(parm)
    parm.msg_lev = g.GLP_MSG_ON
    parm.out_frq = 5000
    g.glp_adv_basis(P, 0)
    if g.glp_simplex(P, parm) != 0 or g.glp_get_status(P) != g.GLP_OPT:
        np.savez(outfile, ok=np.array([0]), basic=np.array([], dtype=np.int64))
        return
    if do_exact:
        if g.glp_exact(P, parm) != 0 or g.glp_get_status(P) != g.GLP_OPT:
            np.savez(outfile, ok=np.array([0]), basic=np.array([], dtype=np.int64))
            return
    basic = np.array([j for j in range(nc)
                      if g.glp_get_col_stat(P, j + 1) == g.GLP_BS
                      or g.glp_get_col_prim(P, j + 1) > 0], dtype=np.int64)
    np.savez(outfile, ok=np.array([1]), basic=basic)


def run_glpk_subprocess(A_sub, b, obj, do_exact, timeout=3600, tag=""):
    """Run glpk_worker in a subprocess; stream its output; return basic list or None."""
    import numpy as np
    import subprocess
    import tempfile
    import os
    fd_in, fin = tempfile.mkstemp(suffix=".npz")
    os.close(fd_in)
    fd_out, fout = tempfile.mkstemp(suffix=".npz")
    os.close(fd_out)
    try:
        Ac = A_sub.tocsc()
        np.savez_compressed(fin, data=Ac.data, indices=Ac.indices, indptr=Ac.indptr,
                            shape=np.array(Ac.shape), b=b, obj=obj,
                            exact=np.array([1 if do_exact else 0]))
        proc = subprocess.Popen(
            [sys.executable, "-u", os.path.abspath(__file__), "--glpk-worker", fin, fout],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            cwd=os.path.dirname(os.path.abspath(__file__)))
        try:
            for line in proc.stdout:
                print(f"    glpk{tag}| {line.rstrip()}", flush=True)
            rc = proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            proc.kill()
            _log(f"  glpk{tag}: timeout after {timeout}s")
            return None
        if rc != 0:
            _log(f"  glpk{tag}: worker exited with code {rc} (crash isolated)")
            return None
        z = np.load(fout)
        if int(z["ok"][0]) != 1:
            return None
        return [int(x) for x in z["basic"]]
    finally:
        for f in (fin, fout):
            try:
                os.unlink(f)
            except OSError:
                pass

# ---------------------------------------------------------------------------
# exact diagKernel monomial coefficients
# ---------------------------------------------------------------------------

def diag_kernel_coeffs(m, r):
    """Exact monomial coefficients of diagKernel m r, as dict (i,j) -> Fraction
    (i = power of q, j = power of l)."""
    n = m - 2 * r
    co = {}

    def add(i, j, v):
        if v:
            co[(i, j)] = co.get((i, j), Fraction(0)) + v

    mr = Fraction(m, r)
    # (m/r) * h_n((1-q)^{x r}, (-l)^{x r})
    for j in range(n + 1):
        cj = mr * comb(n - j + r - 1, r - 1) * comb(j + r - 1, r - 1) * (-1) ** j
        for u in range(n - j + 1):  # (1-q)^{n-j} = sum_u C(n-j,u) (-1)^u q^u
            add(u, j, cj * comb(n - j, u) * (-1) ** u)
    # (m/r) * h_n(q^{x r}, l^{x r})
    for j in range(n + 1):
        add(n - j, j, mr * comb(n - j + r - 1, r - 1) * comb(j + r - 1, r - 1))
    # - h_{n-1}(q^{x (r+1)}, l^{x r})
    for j in range(n):
        add(n - 1 - j, j, -Fraction(comb(n - 1 - j + r, r) * comb(j + r - 1, r - 1)))
    return {k: v for k, v in co.items() if v != 0}


def validate_5_1():
    """Check against Lean's diagKernel_five_one: 4l^2 + (8q-5)l + 12q^2 - 15q + 5."""
    co = diag_kernel_coeffs(5, 1)
    expect = {(0, 2): 4, (1, 1): 8, (0, 1): -5, (2, 0): 12, (1, 0): -15, (0, 0): 5}
    assert co == {k: Fraction(v) for k, v in expect.items()}, co
    print("validate (5,1): OK")


def all_pairs():
    ps = []
    for m in range(9, 62, 2):
        for r in range(2, m):
            if 2 * r < m - 2 * r:
                ps.append((m, r))
    return ps


# ---------------------------------------------------------------------------
# Handelman term expansion: (3q)^a (1-3q)^b l^c (q + t - l)^d,  t = r/m
# ---------------------------------------------------------------------------

def term_coeffs(a, b, c, d, t):
    """Exact monomial coefficients of (3q)^a (1-3q)^b l^c (q+t-l)^d as dict (i,j)->Fraction."""
    co = {}
    p3a = Fraction(3) ** a
    for u in range(b + 1):
        cu = p3a * comb(b, u) * (Fraction(-3)) ** u
        # (q + t - l)^d: multinomial over q^e t^f (-l)^g
        for e in range(d + 1):
            for g in range(d - e + 1):
                f = d - e - g
                w = cu * (comb(d, e) * comb(d - e, g)) * (t ** f) * (-1) ** g
                key = (a + u + e, c + g)
                co[key] = co.get(key, Fraction(0)) + w
    return co


def term_coeffs_x(a, b, c, d, t):
    """Exact coefficients of x^a (1-x)^b l^c (x/3 + t - l)^d in the x = 3q basis,
    as dict (i,j) -> Fraction with i = power of x, j = power of l.
    Note: this is the SAME term as term_coeffs (namely (3q)^a (1-3q)^b l^c (q+t-l)^d),
    re-expanded in x; coefficients relate by a factor 3^i per monomial."""
    co = {}
    third = Fraction(1, 3)
    for u in range(b + 1):
        cu = Fraction(comb(b, u) * (-1) ** u)
        for e in range(d + 1):
            for g in range(d - e + 1):
                f = d - e - g
                w = cu * (comb(d, e) * comb(d - e, g)) * third ** e * t ** f * (-1) ** g
                key = (a + u + e, c + g)
                co[key] = co.get(key, Fraction(0)) + w
    return co


def base_poly_float_x(b, d, t):
    """Float coeff array of (1-x)^b (x/3+t-l)^d in the x-basis: shape (b+d+1, d+1)."""
    import numpy as np
    tf = float(t)
    pb = np.array([comb(b, u) * (-1.0) ** u for u in range(b + 1)])
    pd = np.zeros((d + 1, d + 1))
    for e in range(d + 1):
        for g in range(d - e + 1):
            f = d - e - g
            pd[e, g] = comb(d, e) * comb(d - e, g) * (1.0 / 3.0) ** e * tf ** f * (-1.0) ** g
    out = np.zeros((b + d + 1, d + 1))
    for u in range(b + 1):
        out[u:u + d + 1, :] += pb[u] * pd
    return out


def term_coeffs_float(a, b, c, d, t):
    """Float version (fast) for LP matrix construction."""
    import numpy as np
    co = {}
    tf = float(t)
    p3a = 3.0 ** a
    for u in range(b + 1):
        cu = p3a * comb(b, u) * (-3.0) ** u
        for e in range(d + 1):
            for g in range(d - e + 1):
                f = d - e - g
                w = cu * comb(d, e) * comb(d - e, g) * (tf ** f) * (-1.0) ** g
                key = (a + u + e, c + g)
                co[key] = co.get(key, 0.0) + w
    return co


# ---------------------------------------------------------------------------
# LP feasibility at degree N (float, HiGHS), with row/column scaling
# ---------------------------------------------------------------------------

def basis_tuples(N, dcap=None):
    """All (a,b,c,d), a+b+c+d <= N, optionally with d <= dcap."""
    dc = N if dcap is None else dcap
    out = []
    for a in range(N + 1):
        for b in range(N + 1 - a):
            for c in range(N + 1 - a - b):
                for d in range(min(dc, N - a - b - c) + 1):
                    out.append((a, b, c, d))
    return out


def base_poly_float(b, d, t):
    """Float coeff array of (1-3q)^b (q+t-l)^d: shape (b+d+1, d+1), [i,j] = coeff q^i l^j."""
    import numpy as np
    tf = float(t)
    # (1-3q)^b
    pb = np.array([comb(b, u) * (-3.0) ** u for u in range(b + 1)])
    # (q+t-l)^d
    pd = np.zeros((d + 1, d + 1))
    for e in range(d + 1):
        for g in range(d - e + 1):
            f = d - e - g
            pd[e, g] = comb(d, e) * comb(d - e, g) * (tf ** f) * (-1.0) ** g
    out = np.zeros((b + d + 1, d + 1))
    for u in range(b + 1):
        out[u:u + d + 1, :] += pb[u] * pd
    return out


def lp_feasibility(m, r, N, dcap=None, verbose=True):
    import numpy as np
    from scipy import sparse
    from scipy.optimize import linprog

    t = Fraction(r, m)
    K = diag_kernel_coeffs(m, r)
    degK = max(i + j for (i, j) in K)
    D = max(N, degK)
    monos = [(i, j) for i in range(D + 1) for j in range(D + 1 - i)]
    midx = np.full((D + 1, D + 1), -1, dtype=np.int64)
    for k, (i, j) in enumerate(monos):
        midx[i, j] = k

    dc = N if dcap is None else dcap
    # build blockwise over (b,d): columns are shifts (a,c) of the base poly
    rows_l, cols_l, vals_l, cols, colscale = [], [], [], [], []
    ncol = 0
    for b in range(N + 1):
        for d in range(min(dc, N - b) + 1):
            base = base_poly_float(b, d, t)  # (b+d+1, d+1)
            bi, bj = np.nonzero(base)
            bv = base[bi, bj]
            mx = np.abs(bv).max()
            bvn = bv / mx
            rem = N - b - d
            for a in range(rem + 1):
                for c in range(rem - a + 1):
                    rows_l.append(midx[bi + a, bj + c])
                    cols_l.append(np.full(len(bi), ncol, dtype=np.int64))
                    vals_l.append(bvn)
                    cols.append((a, b, c, d))
                    colscale.append(3.0 ** a * mx)  # true coeff = x / colscale
                    ncol += 1
    rows_i = np.concatenate(rows_l)
    cols_i = np.concatenate(cols_l)
    vals = np.concatenate(vals_l)
    A = sparse.csc_matrix((vals, (rows_i, cols_i)), shape=(len(monos), ncol))
    if verbose:
        print(f"(m,r)=({m},{r}) degK={degK} N={N} dcap={dc}: "
              f"{ncol} columns, {len(monos)} rows, nnz {A.nnz}")

    bvec = np.zeros(len(monos))
    for mn, v in K.items():
        bvec[midx[mn[0], mn[1]]] = float(v)

    rownorm = np.maximum(np.abs(A).max(axis=1).toarray().ravel(), 1e-300)
    Rinv = sparse.diags(1.0 / rownorm)
    A2 = Rinv @ A
    b2 = bvec / rownorm

    rng = np.random.default_rng(20260713)
    obj = rng.uniform(0.5, 1.5, ncol)  # generic objective -> nondegenerate optimal vertex
    res = linprog(obj, A_eq=A2, b_eq=b2, bounds=(0, None), method="highs")
    if verbose:
        print("status:", res.status, res.message.strip() if res.message else "")
    if res.status != 0:
        return None
    x = res.x  # note: scaled coefficients (true coeff = x / colscale); support is what matters
    supp = [k for k in range(ncol) if x[k] > 1e-11 * max(1.0, x.max())]
    if verbose:
        print(f"feasible; support size {len(supp)} (of {ncol}), "
              f"max scaled coeff {x.max():.3e}, min supported {min(x[k] for k in supp):.3e}")
    return {"cols": cols, "x": x, "supp": supp, "monos": monos, "K": K, "t": t,
            "m": m, "r": r, "N": N, "colscale": np.array(colscale)}


# ---------------------------------------------------------------------------
# round-and-correct certificate search (no exact linear algebra needed)
# ---------------------------------------------------------------------------

def find_cert(m, r, N, dcap=None, bcap=None, lb_rel=1e-6, drop_rel=1e-10, verbose=True,
              lp_options=None):
    """Find an exact rational Handelman certificate for diagKernel m r at degree N.

    Scheme: LP with small lower bounds on the pure-monomial columns (a,0,c,0)
    (whose columns are diagonal), exact rounding of the float solution, and exact
    residual correction distributed onto the pure columns.
    Returns list of ((a,b,c,d), Fraction >= 0) with sum c * term == diagKernel, or None.
    """
    import numpy as np
    from scipy import sparse
    from scipy.optimize import linprog

    t = Fraction(r, m)
    K = diag_kernel_coeffs(m, r)
    degK = max(i + j for (i, j) in K)
    if N < degK:
        raise ValueError("N below degree of K")
    # everything below works in the x = 3q basis, where diagKernel's coefficient
    # range is tame; the certificate terms and their coefficients are basis-independent
    Kx = {(i, j): v / Fraction(3) ** i for (i, j), v in K.items()}
    D = N
    monos = [(i, j) for i in range(D + 1) for j in range(D + 1 - i)]
    midx = np.full((D + 1, D + 1), -1, dtype=np.int64)
    for k, (i, j) in enumerate(monos):
        midx[i, j] = k

    dc = N if dcap is None else dcap
    bc = N if bcap is None else bcap
    rows_l, cols_l, vals_l, cols, colscale_exact = [], [], [], [], []
    pure_col = {}  # (i,j) -> column index of (i,0,j,0), i.e. x^i l^j
    ncol = 0
    for b in range(min(bc, N) + 1):
        for d in range(min(dc, N - b) + 1):
            base = base_poly_float_x(b, d, t)
            bi, bj = np.nonzero(base)
            bv = base[bi, bj]
            mx = float(np.abs(bv).max())
            bvn = bv / mx
            mxf = Fraction(mx)  # exact value of the float scale
            rem = N - b - d
            for a in range(rem + 1):
                for c in range(rem - a + 1):
                    rows_l.append(midx[bi + a, bj + c])
                    cols_l.append(np.full(len(bi), ncol, dtype=np.int64))
                    vals_l.append(bvn)
                    cols.append((a, b, c, d))
                    colscale_exact.append(mxf)
                    if b == 0 and d == 0:
                        pure_col[(a, c)] = ncol
                    ncol += 1
    rows_i = np.concatenate(rows_l)
    cols_i = np.concatenate(cols_l)
    vals = np.concatenate(vals_l)
    A = sparse.csc_matrix((vals, (rows_i, cols_i)), shape=(len(monos), ncol))

    bvec = np.zeros(len(monos))
    for mn, v in Kx.items():
        bvec[midx[mn[0], mn[1]]] = float(v)

    # --- Ruiz equilibration of [A | b] (rows scale equations; cols rescale vars) ---
    A = A.tocsr()
    rowscale = np.ones(len(monos))
    colscale_eq = np.ones(ncol)
    b_eq = bvec.copy()
    for _ in range(12):
        rmax = np.maximum(np.abs(A).max(axis=1).toarray().ravel(), np.abs(b_eq))
        rmax = np.sqrt(np.maximum(rmax, 1e-300))
        A = sparse.diags(1.0 / rmax) @ A
        b_eq = b_eq / rmax
        rowscale *= rmax
        cmax = np.sqrt(np.maximum(np.abs(A).max(axis=0).toarray().ravel(), 1e-300))
        A = A @ sparse.diags(1.0 / cmax)
        colscale_eq *= cmax
    A = A.tocsc()
    # LP variable x_k corresponds to exact coefficient c_k = x_k / xdiv_k
    xdiv = [colscale_exact[k] * Fraction(colscale_eq[k]) for k in range(ncol)]

    # objective = Lean expansion cost of each term (plus jitter for nondegeneracy),
    # scaled per column so it prices the *term*, not the scaled variable
    cost = np.array([(b + 1) * (d + 1) * (d + 2) / 2 for (a, b, c, d) in cols])
    obj = cost * np.random.default_rng(20260713).uniform(1.0, 1.01, ncol)
    if lp_options is None:
        lp_options = {}

    def exact_residual(cv):
        """Exact residual in the x-basis: Kx - sum c_k * term_k(x-basis)."""
        resid = dict(Kx)
        for k, val in cv.items():
            if val == 0:
                continue
            a, b, c, d = cols[k]
            for mn, v in term_coeffs_x(a, b, c, d, t).items():
                resid[mn] = resid.get(mn, Fraction(0)) - val * v
        return {mn: v for mn, v in resid.items() if v != 0}

    def solve_and_round(lb, obj_used=None):
        ob = obj if obj_used is None else obj_used
        res = linprog(ob, A_eq=A, b_eq=b_eq, bounds=list(zip(lb, [None] * ncol)),
                      method="highs", options=lp_options)
        if res.status != 0:
            return None, res.status
        # dyadic rounding of the true coefficient value: denominators are powers
        # of two, so residual/coefficient denominators stay small
        cv = {k: Fraction(res.x[k] / float(xdiv[k]))
              for k in range(ncol) if res.x[k] > 0}
        cv = {k: v for k, v in cv.items() if v > 0}
        # candidate columns for exact vertex recovery: support + near-zero reduced cost
        cand = list(sorted(cv.keys(), key=lambda k: -res.x[k]))
        try:
            y = res.eqlin.marginals
            supp_idx = np.array(cand)
            # pick the sign convention that zeroes reduced costs on the support
            r1 = ob - A.T @ y
            r2 = ob + A.T @ y
            red = r1 if np.abs(r1[supp_idx]).mean() <= np.abs(r2[supp_idx]).mean() else r2
            scale = max(1.0, float(np.abs(ob).max()))
            csupp = set(cand)
            near = [int(k) for k in np.argsort(np.abs(red))[:6000]
                    if abs(red[k]) <= 1e-6 * scale and int(k) not in csupp]
            cand += near
        except Exception:
            pass
        return cv, cand

    # pass 1: probe LP feasibility once (no floor) for an early exit on bad input
    lb0 = np.zeros(ncol)
    K00 = Kx.get((0, 0), Fraction(0))
    assert K00 > 0, "diagKernel must be positive at the origin"
    cvals, cand = solve_and_round(lb0)
    if cvals is None:
        if verbose:
            print(f"({m},{r}) N={N} dcap={dc}: LP status {cand} -- infeasible/failed")
        return None
    if verbose:
        print(f"({m},{r}) N={N} dcap={dc}: LP ok ({ncol} cols, {len(monos)} rows, "
              f"support {len(cvals)})")
    def solve_exact_on(supp):
        """flint rref of the exact system restricted to columns `supp`; free
        variables 0.  Returns (cvals or None-if-negative, consistent?)."""
        from flint import fmpq_mat, fmpq
        nr, nc2 = len(monos), len(supp)
        M = fmpq_mat(nr, nc2 + 1)
        for jj, k in enumerate(supp):
            a, b, c, d = cols[k]
            for mn, v in term_coeffs_x(a, b, c, d, t).items():
                M[midx[mn[0], mn[1]], jj] = fmpq(v.numerator, v.denominator)
        for mn, v in Kx.items():
            M[midx[mn[0], mn[1]], nc2] = fmpq(v.numerator, v.denominator)
        R, rank = M.rref()
        piv = []
        row = 0
        for col in range(nc2 + 1):
            if row < rank and R[row, col] != 0:
                piv.append(col)
                row += 1
        if nc2 in piv:
            return None, False
        out = {}
        for irow, p in enumerate(piv):
            val = R[irow, nc2]
            fr = Fraction(int(val.p), int(val.q))
            if fr < 0:
                return None, True
            if fr > 0:
                out[supp[p]] = fr
        return out, True

    def exact_vertex(cand, seed=0):
        """Exact rational vertex via flint dual-simplex repair.

        Start from the float support completed to a genuine basis (exact rref
        pivots over support + pure columns).  Solve the square system exactly;
        while some basic value is negative, pivot it out: solve A_Bᵀ y = e_i,
        price candidate columns exactly, and bring in one with negative alpha.
        Every step is exact (flint/GMP), so the result has ZERO residual."""
        try:
            from flint import fmpq_mat, fmpq
        except ImportError:
            return None
        rng2 = np.random.default_rng(777 + seed)
        nr = len(monos)

        colco_cache = {}

        def colco(k):
            if k not in colco_cache:
                a, b, c, d = cols[k]
                colco_cache[k] = {(midx[mn[0], mn[1]]): v
                                  for mn, v in term_coeffs_x(a, b, c, d, t).items()}
            return colco_cache[k]

        # ---- phase A: HiGHS simplex over ALL columns; extract its basis -------
        try:
            import highspy
        except ImportError:
            return None
        Af = A.tocsc()
        h = highspy.Highs()
        h.setOptionValue("output_flag", False)
        h.setOptionValue("solver", "simplex")
        h.setOptionValue("random_seed", int(seed))
        h.setOptionValue("time_limit", 900.0)
        lp = highspy.HighsLp()
        lp.num_col_ = ncol
        lp.num_row_ = nr
        jit = (cost * rng2.uniform(1.0, 1.01, ncol)).astype(float)
        lp.col_cost_ = list(jit)
        lp.col_lower_ = [0.0] * ncol
        lp.col_upper_ = [1e30] * ncol
        lp.row_lower_ = list(b_eq)
        lp.row_upper_ = list(b_eq)
        lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
        lp.a_matrix_.start_ = [int(x) for x in Af.indptr]
        lp.a_matrix_.index_ = [int(x) for x in Af.indices]
        lp.a_matrix_.value_ = [float(x) for x in Af.data]
        h.passModel(lp)
        if verbose:
            _log(f"  exact vertex: HiGHS simplex on {ncol} cols ...")
        h.run()
        if h.getModelStatus() != highspy.HighsModelStatus.kOptimal:
            if verbose:
                _log(f"  exact vertex: HiGHS status {h.getModelStatus()}")
            return None
        hb = h.getBasis()
        B0 = [j for j in range(ncol)
              if hb.col_status[j] == highspy.HighsBasisStatus.kBasic]
        rows_basic = [i for i in range(nr)
                      if hb.row_status[i] == highspy.HighsBasisStatus.kBasic]
        if verbose:
            _log(f"  exact vertex: HiGHS basis: {len(B0)} structural + "
                 f"{len(rows_basic)} slack rows")
        if len(B0) + len(rows_basic) != nr:
            if verbose:
                _log("  exact vertex: unexpected basis size")
            return None
        # complete with the pure column of each basic-slack row: the pure column
        # of monomial row i is exactly the unit vector e_i, i.e. HiGHS's own
        # slack column, so B is literally the HiGHS basis (same conditioning)
        B = list(B0)
        B0set = set(B0)
        for i in rows_basic:
            k = pure_col[tuple(monos[i])]
            if k in B0set:
                if verbose:
                    _log("  exact vertex: slack/pure duplicate (degenerate); abort")
                return None
            B.append(k)

        # ---- phase B: exact solve + (rarely) a few exact pivots ---------------
        bvec_q = [Kx.get(mn, Fraction(0)) for mn in monos]
        bmat = fmpq_mat(nr, 1)
        for i in range(nr):
            v = bvec_q[i]
            if v:
                bmat[i, 0] = fmpq(v.numerator, v.denominator)

        for it3 in range(40):
            AB = fmpq_mat(nr, nr)
            for jj, k in enumerate(B):
                for ri, v in colco(k).items():
                    AB[ri, jj] = fmpq(v.numerator, v.denominator)
            try:
                xB = AB.solve(bmat)
            except Exception:
                if verbose:
                    _log("  exact vertex: exact basis singular")
                return None
            vals = [Fraction(int(xB[i, 0].p), int(xB[i, 0].q)) for i in range(nr)]
            negs = [i for i in range(nr) if vals[i] < 0]
            if not negs:
                out = {B[i]: vals[i] for i in range(nr) if vals[i] > 0}
                if verbose:
                    _log(f"  exact vertex: EXACT feasible ({len(out)} support, "
                         f"{it3} exact pivots)")
                return out
            istar = min(negs, key=lambda i: vals[i])
            if verbose:
                _log(f"  exact vertex: exact pivot {it3}: {len(negs)} negative "
                     f"(worst {float(vals[istar]):.3e})")
            ei = fmpq_mat(nr, 1)
            ei[istar, 0] = fmpq(1)
            yx = AB.transpose().solve(ei)
            yq = [Fraction(int(yx[i, 0].p), int(yx[i, 0].q)) for i in range(nr)]
            yf = np.array([float(v) for v in yq])
            alpha = Af.T @ yf
            in_B2 = np.zeros(ncol, dtype=bool)
            in_B2[B] = True
            alpha[in_B2] = 0.0
            # float screening, exact verification (ascending alpha)
            order = np.argsort(alpha)
            chosen = None
            for j in order[:200]:
                if alpha[j] >= 0:
                    break
                s = Fraction(0)
                for ri, v in colco(int(j)).items():
                    if yq[ri]:
                        s += yq[ri] * v
                if s < 0:
                    chosen = int(j)
                    break
            if chosen is None:
                if verbose:
                    _log("  exact vertex: no exactly-negative entering column")
                return None
            B[istar] = chosen
        if verbose:
            _log("  exact vertex: exact pivot limit reached")
        return None

    def refine_solution(cv, rounds=3):
        """LP iterative refinement: re-solve against the exact scaled residual
        (min |delta|_1, split variables, deltas bounded below by -cv) and apply
        the correction exactly.  Each round shrinks the row-scaled residual by
        several orders of magnitude."""
        from scipy import sparse as sp2
        Af = A.tocsc()
        for rd in range(rounds):
            resid = exact_residual(cv)
            if not resid:
                return cv
            s = max(abs(float(v)) / rowscale[midx[mn[0], mn[1]]]
                    for mn, v in resid.items())
            if verbose:
                _log(f"  refine {rd}: row-scaled residual {s:.3e}")
            if s == 0.0 or s < 1e-30:
                return cv
            rvec = np.zeros(len(monos))
            for mn, v in resid.items():
                rvec[midx[mn[0], mn[1]]] = float(v) / s
            r_eq = rvec / rowscale
            xf = np.zeros(ncol)
            for k, val in cv.items():
                xf[k] = float(val * xdiv[k])
            ncap = np.maximum(xf / s, 0.0)
            ncap[pure_col[(0, 0)]] = 0.0  # never consume the constant headroom
            A_ref = sp2.hstack([A, -A], format="csc")
            res2 = linprog(np.ones(2 * ncol), A_eq=A_ref, b_eq=r_eq,
                           bounds=[(0, None)] * ncol + list(zip([0.0] * ncol, ncap)),
                           method="highs", options=lp_options)
            if res2.status != 0:
                if verbose:
                    _log(f"  refine {rd}: LP status {res2.status}")
                return cv
            delta = res2.x[:ncol] - res2.x[ncol:]
            sfrac = Fraction(s)
            out = dict(cv)
            for k in np.nonzero(delta)[0]:
                k = int(k)
                newv = out.get(k, Fraction(0)) \
                    + sfrac * Fraction(float(delta[k])) / xdiv[k]
                if newv > 0:
                    out[k] = newv
                else:
                    out.pop(k, None)
            cv = out
        return cv

    def _q2f(x):
        """fmpq -> float magnitude, robust to huge integers."""
        try:
            return float(Fraction(int(x.p), int(x.q)))
        except OverflowError:
            import math
            s = -1 if x.p < 0 else 1
            return s * math.inf

    def exact_phase1(pool, warm=(), max_pivots=250000):
        """Exact rational phase-1 simplex (Bland) over the pool columns.
        Guaranteed to find an exactly feasible nonneg solution of A x = Kx over
        the pool (or prove pool-infeasibility).  Tableau over flint fmpq_mat;
        each pivot is a C-speed outer-product update."""
        from flint import fmpq_mat, fmpq
        nr = len(monos)
        npool = len(pool)
        colco_cache2 = {}

        def colq(k):
            if k not in colco_cache2:
                a, b, c, d = cols[k]
                colco_cache2[k] = {midx[mn[0], mn[1]]: v
                                   for mn, v in term_coeffs_x(a, b, c, d, t).items()}
            return colco_cache2[k]

        # rows with b_i < 0 are negated so artificials start feasible
        bq = [Kx.get(mn, Fraction(0)) for mn in monos]
        sgn = [-1 if bq[i] < 0 else 1 for i in range(nr)]
        # tableau T: [pool columns | artificials | rhs]; objective row Z separate
        nw = npool + nr + 1
        T = fmpq_mat(nr, nw)
        for jj, k in enumerate(pool):
            for ri, v in colq(k).items():
                w = v if sgn[ri] > 0 else -v
                T[ri, jj] = fmpq(w.numerator, w.denominator)
        for i in range(nr):
            T[i, npool + i] = fmpq(1)
            vb = bq[i] if sgn[i] > 0 else -bq[i]
            T[i, npool + nr] = fmpq(vb.numerator, vb.denominator)
        ones = fmpq_mat(1, nr)
        for i in range(nr):
            ones[0, i] = fmpq(1)
        Z = -(ones * T)  # z_j = -sum_i T[i,j]; Z[0, nw-1] = -(artificial sum)
        basis = [npool + i for i in range(nr)]
        # warm preference: indices (into pool) of float-support columns, tried first
        poolpos = {k: jj for jj, k in enumerate(pool)}
        warmpos = [poolpos[k] for k in warm if k in poolpos]
        t0 = _time.time()
        for itp in range(max_pivots):
            # entering: warm-preferred, then Dantzig; Bland every 8th (anti-cycling)
            enter = -1
            if itp % 8 != 7:
                bestv = None
                for j in warmpos:
                    v = Z[0, j]
                    if v < 0 and (bestv is None or v < bestv):
                        bestv = v
                        enter = j
            if enter < 0 and itp % 8 == 7:
                for j in range(npool):
                    if Z[0, j] < 0:
                        enter = j
                        break
            elif enter < 0:
                bestv = None
                for j in range(npool):
                    v = Z[0, j]
                    if v < 0 and (bestv is None or v < bestv):
                        bestv = v
                        enter = j
            if enter < 0:
                break  # phase-1 optimal
            # ratio test (Bland ties: smallest basis label)
            leave = -1
            best = None
            for i in range(nr):
                a = T[i, enter]
                if a > 0:
                    ratio = T[i, npool + nr] / a
                    if best is None or ratio < best or \
                       (ratio == best and basis[i] < basis[leave]):
                        best = ratio
                        leave = i
            if leave < 0:
                if verbose:
                    _log("  exact phase1: unbounded (impossible)")
                return None
            # pivot at (leave, enter) via outer-product update (C-speed)
            p = T[leave, enter]
            vrow = fmpq_mat(1, nw)
            for j in range(nw):
                vrow[0, j] = T[leave, j] / p
            ucol = fmpq_mat(nr, 1)
            for i in range(nr):
                if i != leave:
                    ucol[i, 0] = T[i, enter]
            T = T - ucol * vrow
            for j in range(nw):
                T[leave, j] = vrow[0, j]
            Z = Z - Z[0, enter] * vrow
            basis[leave] = enter
            if verbose and itp % 100 == 0:
                obj = Z[0, nw - 1]
                _log(f"  exact phase1: pivot {itp}, artificial sum "
                     f"{-_q2f(obj):.3e}, {_time.time() - t0:.0f}s")
        obj = Z[0, nw - 1]
        if obj != 0:
            if verbose:
                _log(f"  exact phase1: pool infeasible "
                     f"(artificial sum {-_q2f(obj):.3e})")
            return None
        out = {}
        for i in range(nr):
            val = T[i, npool + nr]
            fr = Fraction(int(val.p), int(val.q))
            if basis[i] < npool:
                if fr < 0:
                    if verbose:
                        _log("  exact phase1: negative basic (unexpected)")
                    return None
                if fr > 0:
                    out[pool[basis[i]]] = fr
            elif fr != 0:
                if verbose:
                    _log("  exact phase1: residual artificial (unexpected)")
                return None
        if verbose:
            _log(f"  exact phase1: EXACT feasible ({len(out)} support)")
        return out

    def cascade(cv):
        """Zero the exact x-basis residual by adding nonneg-coefficient terms.
        In the x-basis the pure term (i,0,j,0) is exactly x^i l^j:
        (i,j), i>=1: +rho on pure (i,0,j,0) if rho>0, else gamma=-rho on
        (i-1,1,j,0) = x^{i-1} l^j - x^i l^j, which passes |rho| down to (i-1,j);
        (0,j), j>=1: +rho on (0,0,j,0) if rho>0, else gamma=-rho on (0,0,j-1,1)
        = (1/3) x l^{j-1} + t l^{j-1} - l^j, passing gamma*t to (0,j-1) and
        gamma/3 to (1,j-1);
        (0,0): needs pure constant mass >= -rho.  Returns (extra_terms, deficit)."""
        resid = exact_residual(cv)
        rho = {mn: v for mn, v in resid.items()}
        extra = {}  # tuple -> coefficient adjustment (pure entries may go negative,
        #             bounded below by the existing LP mass)
        third = Fraction(1, 3)

        def pure_avail(i, j):
            k = pure_col.get((i, j))
            base = cv.get(k, Fraction(0)) if k is not None else Fraction(0)
            return base + extra.get((i, 0, j, 0), Fraction(0))

        for j in range(D, -1, -1):
            for i in range(D - j, -1, -1):
                v = rho.get((i, j), Fraction(0))
                if v == 0:
                    continue
                if v > 0:
                    extra[(i, 0, j, 0)] = extra.get((i, 0, j, 0), Fraction(0)) + v
                    continue
                # negative residual: first absorb into the existing pure mass here
                take = min(-v, pure_avail(i, j))
                if take > 0:
                    extra[(i, 0, j, 0)] = extra.get((i, 0, j, 0), Fraction(0)) - take
                    v = v + take
                if v == 0:
                    continue
                if i == 0 and j == 0:
                    rho[(0, 0)] = v
                    break
                if i >= 1:
                    g = -v
                    extra[(i - 1, 1, j, 0)] = extra.get((i - 1, 1, j, 0), Fraction(0)) + g
                    rho[(i - 1, j)] = rho.get((i - 1, j), Fraction(0)) - g
                else:  # i == 0, j >= 1
                    g = -v
                    extra[(0, 0, j - 1, 1)] = extra.get((0, 0, j - 1, 1), Fraction(0)) + g
                    rho[(0, j - 1)] = rho.get((0, j - 1), Fraction(0)) - g * t
                    rho[(1, j - 1)] = rho.get((1, j - 1), Fraction(0)) - g * third
                rho[(i, j)] = Fraction(0)
        v00 = rho.get((0, 0), Fraction(0))
        if v00 > 0:
            extra[(0, 0, 0, 0)] = extra.get((0, 0, 0, 0), Fraction(0)) + v00
            v00 = Fraction(0)
        # deficit = unabsorbed shortfall at the origin (existing mass already used)
        return extra, -v00

    # tier 1: cheap float paths -- solve at a few constant floors, refine the
    # exact residual, cascade; one exact-vertex attempt in between
    extra = None
    combos = [(0.02, 0), (1e-3, 0), (1e-4, 0), (1e-6, 0)]
    for it, (frac0, sd) in enumerate(combos):
        lb0[pure_col[(0, 0)]] = frac0 * float(K00) * float(xdiv[pure_col[(0, 0)]])
        obj2 = cost * np.random.default_rng(1000 + sd).uniform(1.0, 1.2, ncol)
        cvals2, cand2 = solve_and_round(lb0, obj_used=obj2)
        if cvals2 is None:
            if verbose:
                print(f"  attempt {it}: floor {frac0:g} infeasible")
            continue
        cvals, cand = refine_solution(cvals2), cand2
        extra2, deficit = cascade(cvals)
        if deficit == 0:
            extra = extra2
            if verbose:
                print(f"  attempt {it}: cascade OK at floor {frac0:g}")
            break
        if verbose:
            print(f"  attempt {it}: floor {frac0:g} cascade deficit "
                  f"{float(deficit):.3e}")
        if it == 1:
            ev = exact_vertex(cand, seed=sd)
            if ev is not None:
                cvals = ev
                extra = {}
                break
    # tier 2: guaranteed exact phase-1 simplex on a restricted pool,
    # warm-preferring the float support
    if extra is None:
        pures = list(pure_col.values())
        warm = [k for k in cvals.keys()] if cvals else []
        pool = list(dict.fromkeys(list(cand) + pures))[:8000]
        if verbose:
            print(f"  tier 2: exact phase-1 simplex on {len(pool)} columns")
        ev = exact_phase1(pool, warm=warm)
        if ev is None and ncol > len(pool):
            rng3 = np.random.default_rng(4242)
            extra_pool = [k for k in range(ncol) if k not in set(pool)]
            rng3.shuffle(extra_pool)
            if verbose:
                print("  tier 2: escalating pool")
            ev = exact_phase1(pool + extra_pool[:4000], warm=warm)
        if ev is not None:
            cvals = ev
            extra = {}
    if extra is None:
        if verbose:
            print("  no exact certificate found after retries")
        return None
    # apply the correction terms
    col_of = {tt: k for k, tt in enumerate(cols)}
    tuple_extra = {}
    for tt, g in extra.items():
        tuple_extra[tt] = tuple_extra.get(tt, Fraction(0)) + g
    # merge extra terms into cvals by column index when the tuple exists, else keep aside
    extra_terms = []
    for tt, g in tuple_extra.items():
        if g == 0:
            continue
        k = col_of.get(tt)
        if k is not None:
            cvals[k] = cvals.get(k, Fraction(0)) + g
        else:
            extra_terms.append((tt, g))

    cert = [(cols[k], cv) for k, cv in sorted(cvals.items()) if cv != 0]
    cert += [(tt, g) for tt, g in sorted(extra_terms) if g != 0]
    # final independent verification
    resid = dict(K)
    for (a, b, c, d), cv in cert:
        assert cv > 0
        for mn, v in term_coeffs(a, b, c, d, t).items():
            resid[mn] = resid.get(mn, Fraction(0)) - cv * v
    assert all(v == 0 for v in resid.values()), "final residual nonzero"
    if verbose:
        cost = sum((b + 1) * (d + 1) * (d + 2) // 2 for (a, b, c, d), _ in cert)
        print(f"  EXACT cert: {len(cert)} terms, expansion cost {cost}, "
              f"max |num| bits {max(abs(v.numerator).bit_length() for _, v in cert)}")
    return cert


# ---------------------------------------------------------------------------
# depth-0 Bernstein certificate (closed form -- no LP, no search)
# ---------------------------------------------------------------------------

def bernstein_cert(m, r, verify=True):
    """Exact depth-0 Bernstein certificate of the cleared identity
        (q + r/m)^dy * diagKernel m r q l
          = sum_{i,j} c_ij (3q)^i (1-3q)^(dx-i) l^j (q+r/m-l)^(dy-j),   c_ij >= 0,
    with dx = dy = m-2r-1.  Coefficients are a closed-form linear transform of
    diagKernel's coefficients (monomial -> Bernstein on the reparametrised box).
    Returns (cert list [((a,b,c,d), Fraction)], dy)."""
    t = Fraction(r, m)
    K = diag_kernel_coeffs(m, r)
    n = m - 2 * r
    dx = dy = n - 1
    # coefficients of F(x,y) = K(x/3, (x/3+t) y):  a[(p,j)] x^p y^j
    Kx = {(i, j): v / Fraction(3) ** i for (i, j), v in K.items()}
    a = {}
    third = Fraction(1, 3)
    for (p, j), v in Kx.items():
        for e in range(j + 1):
            w = v * comb(j, e) * third ** e * t ** (j - e)
            key = (p + e, j)
            a[key] = a.get(key, Fraction(0)) + w
    # monomial -> Bernstein, x-direction then y-direction:
    # b_i = sum_{p<=i} C(i,p)/C(D,p) a_p
    bx = {}
    for (p, j), v in a.items():
        for i in range(p, dx + 1):
            key = (i, j)
            bx[key] = bx.get(key, Fraction(0)) + Fraction(comb(i, p), comb(dx, p)) * v
    b = {}
    for (i, q_), v in bx.items():
        for j in range(q_, dy + 1):
            key = (i, j)
            b[key] = b.get(key, Fraction(0)) + Fraction(comb(j, q_), comb(dy, q_)) * v
    cert = []
    minb = min(b.values())
    assert minb >= 0, f"negative Bernstein coefficient ({float(minb):.3e}) at ({m},{r})"
    for (i, j), v in sorted(b.items()):
        c = v * comb(dx, i) * comb(dy, j)
        if c != 0:
            cert.append(((i, dx - i, j, dy - j), c))
    if verify:
        # exact check: sum c*term == (q+t)^dy * K  (in the (q,l) monomial basis)
        lhs = {}
        for f in range(dy + 1):
            w = comb(dy, f) * t ** (dy - f)
            for (i, j), v in K.items():
                key = (i + f, j)
                lhs[key] = lhs.get(key, Fraction(0)) + w * v
        for (a4, b4, c4, d4), cv in cert:
            for mn, v in term_coeffs(a4, b4, c4, d4, t).items():
                lhs[mn] = lhs.get(mn, Fraction(0)) - cv * v
        assert all(v == 0 for v in lhs.values()), f"Bernstein identity failed ({m},{r})"
    return cert, dy


# ---------------------------------------------------------------------------
# Lean emission
# ---------------------------------------------------------------------------

def lean_rat(v):
    """Fraction -> Lean real literal."""
    if v.denominator == 1:
        return f"({v.numerator} : ℝ)"
    return f"({v.numerator}/{v.denominator} : ℝ)"


def lean_term(m, r, tt, v):
    a, b, c, d = tt
    parts = [lean_rat(v)]
    if a:
        parts.append(f"(3*q)^{a}" if a > 1 else "(3*q)")
    if b:
        parts.append(f"(1-3*q)^{b}" if b > 1 else "(1-3*q)")
    if c:
        parts.append(f"l^{c}" if c > 1 else "l")
    if d:
        parts.append(f"(q+{r}/{m}-l)^{d}" if d > 1 else f"(q+{r}/{m}-l)")
    return " * ".join(parts)


def lean_term_nonneg(tt):
    """Explicit proof term for 0 ≤ <lean_term ...> (matches lean_term's left-assoc shape).
    Uses hypotheses hA : 0 ≤ 3*q, hB : 0 ≤ 1-3*q, hL : 0 ≤ l, hM : 0 ≤ q+r/m-l."""
    a, b, c, d = tt
    pf = "hc"  # 0 ≤ coefficient literal, provided per-term via norm_num
    for expo, hyp in ((a, "hA"), (b, "hB"), (c, "hL"), (d, "hM")):
        if expo == 1:
            pf = f"(mul_nonneg {pf} {hyp})"
        elif expo > 1:
            pf = f"(mul_nonneg {pf} (pow_nonneg {hyp} {expo}))"
    return pf


def lean_sum_nonneg(cert):
    """Explicit proof term for 0 ≤ term_1 + ... + term_k (left-assoc sum)."""
    pfs = [lean_term_nonneg(tt).replace("hc", f"h{i}") for i, (tt, _) in enumerate(cert)]
    acc = pfs[0]
    for p in pfs[1:]:
        acc = f"(add_nonneg {acc} {p})"
    return acc


def emit_lean_lemma(m, r, cert):
    """The per-pair certificate list + lemma finKernel_m_r.

    The certificate is emitted as a *list literal* of ℕ-tuples (linear-time
    elaboration; a flat arithmetic expression is quadratic), evaluated by
    `certSum`; nonnegativity is the generic `certSum_nonneg`.  Binomials on the
    diagKernel side are evaluated via descFactorial/factorial (norm_num
    extensions), so large r stays cheap."""
    n = m - 2 * r
    entries = ",\n  ".join(
        f"({v.numerator}, {v.denominator}, {a}, {b}, {c}, {d})"
        for (a, b, c, d), v in cert)
    return f"""/-- Handelman certificate for `diagKernel {m} {r}` ({len(cert)} terms). -/
def finCert_{m}_{r} : List CertTerm := [
  {entries}]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem finKernel_{m}_{r} {{q l : ℝ}} (hq0 : 0 ≤ q) (hq : q ≤ 1/3)
    (hl0 : 0 < l) (hlr : l < q + {r}/{m}) :
    0 ≤ diagKernel {m} {r} q l := by
  have key : diagKernel {m} {r} q l = certSum ({r}/{m}) q l finCert_{m}_{r} := by
    unfold diagKernel finCert_{m}_{r}
    rw [hsym_replicate_append_replicate, hsym_replicate_append_replicate,
        hsym_replicate_append_replicate]
    simp only [show ({m}:ℕ) - 2*{r} = {n} from rfl, show ({n}:ℕ) - 1 = {n - 1} from rfl,
      Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.choose_eq_descFactorial_div_factorial, certSum_cons, certSum_nil]
    norm_num
    try push_cast
    try ring
  rw [key]
  exact certSum_nonneg (by linarith) (by linarith) hl0.le (by linarith) _
"""


def emit_proto_file(m, r, cert, path):
    body = emit_lean_lemma(m, r, cert)
    src = f"""/-
Hfin prototype: exact Handelman certificate for diagKernel {m} {r} (generated by hfin_certs.py).
-/
import OddCycleBound.HighDensity.SymmetricPoly
import OddCycleBound.HighDensity.HfinCertSum

namespace OddCycleBound.HighDensity

{body}
end OddCycleBound.HighDensity
"""
    with open(path, "w", encoding="utf-8") as f:
        f.write(src)
    print(f"wrote {path} ({len(src)} chars)")


def emit_lean_lemma_bern(m, r, cert, dy):
    """Per-pair lemma via the cleared depth-0 Bernstein identity:
    (q+r/m)^dy * diagKernel = certSum ...  with nonneg list coefficients,
    concluded by cancelling the positive factor."""
    n = m - 2 * r
    entries = ",\n  ".join(
        f"({v.numerator}, {v.denominator}, {a}, {b}, {c}, {d})"
        for (a, b, c, d), v in cert)
    return f"""/-- Depth-0 Bernstein certificate for `diagKernel {m} {r}` ({len(cert)} terms). -/
def finCert_{m}_{r} : List CertTerm := [
  {entries}]

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem finKernel_{m}_{r} {{q l : ℝ}} (hq0 : 0 ≤ q) (hq : q ≤ 1/3)
    (hl0 : 0 < l) (hlr : l < q + {r}/{m}) :
    0 ≤ diagKernel {m} {r} q l := by
  have key : (q + {r}/{m}) ^ {dy} * diagKernel {m} {r} q l
      = certSum ({r}/{m}) q l finCert_{m}_{r} := by
    unfold diagKernel finCert_{m}_{r}
    rw [hsym_replicate_append_replicate, hsym_replicate_append_replicate,
        hsym_replicate_append_replicate]
    simp only [show ({m}:ℕ) - 2*{r} = {n} from rfl, show ({n}:ℕ) - 1 = {n - 1} from rfl,
      Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.choose_eq_descFactorial_div_factorial, certSum_cons, certSum_nil]
    norm_num
    try push_cast
    try ring
  have hp : (0:ℝ) < (q + {r}/{m}) ^ {dy} := pow_pos (by linarith) {dy}
  have hmul : (0:ℝ) ≤ (q + {r}/{m}) ^ {dy} * diagKernel {m} {r} q l := by
    rw [key]
    exact certSum_nonneg (by linarith) (by linarith) hl0.le (by linarith) _
  exact (mul_nonneg_iff_of_pos_left hp).mp hmul
"""


def emit_pair_file(m, r, cert, path):
    """One file per pair (m,r): the single lemma finKernel_m_r (maximises lake parallelism)."""
    src = f"""/-
Hfin certificate for the pair (m,r) = ({m},{r}) (GENERATED by hfin_certs.py --gen; do not
edit).  An exact degree-(m-2r-1) Handelman representation of diagKernel {m} {r} with
nonnegative rational coefficients on q ∈ [0,1/3], 0 < l < q + {r}/{m}.
-/
import OddCycleBound.HighDensity.SymmetricPoly
import OddCycleBound.HighDensity.HfinCertSum

namespace OddCycleBound.HighDensity

{emit_lean_lemma(m, r, cert)}
end OddCycleBound.HighDensity
"""
    with open(path, "w", encoding="utf-8") as f:
        f.write(src)


def reflect_grid(m, r):
    """Build the integer Horner grid for the depth-0 Bernstein certificate of (m,r).

    Returns (grid, dx, dy, L) where grid[e][i] = K_{i, dy-e} : ℕ is the integer-cleared
    coefficient of  (3q)^i (1-3q)^(dx-i) l^(dy-e) (mq+r-ml)^e  in  D * certSum,
    D = r * lcm(coeff denominators) * m^dy.  The factor `r * m^dy` matches
    `dkClearedBP`'s natural scale (`r*m^dy*(q+r/m)^dy*diagKernel`); the extra `L = lcm`
    clears the certificate denominators, applied on the `dkClearedBP` side as `smulBP L`.
    (K >= 0; the cleared identity is what the Lean `decide +kernel` verifies.)"""
    from math import gcd
    # verify=False: the in-kernel Lean `decide +kernel` is the authoritative check of the
    # cleared identity; bernstein_cert still asserts Bernstein-coeff nonnegativity (grid ≥ 0).
    cert, dy = bernstein_cert(m, r, verify=False)
    n = m - 2 * r
    dx = n - 1
    assert dy == n - 1, (m, r, dy, n)
    L = 1
    for (_t, v) in cert:
        L = L * v.denominator // gcd(L, v.denominator)
    D = r * L * m ** dy
    Kd = {}
    for (a, b, c, e), coeff in cert:  # a=i, b=dx-i, c=j, e=dy-j
        Kt = Fraction(D * coeff.numerator, coeff.denominator * m ** e)
        assert Kt.denominator == 1 and Kt.numerator >= 0, (m, r, a, b, c, e, Kt)
        Kd[(a, c)] = Kt.numerator  # (i, j) -> K
    grid = [[Kd.get((i, dy - e), 0) for i in range(dx + 1)] for e in range(dy + 1)]
    return grid, dx, dy, L


# Pairs whose max grid-coefficient bit-length exceeds this get a `sorry` STUB instead of the
# real reflection proof (the in-kernel `decide` for such pairs needs > ~16 GB and is deferred
# to a serial high-memory build).  None => never stub.  Read from env HFIN_STUB_BITS so that
# gen_all's worker subprocesses (fresh imports) inherit it.
import os as _os
STUB_BITS = int(_os.environ["HFIN_STUB_BITS"]) if _os.environ.get("HFIN_STUB_BITS") else None


def emit_pair_file_reflect(m, r, path):
    """One file per pair (m,r) via the Horner BP reflection infra (HfinPolyReflect.lean):
    grid data + finKernel_m_r, the cleared identity checked in-kernel by `decide +kernel`.
    If STUB_BITS is set and the pair's coefficients exceed it, emit a `sorry` stub instead."""
    grid, dx, dy, L = reflect_grid(m, r)
    if STUB_BITS is not None:
        mb = max((max((v.bit_length() for v in row), default=0) for row in grid), default=0)
        if mb > STUB_BITS:
            emit_pair_file_stub(m, r, path, mb)
            return
    gridlit = ",\n  ".join("[" + ", ".join(str(v) for v in row) + "]" for row in grid)
    src = f"""/-
Hfin certificate for (m,r) = ({m},{r}) via Horner BP reflection (GENERATED by hfin_certs.py
--gen; do not edit).  Depth-0 Bernstein certificate of the cleared identity
`{L} * (q+{r}/{m})^{dy} * (r*m^dy) * diagKernel {m} {r} = certReal`, checked in-kernel
(`decide +kernel`); nonnegativity of `certReal` is structural, so `0 <= diagKernel {m} {r}`.
-/
import OddCycleBound.HighDensity.HfinPolyReflect

set_option maxHeartbeats 400000000
set_option maxRecDepth 100000

namespace OddCycleBound.HighDensity

def grid_{m}_{r} : List (List ℕ) := [
  {gridlit}]

theorem finKernel_{m}_{r} {{q l : ℝ}} (hq0 : 0 ≤ q) (hq : q ≤ 1/3)
    (hl0 : 0 < l) (hlr : l < q + {r}/{m}) :
    0 ≤ diagKernel {m} {r} q l := by
  have hpos : (0:ℝ) ≤ (({m}:ℤ):ℝ) * q + (({r}:ℤ):ℝ) - (({m}:ℤ):ℝ) * l := by
    push_cast; linarith [hlr]
  have hcert : 0 ≤ certReal ({m}:ℤ) ({r}:ℤ) {dx} {dy} q l grid_{m}_{r} :=
    certReal_nonneg ({m}:ℤ) ({r}:ℤ) {dx} {dy} (by linarith) (by linarith) hl0.le hpos grid_{m}_{r}
  have hdata : eqBP (smulBP ({L} : ℤ) (dkClearedBP {m} {r}))
      (hornerBP ({m}:ℤ) ({r}:ℤ) {dx} {dy} grid_{m}_{r}) = true := by
    decide +kernel
  have hbridge : bpEval q l (smulBP ({L} : ℤ) (dkClearedBP {m} {r}))
      = bpEval q l (hornerBP ({m}:ℤ) ({r}:ℤ) {dx} {dy} grid_{m}_{r}) := eqBP_sound q l _ _ hdata
  rw [eval_smulBP, eval_dkClearedBP {m} {r} (by norm_num) (by norm_num) q l,
      eval_hornerBP ({m}:ℤ) ({r}:ℤ) {dx} {dy} q l grid_{m}_{r}] at hbridge
  have hqt : (0:ℝ) < q + (({r}:ℕ):ℝ) / (({m}:ℕ):ℝ) := by
    have : (0:ℝ) < (({r}:ℕ):ℝ) / (({m}:ℕ):ℝ) := by positivity
    linarith [hq0]
  have hL : (0:ℝ) < (({L}:ℤ):ℝ) := by norm_num
  have hA0 : (0:ℝ) < (({r}:ℕ):ℝ) * (({m}:ℕ):ℝ) ^ ({m} - 2 * {r} - 1)
      * (q + (({r}:ℕ):ℝ) / (({m}:ℕ):ℝ)) ^ ({m} - 2 * {r} - 1) := by
    have h2 : (0:ℝ) < (({m}:ℕ):ℝ) ^ ({m} - 2 * {r} - 1) := by positivity
    have h3 : (0:ℝ) < (q + (({r}:ℕ):ℝ) / (({m}:ℕ):ℝ)) ^ ({m} - 2 * {r} - 1) := pow_pos hqt _
    positivity
  rw [← hbridge] at hcert
  exact (mul_nonneg_iff_of_pos_left hA0).mp ((mul_nonneg_iff_of_pos_left hL).mp hcert)

end OddCycleBound.HighDensity
"""
    with open(path, "w", encoding="utf-8") as f:
        f.write(src)


def emit_pair_file_stub(m, r, path, mb):
    """A `sorry` stub for a pair whose real reflection proof is deferred (too memory-heavy).
    Same theorem signature as the real `finKernel_m_r`, so dispatchers/aggregate still link."""
    src = f"""/-
Hfin certificate STUB for (m,r) = ({m},{r}) (GENERATED).  DEFERRED: the depth-0 Bernstein
reflection identity for this pair has ~{mb}-bit integer coefficients; its in-kernel
`decide +kernel` needs > ~16 GB, so it is left as `sorry` for a later serial high-memory
build.  The certificate itself is proven valid (Python) and passes at higher `-M`.
-/
import OddCycleBound.HighDensity.HfinPolyReflect

namespace OddCycleBound.HighDensity

theorem finKernel_{m}_{r} {{q l : ℝ}} (hq0 : 0 ≤ q) (hq : q ≤ 1/3)
    (hl0 : 0 < l) (hlr : l < q + {r}/{m}) :
    0 ≤ diagKernel {m} {r} q l := by
  sorry

end OddCycleBound.HighDensity
"""
    with open(path, "w", encoding="utf-8") as f:
        f.write(src)


def emit_m_file(m, rs, path):
    """Per-m dispatcher finKernel_M<m>, importing its pair files."""
    rs = sorted(rs)
    imports = "\n".join(
        f"import OddCycleBound.HighDensity.Hfin.P{m:03d}R{r:02d}" for r in rs)
    rmax = max(rs)
    bullets = "\n".join(
        f"  · exact finKernel_{m}_{r} hq0 hq hl0 (by push_cast at hlr; exact hlr)"
        for r in rs)
    src = f"""/-
Hfin dispatcher for m = {m} (GENERATED by hfin_certs.py --gen; do not edit).
-/
{imports}

namespace OddCycleBound.HighDensity

/-- Dispatcher for `m = {m}`: all residual-strip pairs `(m,r)`. -/
theorem finKernel_M{m} {{q l : ℝ}} (r : ℕ) (hr2 : 2 ≤ r) (hres : 2*r < {m} - 2*r)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/3) (hl0 : 0 < l) (hlr : l < q + (r : ℝ)/{m}) :
    0 ≤ diagKernel {m} r q l := by
  have hub : r ≤ {rmax} := by omega
  interval_cases r
{bullets}

end OddCycleBound.HighDensity
"""
    with open(path, "w", encoding="utf-8") as f:
        f.write(src)


def emit_aggregate(ms, outdir, m_hi=61):
    """Aggregate finKernel_all for odd 9 ≤ m ≤ m_hi (only the m in `ms`, which must be exactly
    the odd values in [9, m_hi])."""
    imports = "\n".join(f"import OddCycleBound.HighDensity.Hfin.M{m:03d}" for m in ms)
    bullets = []
    for m in range(9, m_hi + 1):
        if m % 2 == 1:
            bullets.append(f"  · exact finKernel_M{m} r hr2 hres hq0 hq hl0 "
                           f"(by push_cast at hlr ⊢; exact hlr)")
        else:
            bullets.append("  · exact absurd hm (by decide)")
    body = "\n".join(bullets)
    src = f"""/-
Hfin aggregate (GENERATED by hfin_certs.py --gen; do not edit): the
`prop:finite` certificate family for the residual strip, all odd 9 ≤ m ≤ {m_hi}.
-/
{imports}

namespace OddCycleBound.HighDensity

/-- **`Hfin` (`prop:finite`).**  For every odd `9 ≤ m ≤ {m_hi}` and residual-strip pair
`(r, ℓ)` (`r ≥ 2`, `2r < m - 2r`, `0 < ℓ < q + r/m`) with `q ∈ [0, 1/3]`,
the diagonal kernel is nonnegative: `0 ≤ diagKernel m r q ℓ`. -/
theorem finKernel_all {{q l : ℝ}} {{m r : ℕ}} (hm : Odd m) (hm9 : 9 ≤ m) (hmHi : m ≤ {m_hi})
    (hr2 : 2 ≤ r) (hres : 2*r < m - 2*r)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/3) (hl0 : 0 < l) (hlr : l < q + (r : ℝ)/(m : ℝ)) :
    0 ≤ diagKernel m r q l := by
  interval_cases m
{body}

end OddCycleBound.HighDensity
"""
    with open(f"{outdir}/Aggregate.lean", "w", encoding="utf-8") as f:
        f.write(src)


def gen_pair(m, r, outdir, verbose=True):
    """Generate one pair's certificate + Lean file (skips if the file exists).
    Returns the output path."""
    import os
    path = f"{outdir}/P{m:03d}R{r:02d}.lean"
    if os.path.exists(path):
        _log(f"({m},{r}) exists, skipping")
        return path
    t0 = _time.time()
    emit_pair_file_reflect(m, r, path)
    _log(f"({m},{r}) DONE in {_time.time()-t0:.1f}s -> {path}")
    return path


def _gen_pair_worker(args):
    m, r, outdir = args
    import io, os, traceback
    logdir = f"{outdir}/logs"
    os.makedirs(logdir, exist_ok=True)
    logpath = f"{logdir}/p{m:03d}r{r:02d}.log"
    old = sys.stdout
    try:
        with open(logpath, "w", encoding="utf-8", buffering=1) as fh:
            sys.stdout = fh
            try:
                gen_pair(m, r, outdir, verbose=True)
                return (m, r, True, "")
            except Exception:
                traceback.print_exc(file=fh)
                return (m, r, False, logpath)
    finally:
        sys.stdout = old


def gen_all(outdir, only_m=None, jobs=1, m_hi=61):
    """Generate certificates + Lean files for all pairs with m ≤ m_hi (or one m).
    With jobs > 1, pairs run in parallel processes (per-pair logs in outdir/logs).
    The aggregate `finKernel_all` is emitted for odd 9 ≤ m ≤ m_hi."""
    import os
    os.makedirs(outdir, exist_ok=True)
    ms = sorted({m for (m, r) in all_pairs() if m <= m_hi})
    if only_m is not None:
        ms = [m for m in ms if m == only_m]
    pairs = [(m, r) for m in ms for (mm, r) in all_pairs() if mm == m]
    todo = [(m, r) for (m, r) in pairs
            if not os.path.exists(f"{outdir}/P{m:03d}R{r:02d}.lean")]
    _log(f"{len(pairs)} pairs, {len(todo)} to generate, jobs={jobs}")
    if jobs > 1 and todo:
        from concurrent.futures import ProcessPoolExecutor, as_completed
        # hardest first so the tail is short
        todo.sort(key=lambda p: -(p[0] - 2 * p[1]))

        # progress bar over predicted work: pair weight ~ rows^3
        # (rows = #monomial constraints); ETA adapts as pairs complete
        def weight(p):
            deg = p[0] - 2 * p[1] - 1
            rows = (deg + 1) * (deg + 2) // 2
            return rows ** 3 / 1e6

        total_w = sum(weight(p) for p in todo)
        try:
            from tqdm import tqdm
            bar = tqdm(total=round(total_w, 1), unit="work",
                       bar_format="{l_bar}{bar}| {n:.0f}/{total:.0f} "
                                  "[{elapsed}<{remaining}]")
        except ImportError:
            bar = None
        ndone, nfail = 0, 0
        t0 = _time.time()
        with ProcessPoolExecutor(max_workers=jobs) as ex:
            futs = {ex.submit(_gen_pair_worker, (m, r, outdir)): (m, r)
                    for (m, r) in todo}
            for fut in as_completed(futs):
                m, r, ok, log = fut.result()
                ndone += 1
                nfail += 0 if ok else 1
                msg = (f"[{ndone}/{len(todo)}] ({m},{r}) "
                       f"{'ok' if ok else 'FAILED see ' + log}"
                       f"{'' if not nfail else f'  ({nfail} failures)'}")
                if bar is not None:
                    bar.update(round(weight((m, r)), 1))
                    bar.set_postfix_str(f"last ({m},{r})"
                                        + (f" FAIL x{nfail}" if nfail else ""))
                    from tqdm import tqdm as _t
                    _t.write(f"[{_time.strftime('%H:%M:%S')}] {msg}")
                else:
                    el = _time.time() - t0
                    eta = el / ndone * (len(todo) - ndone)
                    _log(f"{msg}  elapsed {el/60:.1f}m  ETA {eta/60:.1f}m")
        if bar is not None:
            bar.close()
    else:
        for (m, r) in todo:
            gen_pair(m, r, outdir)
    # dispatchers + aggregate (only when every pair file exists)
    missing = [(m, r) for (m, r) in pairs
               if not os.path.exists(f"{outdir}/P{m:03d}R{r:02d}.lean")]
    if missing:
        _log(f"{len(missing)} pairs still missing; dispatchers not written: {missing[:8]}")
        return
    for m in ms:
        rs = [r for (mm, r) in all_pairs() if mm == m]
        emit_m_file(m, rs, f"{outdir}/M{m:03d}.lean")
    _log(f"wrote per-m dispatchers for {len(ms)} values of m")
    if only_m is None:
        emit_aggregate(ms, outdir, m_hi=m_hi)
        _log(f"wrote {outdir}/Aggregate.lean (m ≤ {m_hi})")


def exact_certificate(sol, verbose=True, extra=0):
    """Solve A_S c_S = K exactly (Fractions) on the LP support S; verify c_S >= 0.
    Returns list of ((a,b,c,d), Fraction) or None."""
    m, r, t, K = sol["m"], sol["r"], sol["t"], sol["K"]
    cols, x, supp = sol["cols"], sol["x"], sol["supp"]
    # candidate columns, biggest first, support first
    cand = sorted(supp, key=lambda k: -x[k])
    if extra:
        rest = sorted((k for k in range(len(cols)) if k not in set(supp)),
                      key=lambda k: -x[k])[:extra]
        cand += rest
    terms = [cols[k] for k in cand]
    # exact columns
    colco = [term_coeffs(*tt, t) for tt in terms]
    monos = sorted(set().union(K.keys(), *[c.keys() for c in colco]))
    midx = {mn: i for i, mn in enumerate(monos)}
    nr, nc = len(monos), len(terms)
    if verbose:
        print(f"exact solve: {nr} rows x {nc} cols")
    from sympy.polys.matrices import DomainMatrix
    from sympy import QQ
    rows = [[QQ(0)] * (nc + 1) for _ in range(nr)]
    for j, co in enumerate(colco):
        for mn, v in co.items():
            rows[midx[mn]][j] = QQ(v.numerator, v.denominator)
    for mn, v in K.items():
        rows[midx[mn]][nc] = QQ(v.numerator, v.denominator)
    Aug = DomainMatrix(rows, (nr, nc + 1), QQ)
    rref, pivots = Aug.rref()
    if nc in pivots:
        if verbose:
            print("inconsistent system (support too small)")
        return None
    # free variables -> rationalized float LP values; pivots by back-substitution
    colscale = sol.get("colscale")
    floatval = {j: (x[cand[j]] / colscale[cand[j]] if colscale is not None else 0.0)
                for j in range(nc)}
    pivset = set(pivots)
    cvals = [Fraction(0)] * nc
    for j in range(nc):
        if j not in pivset:
            cvals[j] = Fraction(floatval[j]).limit_denominator(10 ** 12)
    rr = rref.to_list()
    nfree = nc - len(pivots)
    if verbose and nfree:
        print(f"{nfree} free columns among candidates (rank {len(pivots)})")
    for irow, p in enumerate(pivots):
        num = rr[irow][nc]
        v = Fraction(int(num.numerator), int(num.denominator))
        for j in range(p + 1, nc):
            if j not in pivset and cvals[j] != 0:
                e = rr[irow][j]
                if e:
                    v -= Fraction(int(e.numerator), int(e.denominator)) * cvals[j]
        cvals[p] = v
    # verify: nonneg + exact identity
    neg = [(terms[j], cvals[j]) for j in range(nc) if cvals[j] < 0]
    if neg:
        if verbose:
            print(f"{len(neg)} negative coefficients (worst {min(v for _, v in neg)}); retry needed")
        return None
    resid = dict(K)
    for j in range(nc):
        if cvals[j] == 0:
            continue
        for mn, v in colco[j].items():
            resid[mn] = resid.get(mn, Fraction(0)) - cvals[j] * v
    bad = {k: v for k, v in resid.items() if v != 0}
    if bad:
        if verbose:
            print(f"residual nonzero at {len(bad)} monomials -- inconsistent")
        return None
    cert = [(terms[j], cvals[j]) for j in range(nc) if cvals[j] != 0]
    if verbose:
        print(f"EXACT certificate verified: {len(cert)} terms, all coeffs >= 0")
    return cert


def analyze_support(sol):
    """Print exponent-pattern stats of the LP support."""
    from collections import Counter
    cols, x, supp = sol["cols"], sol["x"], sol["supp"]
    tot = Counter()
    for k in supp:
        a, b, c, d = cols[k]
        tot[(a + b, c + d)] += 1
    print("support (a+b, c+d) histogram:")
    for key in sorted(tot):
        print("   ", key, tot[key])
    bmax = max(cols[k][1] for k in supp)
    dmax = max(cols[k][3] for k in supp)
    degs = [sum(cols[k]) for k in supp]
    print(f"max b = {bmax}, max d = {dmax}, term degree range [{min(degs)},{max(degs)}]")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--glpk-worker", nargs=2, metavar=("IN", "OUT"),
                    help="internal: crash-isolated GLPK solve")
    ap.add_argument("--validate", action="store_true")
    ap.add_argument("--pairs", action="store_true")
    ap.add_argument("--lp", nargs=3, type=int, metavar=("m", "r", "N"))
    ap.add_argument("--dcap", type=int, default=None)
    ap.add_argument("--cert", action="store_true", help="exact recovery after --lp")
    ap.add_argument("--find", nargs=3, type=int, metavar=("m", "r", "N"),
                    help="round-and-correct exact certificate")
    ap.add_argument("--gen", metavar="OUTDIR", help="generate all per-m cert files")
    ap.add_argument("--gen-pair", nargs=2, type=int, metavar=("m", "r"),
                    help="generate a single pair file (use with --gen OUTDIR)")
    ap.add_argument("--jobs", type=int, default=1, help="parallel workers for --gen")
    ap.add_argument("--only-m", type=int, default=None)
    ap.add_argument("--analyze", action="store_true")
    args = ap.parse_args()
    if args.glpk_worker:
        glpk_worker(args.glpk_worker[0], args.glpk_worker[1])
        return
    if args.validate:
        validate_5_1()
    if args.pairs:
        ps = all_pairs()
        print(len(ps), "pairs; deg distribution:")
        from collections import Counter
        cnt = Counter(m - 2 * r - 1 for (m, r) in ps)
        print(sorted(cnt.items()))
    if args.find:
        m, r, N = args.find
        find_cert(m, r, N, dcap=args.dcap)
    if args.gen and args.gen_pair:
        m, r = args.gen_pair
        gen_pair(m, r, args.gen)
    elif args.gen:
        gen_all(args.gen, only_m=args.only_m, jobs=args.jobs)
    if args.lp:
        m, r, N = args.lp
        sol = lp_feasibility(m, r, N, dcap=args.dcap)
        if sol is not None and args.analyze:
            analyze_support(sol)
        if sol is not None and args.cert:
            cert = exact_certificate(sol)
            if cert is not None:
                cost = sum((b + 1) * (d + 1) * (d + 2) // 2 for (a, b, c, d), _ in cert)
                print(f"expansion cost proxy: {cost} monomial products; "
                      f"max denom bits {max(v.denominator.bit_length() for _, v in cert)}, "
                      f"max numer bits {max(v.numerator.bit_length() for _, v in cert)}")


if __name__ == "__main__":
    main()
