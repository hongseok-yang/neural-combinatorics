# Verification scripts for `smoothed_goodman_spectral_partial.tex`

These scripts certify (numerically, or by exact symbolic computation) the claims
in the companion note `../smoothed_goodman_spectral_partial.tex`, on the smoothed
Goodman inequality

```
Delta_2(W) = t(C3 u_{K2} C5, W) - (2p-1) t(C5, W) >= 0,   p = t(K2,W) >= 1/2.
```

Requirements: Python 3 with `numpy`, `sympy`, `scipy` (tested with numpy 2.4,
sympy 1.14, scipy 1.17). Run any script from inside this directory, e.g.
`python3 spectral.py`.

## Engine (shared modules)

| file | role |
|------|------|
| `spectral.py` | validated step-graphon engine: mass-weighted eigendecomposition of `T_W`, overlaps `a_i`, triple tensor `c_{ijk}`, direct and spectral `Delta_2`, Goodman kernel. `python3 spectral.py` runs a self-test. Cross-checked against a fully independent brute-force theta-graph homomorphism count and against `core.py`. |
| `core.py` | earlier independent step-graphon engine (bipodal checker lineage); `spectral.py` is validated against it. |

## Claim -> script map

| note item | script | what it certifies | runtime |
|-----------|--------|-------------------|---------|
| Prop. (spectral form), §1 | `spectral_verify.py` | the exact identities `t(C3uC5)=sum lam_i lam_j^2 lam_k^4 c_{ijk}^2`, `Delta_2 = sum_k lam_k^4 beta_k`, etc., to ~1e-15 over random step graphons | ~1 min |
| Prop. (Goodman part minus degree correction), §2 | `decomp.py` | `Delta_2 = G - 2D`, `G>=0`, discrete forms of `G`, `D`, `delta` | seconds |
| Lemma (`beta_top >= 0`), §3 | `verify_betatop.py` | the reduction, the Dirichlet sub-claim `int d_W phi_top^2 >= lambda_top >= p`, and the three-term decomposition (all terms >=0) | ~1 min |
| Verified Claim (JEN / crux A), §4 | `verify_jen.py` | the residual PSD crux `lam_1^2 Y5^2 >= (2p-1)t(C5)^2` and `<g^2,T^4 g^2> >= (2p-1)t(C2)`; min gap positive, tight only at `W=1` | ~1-2 min |
| Perron double-drop + facts (P1)-(P4), §4 | `route_final_chain.py` | the two nonnegative drops of Prop. (Perron double-drop) and the four auxiliary facts, sample-by-sample | ~1 min |
| Thm. (block-constant gradient), §5 | `grad_kernel_sym.py` | the Frechet derivative at `W_m` is block-constant with `g_diag = kappa_m > 0`, `g_off < 0` (closed forms) | seconds |
| Thm. (quantitative neighbourhood), §5 | `combined_radius.py` | the first-order lower bound, remainder bound, and the explicit radius `r_m = kappa_m/10` | ~1 min |
| Thm. (neighbourhood), sharp constant | `C2_rational.py` | exact rational `C2(m)` (e.g. `C2(3)=242/243`, `C2(4)=761/512`) and monotone `-> 4` | seconds |
| Prop. (rank-3 degenerate axis), §5 | `rank3_degaxis.py` | `Delta_2 = N(d,o)/243` with all Bernstein coefficients of `N` nonnegative | seconds |
| Appendix A (falsification search) | `search_delta2.py` | multi-block search for a counterexample to `Delta_2 >= 0`; min = 0 only at multipartite / `W=1` | minutes (large sweep) |
| Appendix A (boundary atoms) | `atom_tests.py` | `t(H,W) >= Phi_H(p)` on the top branch for odd wheels, prism, pyramid, thetas; the even-girth non-example `theta_{2,2,3}` | slow (several minutes; scipy restarts per atom) |

## Notes

- "Verified" in the note means: no counterexample over the stated sample, minima
  at machine precision. It is **not** a proof; the residual scalar crux
  (`verify_jen.py`) is the one open inequality of the PSD case.
- The heavier scripts (`search_delta2.py`, `atom_tests.py`,
  `route_final_chain.py`) are exploratory sweeps; reduce their sample counts /
  restart counts near the top of each file for a quick run.
- These scripts were developed in a scratch workspace; this is a curated subset
  covering each claim in the note. Randomized checks use fixed seeds where it
  matters, but exact reproduction of a reported minimum is not guaranteed across
  numpy/BLAS versions — the qualitative outcome (no failures, minima ~0) is.
