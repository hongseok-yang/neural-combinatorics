# Lemma Z-B (Zone B of the Region-II scalar Huber inequality): statement and proof

Author: Claude (Zone-B subagent), July 11, 2026.
Verifier: `check_ZB_final.py` (this directory); certificate: `cert_ZB_boxes.csv`.
Definitions exactly as in `BRIEF.md`.

---

## Statement

**Lemma Z-B.** Let `(q, alpha)` be admissible (`1/3 < q < 1/2`, `q < alpha <= r(q)`), let
`m >= 15` be an integer, and write `e = 1 - 2 alpha`, `d = alpha - q`, `xi = 4 alpha^2 d / e^2`,
`L = sqrt(pq - alpha^2)`, `f = alpha - L`, `rho = (A_m/B_m) sqrt(alpha) / (2 sqrt2 f)`. If

```
e in [1/60, 1/3)    and    xi >= 1,
```

then

```
R_m  <=  sqrt(2 alpha) * B_m * f * ( d - e^2 / (16 alpha^2 (1 + rho)) ).        (Z-B)
```

The right-hand side is the lambda = 1 dual certificate, so (Z-B) implies
`R_m <= C_m psi(xi, rho)` on this zone (BRIEF, choice (II); `C_m xi = sqrt(2 alpha) B_m f d`
exactly). Oddness of `m` and positivity of `R_m` are not needed; the payment is
nonnegative on the zone (Step 2), so (Z-B) is trivially true when `R_m <= 0`.

Throughout the proof we use the exact reparametrization (BRIEF): `kappa = d/e`,

```
alpha = (1-e)/2,  d = kappa e,  q = alpha - d,  p = (1+e)/2 + d = alpha + d + e,
L^2 = alpha e - d(d+e) = e[(1-e)/2 - kappa(1+kappa) e],
x = alpha/p,  y = L/p,  l = L/alpha,  tau = q/alpha,
xi = (1-e)^2 kappa / e.
```

Admissibility is `0 < kappa <= kappa_max(e) := (1-e)/(1+e)` and
`kappa < kappa_q(e) := (1-3e)/(6e)`; the zone condition `xi >= 1` is
`kappa >= kappa_xi(e) := e/(1-e)^2`. Write the **zone domain**

```
D := { (e, kappa) :  1/60 <= e < 1/3,  kappa_xi(e) <= kappa <= min(kappa_max(e), kappa_q(e)) },
```

with the convention that the `kappa_q` constraint is strict (`q > 1/3`); using the closed
interval only enlarges `D`, and we prove the inequality on the enlargement.

Elementary facts used freely (all verified in the verifier and elementary to check):
`0 < L < alpha < p`, hence `0 < x, y, l, tau < 1` and `f > 0`
(indeed `L^2 <= alpha e < alpha^2` since `e < 1/3 < alpha`; and
`L^2 = pq - alpha^2 >= q(1-q) - q(1-alpha) = q d > 0`, the middle step being
`alpha^2 <= q(1-alpha)`, i.e. `alpha^2 + q alpha - q <= 0`, i.e. admissibility
`alpha <= r(q)`); `2 alpha = 1 - e`; `p/alpha = 1/x`;
`A_m, B_m > 0`, so `rho > 0`.

---

## Step 0. The zone is empty for e >= e1 := 2033/10000

**Claim.** If `e >= e1` then `D` contains no point, i.e. `kappa_xi(e) >= kappa_q(e)`.

*Proof.* `kappa_xi(e) >= kappa_q(e)` iff `6 e^2 >= (1-3e)(1-e)^2`, i.e. `h(e) >= 0` where
`h(e) := 6 e^2 - (1-3e)(1-e)^2`. Exactly,

```
h(e1) = 376819811 / 10^12 > 0,
```

and `h'(e) = 12 e + 3(1-e)^2 + 2(1-3e)(1-e)` is a sum of three nonnegative terms for
`0 < e <= 1/3` (the last vanishes only at `e = 1/3`), so `h' > 0` there and `h > 0` on
`[e1, 1/3)`. Hence `kappa_xi > kappa_q >= min(kappa_max, kappa_q)` and no admissible
`kappa` exists. ∎

So it suffices to prove (Z-B) for `(e, kappa) in D1 := D ∩ {e <= e1}`. Note also, for
`e in [1/60, e1]`: `kappa_xi(e) >= kappa_xi(1/60) = 60/3481` (as `kappa_xi' = (1+e)/(1-e)^3 > 0`)
and `min(kappa_max, kappa_q)(e) <= kappa_max(1/60) = 59/61` (both `kappa_max`, `kappa_q`
are decreasing). Hence

```
D1  ⊆  Rect := [1/60, 2033/10000] x [60/3481, 59/61].                       (Root box)
```

## Step 1. Defect upper bound and reduction

**Defect identity** (exact; uses `q = alpha tau`, `p = alpha + d + e`):

```
R_m = alpha^{m-1} [ alpha (1 - tau^{m-1}) - (d+e) tau^{m-1} ] + L^m.
```

Apply, with `w := 1 - tau = d/alpha in (0,1)` and integer `m-1 >= 1`:
`1 - tau^{m-1} <= (m-1) w` and Bernoulli `tau^{m-1} >= 1 - (m-1) w`. Both substitutions
increase the bracket (the coefficient `-(d+e)` of `tau^{m-1}` is negative), giving

```
R_m <= alpha^{m-1} [ (m-1) d (1 + (d+e)/alpha) - (d+e) ] + L^m
     = alpha^{m-1} [ (m-1) d / x - (d+e) ] + L^m                              (1)
```

(using `1 + (d+e)/alpha = p/alpha = 1/x`). Divide (1) by `D := m d alpha p^{m-2} > 0`,
using `alpha^{m-1} = x^{m-1} p^{m-1}`, `(d+e)/d = 1 + 1/kappa`, `L^m = y^m p^m`:

```
R_m / D  <=  J(m-1) + Lam_L,   where   n := m-1,
J(n)    :=  x^{n-2} (n - A) / (n+1),      A := x (1 + 1/kappa),
Lam_L   :=  y^m p^2 / (m d alpha).                                            (2)
```

(The algebra `x^{m-2}[(m-1)/(mx) - (1+1/kappa)/m] = J(m-1)` is an identity:
`(m-1)/(mx) - (1+1/kappa)/m = [kappa(m-1) - x(1+kappa)]/(m x kappa)`.)

## Step 2. Payment lower bound

Let `P := sqrt(2 alpha) B_m f (d - eps_hat)`, `eps_hat := e^2/(16 alpha^2 (1+rho))`,
`eps := eps_hat / d`. Since `eps_hat/d = 1/(4 xi (1+rho))` (exact, from
`xi = 4 alpha^2 d/e^2`), the hypotheses `xi >= 1`, `rho > 0` give

```
eps <= 1/4,   hence   d - eps_hat = d (1 - eps) >= (3/4) d > 0.               (3)
```

Now `B_m = 2 L^{m-2} + m k_m(L) >= m k_m(L) = m p^{m-1} (1 - y^{m-1})/(p + L)`, and
`f/(p+L) = alpha(1-l)/(p(1+y)) = x(1-l)/(1+y)`, `sqrt(2 alpha) = sqrt(1-e)`,
`alpha = x p`; therefore

```
P >= D * Pi_m,   Pi_m := sqrt(1-e) (1-l)(1 - y^{m-1})(1 - eps) / (1+y).       (4)
```

## Step 3. Elimination of m (all bounds are functions of (e,kappa) only)

**(3a) rho lower bound.** `k_m(t)` is decreasing in `t` on `[0,p)` and `alpha > L`, so
`k_m(alpha) <= k_m(L)`; with `c = 2L^{m-2} >= 0` and `(c+a)/(c+b) >= a/b` for
`0 < a <= b`:

```
A_m/B_m >= k_m(alpha)/k_m(L)
        = (p^{m-1} - alpha^{m-1})(p+L) / [ (p+alpha)(p^{m-1} - L^{m-1}) ]
        >= (1 - x^{m-1}) * p/(p+alpha)  =  (1 - x^{m-1})/(1+x)
        >= (1 - x^14)/(1+x)                                (m-1 >= 14, 0<x<1),
rho >= rho_lb := (1 - x^14) sqrt(alpha) / (2 sqrt2 f (1+x)) > 0.              (5)
```

**(3b) eps upper bound.** From `eps = e/(4 (1-e)^2 kappa (1+rho))` (exact) and (3), (5):

```
eps <= eps_ub := min( 1/4 ,  e / (4 (1-e)^2 kappa (1 + rho_lb)) ).            (6)
```

**(3c) Pi lower bound.** `0 < y < 1` and `m-1 >= 14` give `y^{m-1} <= y^14`; with (6):

```
Pi_m >= Pi_lo := sqrt(1-e) (1-l)(1-y^14)(1-eps_ub)/(1+y).                     (7)
```

**(3d) Lambda upper bound.** `0 < y < 1`, `m >= 15`:

```
Lam_L = y^m p^2/(m d alpha) <= Lam_bar := y^15 p^2 / (15 d alpha).            (8)
```

**(3e) J upper bound.** Fix `(e,kappa)`; on real `n in (A, oo)`,
`(ln J)''(n) = -1/(n-A)^2 + 1/(n+1)^2 < 0` (as `0 < n - A < n + 1`), so `J` is strictly
log-concave. Moreover `(ln J)'(n) = ln x + 1/(n-A) - 1/(n+1) <= -(1-x) + 1/(n-A)`
(using `ln x <= x - 1`), which is `<= 0` whenever `n >= A + 1/(1-x)`. Hence with

```
N := max( 14, ceil( A + 1/(1-x) ) + 1 ),
Jhat := max( 0, max_{14 <= n <= N, n integer} J(n) ),
```

every integer `n >= 14` satisfies `J(n) <= Jhat`: for `n <= A` because `J(n) <= 0`; for
`A < n <= N` by inclusion in the scan; for `n > N` because `J` is nonincreasing on
`[N, oo)` and `J(N) <= Jhat`. (9)

## Step 4. The two-variable battle

**Battle inequality.** For all `(e, kappa) in D1`:

```
Pi_lo(e,kappa)  >=  Jhat(e,kappa) + Lam_bar(e,kappa).                        (10)
```

*Proof of (10): finite certificate in exact rational arithmetic.* The Root box (Step 0)
is tiled by the 18 leaves listed below (obtained by axis-aligned bisection; the tiling is
exact by construction and is Monte-Carlo audited in the verifier, T3). One leaf is
**EMPTY**: it satisfies `kappa^+ < kappa_xi(e^-)`, and since `kappa_xi` is increasing in
`e`, it contains no point of `D1`. Each of the 17 **PASS** leaves
`B = [e^-, e^+] x [kappa^-, kappa^+]` satisfies the endpoint inequality

```
Pi_box(B)  >=  Jbox(B) + Lambox(B) + 1/20                                    (11)
```

in exact rational arithmetic (dyadic directed rounding, 120 fractional bits; every
rounding is outward), where the box functionals are defined by the following bounds,
valid for every `(e,kappa) in B ∩ D1`:

* Monotone primitives (exact interval endpoints):
  `alpha in [alpha^-, alpha^+] = [(1-e^+)/2, (1-e^-)/2]`; `d >= d^- = kappa^- e^-`;
  `p in [p^-, p^+] = [(1+e^-)/2 + kappa^- e^-, (1+e^+)/2 + kappa^+ e^+]`;
  `L^2 in [L2^-, L2^+]` with `L2^- = max(0, e^-(1-e^-)/2 - kappa^+(1+kappa^+)(e^+)^2)`,
  `L2^+ = e^+(1-e^+)/2 - kappa^-(1+kappa^-)(e^-)^2` (the two summands of
  `L^2 = e(1-e)/2 - kappa(1+kappa)e^2` are separately monotone; `e < 1/2`).
* `x = alpha/p` is decreasing in `e` and in `kappa` (numerator decreasing, denominator
  increasing), so `x <= x^+ := alpha^+/p^-` and `x >= x^- := alpha^-/p^+`, both attained
  at box corners. `A = x(1+1/kappa)` is a product of positive factors each decreasing
  in `(e,kappa)`, so `A >= A^- := x^- (1 + 1/kappa^+)`, attained at the corner
  `(e^+, kappa^+)`.
* Derived bounds with directed rounding and directed rational `sqrt`:
  `L <= L^+ := sqrt_up(L2^+)`, `L >= L^- := sqrt_dn(L2^-)`; `y <= y^+ := L^+/p^-`;
  `l <= l^+ := L^+/alpha^-`; `f <= f^+ := alpha^+ - L^-`;
  `rho_lb >= rho^- := (1-(x^+)^14) sqrt_dn(alpha^-) / (2 sqrt_up(2) f^+ (1+x^+))`;
  `eps_ub <= eps^+ := min(1/4, e^+/(4(1-e^+)^2 kappa^- (1+rho^-)))`
  (the `1/4` branch is valid pointwise on `D1` by (3));
  `Pi_lo >= Pi_box := sqrt_dn(1-e^+)(1-l^+)(1-(y^+)^14)(1-eps^+)/(1+y^+)`;
  `Lam_bar <= Lambox := (y^+)^15 (p^+)^2/(15 d^- alpha^-)`;
  `Jhat <= Jbox := max(0, max_{14 <= n <= N(B)} (x^+)^{n-2} (n - A^-)/(n+1) )` with
  `N(B) := max(14, ceil(A^- + 1/(1-x^+)) + 1)`. The `Jbox` bound holds for every integer
  `n >= 14` pointwise — for `n <= A^-`: `n <= A`, so `J(n) <= 0 <= Jbox`; for
  `A^- < n <= N(B)`: `J(n) <= (x^+)^{n-2}(n-A^-)/(n+1) <= Jbox`; for `n > N(B)`: the
  pointwise scan-cap argument of (9) applied with parameters `(x^+, A^-)` — the
  comparison function `g(n) := (x^+)^{n-2}(n-A^-)/(n+1) >= J(n)` is nonincreasing on
  `[N(B), oo)` and `g(N(B)) <= Jbox`.

Combining, on `B ∩ D1`: `Pi_lo >= Pi_box >= Jbox + Lambox >= Jhat + Lam_bar`, which is
(10). Every point of `D1` lies in some PASS leaf (Root-box inclusion from Step 0 +
exact tiling + EMPTY-leaf justification), so (10) holds on all of `D1`. ∎

**The 18-leaf certificate** (endpoints are exact rationals — dyadic subdivisions of the
Root box, see `cert_ZB_boxes.csv` for exact values; margins are the exact-arithmetic
values of `Pi_box - Jbox - Lambox`, rounded down):

| # | e-interval | kappa-interval | status | exact margin |
|---|------------|----------------|--------|--------------|
| 1 | [0.016667, 0.063325] | [0.017236, 0.076610] | PASS | 0.1174 |
| 2 | [0.016667, 0.039996] | [0.076610, 0.135984] | PASS | 0.1700 |
| 3 | [0.016667, 0.039996] | [0.135984, 0.254731] | PASS | 0.1056 |
| 4 | [0.016667, 0.039996] | [0.254731, 0.492225] | PASS | 0.0717 |
| 5 | [0.016667, 0.039996] | [0.492225, 0.967213] | PASS | 0.0890 |
| 6 | [0.039996, 0.063325] | [0.076610, 0.135984] | PASS | 0.2141 |
| 7 | [0.039996, 0.063325] | [0.135984, 0.254731] | PASS | 0.1934 |
| 8 | [0.039996, 0.063325] | [0.254731, 0.492225] | PASS | 0.2073 |
| 9 | [0.039996, 0.063325] | [0.492225, 0.967213] | PASS | 0.2556 |
| 10 | [0.063325, 0.109983] | [0.017236, 0.076610] | PASS | 0.2041 |
| 11 | [0.063325, 0.109983] | [0.076610, 0.135984] | PASS | 0.1554 |
| 12 | [0.063325, 0.109983] | [0.135984, 0.254731] | PASS | 0.1525 |
| 13 | [0.063325, 0.109983] | [0.254731, 0.492225] | PASS | 0.1891 |
| 14 | [0.063325, 0.109983] | [0.492225, 0.967213] | PASS | 0.2420 |
| 15 | [0.109983, 0.203300] | [0.017236, 0.135984] | EMPTY (kappa^+ < kappa_xi(e^-)) | — |
| 16 | [0.109983, 0.203300] | [0.135984, 0.254731] | PASS | 0.0940 |
| 17 | [0.109983, 0.203300] | [0.254731, 0.492225] | PASS | 0.1100 |
| 18 | [0.109983, 0.203300] | [0.492225, 0.967213] | PASS | 0.1564 |

(Leaf 15 is empty because `kappa_xi(0.109983...) = 0.13884... > 0.135984...`; the exact
rational comparison is part of the certificate.)

## Step 5. Assembly

Let `(q, alpha, m)` be as in the Lemma. By Step 0, `(e,kappa) in D1`. Chain (2), (9),
(8), (10), (7), (4):

```
R_m / D <= J(m-1) + Lam_L <= Jhat + Lam_bar <= Pi_lo <= Pi_m <= P / D,
```

and `D > 0` gives `R_m <= P`, which is (Z-B). ∎

---

## Constants (summary)

* Zone cap: `e1 = 2033/10000` (zone empty above it; exact margin `h(e1) = 376819811e-12`).
* Root box: `[1/60, 2033/10000] x [60/3481, 59/61]`.
* Certified per-box exact margin: `>= 1/20`; smallest certified margin `0.0717` (leaf 4).
* Payment discount: `eps <= 1/4` globally on the zone; `rho_lb` as in (5).
* Scan caps `N` never exceeded `~90` in the certificate.

## Verification results (`check_ZB_final.py`, mpmath 60 dps + exact rationals)

```
Part 0  directed rounding/sqrt unit tests                    OK (2000 cases)
Part A  h(e1) = 3.768198e-04 > 0 exact; min(kxi-khi) on [e1,1/3) = +4.87e-04   OK
Part B  9360 adversarial (e,kappa,m) points (kappa = kxi and khi exact,
        e = 1/60 and e = 2033/10000 exact, m in {15,...,100001}):
        C1 (identity)      -5.2e-57 (roundoff)      C2 defect UB    +6.16e-04
        C3 (identity)      -2.1e-58 (roundoff)      C4 payment LB   -6.0e-61 (roundoff)
        C5 rho-rho_lb      +2.11e-02                C6 eps_ub-eps   +9.67e-05
        C6b 1/4-eps        +3.07e-02                C7 Pi_m-Pi_lo   +6.75e-05
        C8 Jhat-J(n)       +0.0 (equality at argmax n; tested to n = 10^4)
        C9 Lam_bar-Lam_L   +0.0 (equality at m=15)  C11 (P-R)/P     +4.70e-01
Part C  battle on 160x120 grid: min margin +0.2065, min ratio 1.6731
        (tightest: e = 1/60, kappa ~ 0.46)
Part D  exact-rational certification: 17 PASS + 1 EMPTY leaves, min margin 0.0717
        T1 degenerate-box direction OK; T2 enclosure OK (1696 pts);
        T3 coverage audit OK (99962 random domain points, 0 misclassified)
```

The three tiny negative entries are floating-point roundoff on exact identities /
near-identities at 60-digit precision (magnitudes < 1e-56); every genuine inequality of
the chain has strictly positive slack.

## Scope and honesty notes

* Status: **(ii) reduced to explicit finite rational certificates** for Step 4
  (17 machine-checkable box inequalities in exact rational arithmetic, listed above and
  in `cert_ZB_boxes.csv`), and **(i) proved analytically** for Steps 0-3 and 5.
  No step relies on floating-point evidence.
* The lemma covers all integers `m >= 15` (oddness not needed) and does not need the
  `R_m > 0` hypothesis.
* **Coverage warning for the orchestrator.** Zone B as proved covers exactly
  `{e in [1/60, 1/3), xi >= 1}`. Together with Zone A (`e <= 1/60, xi >= 1`) and Zone
  C-small (`e <= 1/60, xi <= 1`) the union is `{e <= 1/60} ∪ {xi >= 1}`. The remaining
  set `{e in (1/60, 1/3), xi < 1}` is **nonempty and contains positive-defect points**:
  e.g. `e = 0.05, kappa = 0.05` is admissible (`kappa_max = 0.9048, kappa_q = 2.833`),
  has `xi = 0.9025 < 1`, and `R_201 = +6.4e-66 > 0` (also `e = 0.2, kappa = 0.3,
  m = 101`: `xi = 0.96, R_m = +6.4e-41`). So a further lemma (ultra-thin at moderate
  `e`; the natural tool is the `lambda = min(1, 2 rho xi)` certificate of Zone C) is
  still required before the zones tile the whole admissible domain.
* The proof uses only: the defect identity, Bernoulli/`1-t^n <= n(1-t)`,
  `ln x <= x-1`, monotonicity of `k_m`, the mediant inequality `(c+a)/(c+b) >= a/b`,
  log-concavity of `J`, elementary monotonicities in `(e,kappa)`, and exact rational
  interval evaluation on 18 boxes.
