# Zone Z1 (pinch) — complete lemma and proof

Status: **proved analytically with fully explicit constants.** Every numerical
constant below is certified by an exact rational-arithmetic check in
`check_Z1.py` (section S15), and every inequality of the chain is additionally
verified numerically on dense grids (worst slacks reported at the end).

All notation is that of `BRIEF.md`. Throughout: q in (1/3,1/2), p = 1-q,
alpha in (q, r(q)], d = alpha-q, e = 1-2*alpha, L = sqrt(pq-alpha^2),
f = alpha-L, kappa = d/e, T = m*e, and

    R_m   = alpha^m + L^m - p q^{m-1},
    k_m(t)= (p^{m-1}-t^{m-1})/(p+t),
    B_m   = 2 L^{m-2} + m k_m(L),      A_m = 2 L^{m-2} + m k_m(alpha),
    rho   = (A_m/B_m) sqrt(alpha) / (2 sqrt(2) f).

In the (e,kappa) parametrization: alpha = (1-e)/2, d = kappa*e, q = alpha-d,
p = alpha+(1+kappa)e = (1+e+2 kappa e)/2, and the admissible domain is
0 < kappa <= kappa_max(e) = (1-e)/(1+e)  (i.e. L^2 >= 0), plus q > 1/3, which
is not binding for e <= 1/30.

---

## Lemma Z1 (pinch zone, lam = 1 certificate)

**Lemma.** Let m >= 15 be an odd integer and let (q, alpha) be admissible with

    T := m*e <= 1/2        (hence e <= 1/30).

If R_m > 0, then

    R_m  <=  sqrt(2*alpha) * B_m * f * ( d - e^2 / (16*alpha^2*(1+rho)) ).   (Z1)

Consequently R_m <= C_m * psi(xi, rho) on this whole region.

Remarks.
* No lower bound on e, kappa or xi is assumed: (Z1) covers the ENTIRE
  admissible strip T <= 1/2, including the ultra-thin sliver xi -> 0 (where
  R_m > 0 simply fails unless kappa*m is bounded below, Step 3). Hence the
  other zones only ever need T = m*e > 1/2.
* The subtracted term is positive and small: e^2/(16 alpha^2 (1+rho)) <= 0.153*d
  on the region (Step 4), so the right side of (Z1) is >= 0.847*sqrt(2 alpha)*B_m*f*d > 0.

---

## Step 0. Standing bounds on the domain

Let gamma := 1+kappa in (1,2), u := (d+e)/p, x := alpha/p = 1-u,
tau := q/alpha = 1 - d/alpha, y := L/p, l := L/alpha,
lbar := sqrt(2e/(1-e)), w' := (d+e)/alpha.

From m >= 15, T <= 1/2, 0 < kappa <= kappa_max < 1:

  (D1) e = T/m <= min(1/30, T/15).
  (D2) alpha = (1-e)/2 in [29/60, 1/2);   e/alpha = 2e/(1-e) <= 2/29.
  (D3) p = (1+e(1+2kappa))/2, so 1/2 <= p <= (1+3e)/2 <= 0.55;  p = alpha+d+e.
  (D4) L^2 = alpha*e - d(d+e) <= alpha*e, so l <= lbar and
       lbar^2 = 2e/(1-e) <= 2/29, hence lbar <= 0.263      [cert c14a].
  (D5) w' = gamma*e * 2/(1-e) <= 4e/(1-e) <= 4/29 <= 0.138  [cert c14b];
       1 + lbar + w' <= 1.401 <= 1.5                        [cert c14c].
  (D6) u = gamma*e/p <= 2*gamma*e <= (2/15)*gamma*T <= 0.1334*g, g := gamma*T
       (using (D1): e <= T/15)                              [cert: 0.1334 >= 2/15].
  (D7) y < l (p > alpha), and 0 <= tau, x < 1.

Elementary inequalities used (proofs standard, included for completeness):

  (E1) Bernoulli: (1-v)^n >= 1 - n v          (v in [0,1], integer n >= 1).
  (E2) 1 - t^n <= n(1-t)                      (t in [0,1], integer n >= 1).
  (E3) (1-v)^n <= 1 / (1 + n v + C(n,2) v^2)  (v in [0,1), integer n >= 2).
       Proof: (1-v)^{-n} = (1 + v/(1-v))^n >= 1 + n*v/(1-v) + C(n,2)*(v/(1-v))^2
       >= 1 + n v + C(n,2) v^2, by the binomial theorem (all terms >= 0).
  (E4) sqrt(1-e) >= 1 - 0.505 e  for e in [0, 0.039]:
       squaring (both sides in (0,1]), it is equivalent to
       0.255025 e^2 <= 0.01 e, i.e. e <= 0.0392...; holds for e <= 1/30.
  (E5) prod_i (1-a_i) >= 1 - sum_i a_i  for a_i in [0,1] (induction).
  (E6) psi(xi,rho) >= lam*xi - lam^2/(4(rho+lam)) for every lam in [0,1]:
       from psi = min_{0<=v<=1} [rho v^2 + max(xi - v + v^2, 0)] and
       max(w,0) >= lam*w:  psi >= min_v [(rho+lam)v^2 - lam v] + lam*xi
       = lam*xi - lam^2/(4(rho+lam)), the min being at
       v = lam/(2(rho+lam)) in [0, 1/2] subset [0,1].

## Step 1. Defect identity and defect upper bound

Since q = alpha*tau and p*q^{m-1} = p*alpha^{m-1}*tau^{m-1},

  (I)  R_m = alpha^{m-1} * ( alpha - p*tau^{m-1} ) + L^m.

Write alpha - p*tau^{m-1} = alpha(1 - tau^{m-1}) - (d+e)*tau^{m-1}
(using p - alpha = d + e). By (E2), alpha(1-tau^{m-1}) <= (m-1)*d; by (E1),
tau^{m-1} = (1 - d/alpha)^{m-1} >= 1 - (m-1)d/alpha  (valid: 0 < d/alpha < 1).
Hence

  alpha - p*tau^{m-1} <= (m-1)d - (d+e)(1 - (m-1)d/alpha)
                       = (m-1)*d*p/alpha - (d+e),

(using 1 + (d+e)/alpha = p/alpha), and therefore

  (S2)  R_m <= (m-1)*d*p*alpha^{m-2} - (d+e)*alpha^{m-1} + L^m.

## Step 2. Tail bounds

From L^2 <= alpha*e and (D2), for m >= 15:

  (S4)  L^m / alpha^{m-1} <= e * (e/alpha)^{m/2-1} <= e * (2/29)^{13/2}
                          <= 2.83e-8 * e <= 3e-8 * e     [cert c12],

  (S5)  eps1 := L^m/(m d p^{m-1}) <= x^{m-1} (e/alpha)^{m/2-1} / (m kappa)
             <= 2.83e-8/(m*kappa).

## Step 3. Lemma A: positive defect forces kappa*m > 0.8787

Assume R_m > 0. By (S2) and (S4),

  0 < (m-1)*d*p*alpha^{m-2} - (d+e)*alpha^{m-1} + 3e-8 * e * alpha^{m-1}.

Divide by e*alpha^{m-1} and use d = kappa*e, d+e = gamma*e:

  (m-1)*kappa*p/alpha > (1+kappa) - 3e-8,
  i.e.  kappa * [ (m-1)p/alpha - 1 ] > 1 - 3e-8.

Now p/alpha = 1 + (d+e)/alpha <= 1 + 4e/(1-e) <= 33/29 (kappa < 1, e <= 1/30),
so (m-1)p/alpha - 1 <= (33m-62)/29 < 33m/29, giving

  (S3)  m*kappa > (29/33)*(1 - 3e-8) > 0.8787          [cert c11].

(Contrapositive: if kappa <= 0.8787/m then R_m <= 0 and there is nothing to
prove. Numerically the true threshold is m*kappa ~ 1.04; 0.8787 is safe.)

## Step 4. Payment lower bound

A_m, B_m, f > 0 (p > alpha > L >= 0, and f = alpha - L > 0 because
L^2 <= alpha*e < alpha^2 for e < 1/3), hence rho > 0 and

  sub := e^2/(16 alpha^2 (1+rho)) <= subbar := e^2/(16 alpha^2),
  subbar/d = e/(4(1-e)^2 kappa) = T / (4(1-e)^2 * m*kappa)
           <= (1/2)*0.2676/0.8787 <= 0.153              [certs c4, c13, using (S3)].

Using B_m >= m*k_m(L) and k_m(L) = p^{m-1}(1-y^{m-1})/(p+L):

  (S7)  sqrt(2 alpha) B_m f (d - sub)
        >= m d p^{m-1} * G * (1-y^{m-1}) * (1 - subbar/d),
        where G := sqrt(2 alpha) * f/(p+L),

all factors being nonnegative (1 - subbar/d >= 0.847).

## Step 5. Normalized reduction

Divide (S2) and (S7) by m*d*p^{m-1} > 0. With N := m-2-1/kappa+(1+1/kappa)u,
it suffices to prove

  (N)  D := R_m/(m d p^{m-1}) <= W := G (1-y^{m-1}) (1 - subbar/d),

and (S2) gives (note (d+e)/d = 1+1/kappa, x = alpha/p)

  D <= ((m-1)/m) x^{m-2} - ((1+1/kappa)/m) x^{m-1} + eps1
     = x^{m-2} * N/m + eps1.

## Step 6. Lower bound for W

G = sqrt(1-e)(1-l)/(1+w'+l) is decreasing in l, and l <= lbar, so with (D4),
(D5), y < l <= lbar < 1, m-1 >= 14:

  W >= sqrt(1-e) * (1-lbar)/(1+lbar+w') * (1-lbar^14) * (1-subbar/d)
     = (1-lbar)(1-delta)/(1+lbar+w'),

where delta := 1 - sqrt(1-e)(1-lbar^14)(1-subbar/d) in [0,1]. By (E4), (E5),

  (S9)  delta <= deltabar := 0.505 e + lbar^14 + subbar/d.

Note deltabar <= 0.505/30 + 1e-8 + 0.153 <= 0.17 [cert c15a; lbar^14 <= (2/29)^7 <= 1e-8].

## Step 7. Case N <= 0

Then D <= eps1 <= 2.83e-8/0.8787 <= 3.3e-8 [cert c15c], while

  W >= (1 - lbar - deltabar)/(1+lbar+w') >= (1-0.263-0.17)/1.5 > 0.37,

using (E5), (D4), (D5). So (N) holds with huge slack.  [cert c15b]

## Step 8. Case N > 0: reduction to the ledger inequality

By (E3) with n = m-2 >= 13, v = u:

  (S8)  x^{m-2} <= 1/(1+s),  s := z + c z^2,  z := (m-2)u,  c := (m-3)/(2(m-2)).

So D <= N/(m(1+s)) + eps1 and, multiplying (N) through by
m(1+s)(1+lbar+w') > 0, it suffices that

  N (1+lbar+w') + eps1 * m(1+s)(1+lbar+w') <= m(1+s)(1-lbar)(1-deltabar).

Use (1-lbar)(1-deltabar) >= 1-lbar-deltabar (E5), N <= m (because
(1+1/kappa)u <= 2+1/kappa follows from u <= 1), and 1+lbar+w' <= 1.5 (D5):
it suffices that

  N + m(lbar+w') + 1.5 eps1 m(1+s) <= m(1+s) - m(1+s)(lbar+deltabar).

Substituting N = m-2-1/kappa+(1+1/kappa)u and rearranging, this is exactly

  (LEDGER)   m*lbar*(2+s) + m*w' + m(1+s)*deltabar
             + 1.5*m*eps1*(1+s) + (1+1/kappa)*u
             <=  2 + 1/kappa + m*s.

## Step 9. Proof of (LEDGER)

### 9.0 m-elimination

Set X := m*T = m^2*e >= 15*T, Y := sqrt(X), g := gamma*T <= 1. Exact identities
and bounds (all from (D1)-(D6); recall e = T^2/X, m = X/T):

  (M1) z = 2*gamma*T*(1-2/m)/(1+e(1+2kappa)) <= 2 g;  hence
       s <= z + z^2/2 <= 2g + 2g^2  and  2+s <= 2(1+g+g^2),  1+s <= Sbar := 1+2g+2g^2.
  (M2) m*lbar = sqrt(2X/(1-e)):
         on T <= 1/2 (e<=1/30):  m*lbar <= 1.4384*Y   [cert c1: 1.4384^2 >= 60/29]
         on T <= 1/8 (e<=1/120): m*lbar <= 1.42015*Y  [cert c2].
  (M3) m*w' = 2 g/(1-e) <= 2.069 g (e<=1/30) resp. <= 2.01681 g (e<=1/120)
       [certs c5, c5'].
  (M4) m*(subbar/d) = T/(4(1-e)^2 kappa) <= (1/kappa)*cK5*T with
       cK5 = 0.2676 (e<=1/30) resp. 0.25423 (e<=1/120) [certs c4, c4'].
  (M5) m*(1+s)*lbar^14 = (1+s)*(2T/(1-e))^7/m^6 <= 5*(30/29)^7/15^6 <= 1e-6
       (using 2T <= 1, 1+s <= Sbar <= 5, m >= 15).
  (M6) 1.5*m*eps1*(1+s) <= 1.5*(2.83e-8/kappa)*5 <= 3e-7/kappa   [by (S5)].
  (M7) resource:  m*s = m*z*(1+c*z),  with the exact
       m*z = 2*gamma*(X-2T)/(1+e(1+2kappa)) >= 2*gamma*(X-2T)/(1+T/5)
       (since e(1+2kappa) <= 3e <= T/5 by (D1)), and, using
       c >= 6/13 and z >= 2g*(13/15)/(1+T/5) (m >= 15),
         1 + c*z >= 1 + 0.8*g/(1+T/5)          [(6/13)(26/15) = 4/5 exactly].
       Hence   m*s >= Alow*(X - 2T) > 0,
       Alow := (2*gamma/(1+T/5)) * (1 + 0.8*g/(1+T/5)).

### 9.1 The 1/kappa bracket

The costs carrying a factor 1/kappa are (M4), the u/kappa part of
(1+1/kappa)u (which is <= (1/kappa)*0.1334*g by (D6)), and (M6). Total:
(1/kappa)*beta with

  beta := cK5*T*Sbar + 0.1334*g + 3e-7 <= 0.2676*(1/2)*5 + 0.1334 + 3e-7 <= 0.803 < 1
  [cert c18].

Since kappa < kappa_max < 1, 1/kappa > 1, so

  2 + 1/kappa - (1/kappa)*beta >= 2 + (1-beta) = 3 - beta.

### 9.2 The quadratic form

Combining 9.0-9.1, (LEDGER) follows from  H(Y) >= 0  for the relevant Y, where

  H(Y) := Alow' * Y^2 - Bbar * Y + Cbar,
  Bbar := 2*cK1*(1+g+g^2)        (cK1 = 1.4384 resp. 1.42015),
  Cbar := 3 - beta - [2T*Alow-term] - cK2*g - 0.505*T*Sbar - 0.1334*g - 1e-6
          (cK2 = 2.069 resp. 2.01681; the 0.505*T*Sbar is K3 = m*0.505e*(1+s);
           the second 0.1334*g is the direct u-part; 1e-6 is (M5)),

and Alow' is a per-case lower bound for Alow. Two cases:

### 9.3 Case P1: T <= 1/8 (covers all Y >= 0)

Here g <= 1/4, Sbar <= 13/8, e <= 1/120. Bounds:

  Alow >= 2*gamma/(1+T/5) >= 1.9512*gamma          [cert c9a],
  Alow <= 2*gamma*(1+0.8g) <= 2.4*gamma            [cert c9d],
  Bbar <= 2.8403*(1+1/4+1/16) = 3.727894  (so Bbar^2 <= 13.8972),
  Cbar >= 3 - beta(1/8,gamma) - 2*(1/8)*2.4*gamma - 2.01681*(gamma/8)
          - 0.505*(1/8)*(13/8) - 0.1334*(gamma/8) - 1e-6
       =: Clow(gamma)   (linear, decreasing in gamma; every subtracted term is
          increasing in T, so evaluating at T = 1/8 is valid for all T <= 1/8).

Then H(Y) >= 1.9512*gamma*Y^2 - 3.727894*Y + Clow(gamma), and

  psi(gamma) := 4*1.9512*gamma*Clow(gamma) - Bbar^2

is a concave quadratic in gamma with (exact rational arithmetic)

  psi(1) = 1.4029... > 0,   psi(2) = 2.8814... > 0     [certs c9b, c9c],

hence psi > 0 on [1,2]: the discriminant of H is negative and H(Y) > 0 for
ALL Y >= 0. Case P1 done (no constraint on X needed).

### 9.4 Case P2: 1/8 <= T <= 1/2 (uses X >= 15T)

Here use the T <= 1/2 constants (cK1 = 1.4384, cK2 = 2.069, cK5 = 0.2676) and

  Alow >= A' := 1.81818*gamma*(1 + 0.72727*g)     [certs c16d, c16e],

so m*s >= A'(X-2T), and H(Y) = A'Y^2 - Bbar*Y + (C0 - 2T*A') with
C0 := 3 - beta - 2.069g - 0.505*T*Sbar - 0.1334g - 1e-6.

(a) Vertex location. Y* = Bbar/(2A') = 0.79113*(1+g+g^2)/(gamma*(1+0.72727g))
    [cert c10a]. For fixed T, the numerator over gamma, 1/gamma + T + gamma*T^2,
    is nonincreasing in gamma (since g = gamma*T <= 1), and the denominator is
    increasing, so Y* is maximal at gamma = 1:
    Y* <= 0.79113*(1+T+T^2)/(1+0.72727T), which is increasing in T
    (derivative of (1+T+T^2)/(1+0.72727T) has numerator
    0.27273 + 2T + 0.72727T^2 > 0), hence
    Y* <= 0.79113*1.75/1.363635 <= 1.0153 <= sqrt(15/8) <= sqrt(15T)
    [certs c10b, c10c]. So on Y >= sqrt(15T), H is minimized at Y = sqrt(15T).

(b) Value at X = 15T.  Phi(T,gamma) := H(sqrt(15T)) = 13*T*A' - Bbar*sqrt(15T) + C0.
    Using Bbar*sqrt(15T) <= 11.142*(1+g+g^2)*sqrt(T) [cert c3] and
    C0 >= 3 - 0.7726*T*Sbar - 2.336*g - 2e-6 [certs: 0.7726 = 0.2676+0.505,
    c16f: 2.336 >= 2.069 + 2*0.1334], expand in powers of gamma:

      Phi(T,gamma) >= a0(T) + a1(T)*gamma + a2(T)*gamma^2,
      a0(T) = 3 - 2e-6 - 0.7726*T - 11.142*sqrt(T),
      a1(T) = T*(21.30034 - 1.5452*T - 11.142*sqrt(T)),
      a2(T) = T^2*(17.18999 - 1.5452*T - 11.142*sqrt(T)),

    [certs c16a-c17e for the coefficient assembly: 13*1.81818 >= 23.63634,
    13*1.81818*0.72727 >= 17.18999, 23.63634 - 2.336 >= 21.30034].
    On T <= 1/2, sqrt(T) <= 0.70711, so
    21.30034 - 0.7726 - 11.142*0.70711 > 0 and 17.18999 - 0.7726 - 7.879 > 0
    [certs c17a, c17b]: a1, a2 > 0, hence Phi(T,gamma) >= Phi(T,1) =: phi(T)
    for all gamma >= 1.

(c) The one-variable inequality phi(T) >= 0 on [1/8, 1/2]. With tau := sqrt(T)
    in [0.35355, 0.70711] [certs c19a, c17c]:

      phi = 3 - 2e-6 + 20.52774 tau^2 + 15.64479 tau^4 - 1.5452 tau^6
            - 11.142 (tau + tau^3 + tau^5).

    Interval I1 = [0.35355, 1/2]: tau^3 <= tau/4, tau^5 <= tau/16,
    tau^6 <= 1/64, tau^4 >= 0 give
      phi >= 2.97584 + 20.52774 tau^2 - 14.62388 tau    [certs c7a, c7b],
    whose discriminant is negative [cert c7c]; positive for all tau.

    Interval I2 = [1/2, 0.70711]: tau^3, tau^5, tau^6 are convex, so each is
    bounded above on [a,b] = [1/2, 70711/100000] by its secant line
    s_k*tau + i_k (computed in exact rationals in check_Z1.py), and
    tau^4 >= tau^2/4 (tau >= 1/2). This yields
      phi >= 11.70546 + 24.43894 tau^2 - 32.08310 tau,
    whose discriminant is negative [cert c8b]; positive for all tau.

    Hence phi(T) > 0 on [1/8, 1/2], completing Case P2.

Cases P1 and P2 cover T in (0, 1/2], so (LEDGER) holds, hence (N), hence (Z1). ∎

## Step 10. Consequence R_m <= C_m psi(xi, rho)

By (E6) with lam = 1: psi >= xi - 1/(4(1+rho)). Multiplying by
C_m = B_m f sqrt(2 alpha) e^2/(4 alpha^2) and using the exact identities
C_m * xi = sqrt(2 alpha) B_m f d  and  C_m/(4(1+rho)) = sqrt(2 alpha) B_m f
* e^2/(16 alpha^2 (1+rho)):

  C_m psi(xi,rho) >= sqrt(2 alpha) B_m f ( d - e^2/(16 alpha^2 (1+rho)) ) >= R_m. ∎

---

## Constants table (all certified in exact arithmetic, check_Z1.py S15)

| constant | role | certificate |
|---|---|---|
| 0.8787 | Lemma A: m*kappa lower bound | (29/33)(1-3e-8) > 0.8787 |
| 3e-8, 2.83e-8 | L^m tails | (2/29)^13 <= (2.83e-8)^2 |
| 0.153 | subbar/d | 0.5*0.2676/0.8787 <= 0.153 |
| 0.505 | sqrt(1-e) linearization | (E4), e <= 1/30 |
| 0.263, 0.138, 1.5 | lbar, w', 1+lbar+w' | 2/29 <= 0.263^2 etc. |
| 1.4384 / 1.42015 | m*lbar <= cK1*Y | cK1^2 >= 2/(1-e_max) |
| 2.069 / 2.01681 | m*w' <= cK2*g | cK2 >= 2/(1-e_max) |
| 0.2676 / 0.25423 | K5 coefficient | cK5 >= 1/(4(1-e_max)^2) |
| 0.1334 | u <= 0.1334 g | 0.1334 >= 2/15 |
| 1e-6, 3e-7 | lbar^14, eps1 tails | (M5), (M6) |
| 1.9512, 2.4 | P1 Alow bounds | 1.9512 <= 2/1.025 |
| 1.81818, 0.72727 | P2 A' coefficients | <= 2/1.1, 0.8/1.1 |
| 11.142 | Bbar*sqrt(15) | 11.142^2 >= 2.8768^2*15 |
| 0.79113, 1.0153 | vertex bound | c10a-c10c |
| 23.63634, 21.30034, 17.18999, 20.52774, 15.64479, 2.336, 0.7726 | Phi/phi coefficients | c16a-c17e |
| I1/I2 quadratics | phi > 0 | disc < 0, exact rationals c7c, c8b |

## Verification status (check_Z1.py, mpmath dps=40)

* S15 exact rational certificates: **all PASS** (Fraction arithmetic).
* Main grid: 11,400 points, m in {15,...,100001}, T in [1e-6, 0.5],
  kappa from 0.8787/m to kappa_max. Every step S1-S17 has nonnegative worst
  slack. Highlights:
  - defect identity residual < 1e-30 (S1);
  - (LEDGER) worst relative margin 0.3898 at (m,T,kappa-frac) = (15, 0.5, 0.15) (S11);
  - decomposed certificate H(Y) worst value +1.64 (S14), i.e. the analytic
    case analysis is nowhere near failing;
  - end-to-end (Z1): worst relative margin 2.6e-5 at (m, T) = (100001, 1e-6)
    (the genuine pinch corner where the target inequality itself is tight,
    margin ~ 2.6/m) (S16).
* Lemma A scan over the FULL kappa range (not just kappa > 0.8787/m):
  min m*kappa over positive-defect points = 1.038 > 0.8787; no violations (S3).
* Fine corner scan (m in [15,31] odd, 100 T-values, 41 kappa-values,
  ~37k points): worst LEDGER margin 0.3896, worst H(Y) = +1.637.

## Interface to the other zones

Lemma Z1 disposes of the entire region T = m*e <= 1/2 for all odd m >= 15 and
all admissible (q, alpha) — with the single certificate lam = 1 and no
xi/kappa restriction. The remaining work (zones Z2/Z3/Z4) is exactly
T > 1/2, where e > 1/(2m); in particular for e <= 1/50 those zones may assume
m > 25/e... i.e. x^{m-2} <= exp(-2(m-2)(1+kappa)e/(1+3e)) <= exp(-0.9/(1+3e))
is bounded away from 1, the intended exponential-slack mechanism of Z2.

Choices made: T0 = 1/2 (the largest value for which the pinch machinery holds
with uniform constants: it forces e <= 1/30, used throughout; pushing T0
further requires e-dependent retuning that belongs to Z2's exponential
regime). No separate e0 is needed inside Z1.
