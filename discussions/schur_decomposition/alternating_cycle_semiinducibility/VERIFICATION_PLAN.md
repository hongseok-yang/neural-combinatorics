# Verification plan — central fixed-density inequality for alternating cycles

## Milestone dashboard

| Milestone | Deliverable | Status | Difficulty |
|---|---|:---:|:---:|
| M0 | Baseline build, axiom audit, and numerical harness | ✅ done | Easy |
| M1 | Density parameters and centered-kernel definitions | ✅ done | Medium |
| M2 | Period-two color word and parameterized diagonal Schur model | ✅ done | Medium |
| M3 | Weighted excursion coefficients and diagonal matrix inequality | ✅ done | Medium |
| M4 | Normalized centered operator and Krylov spectral model | ✅ done | Hard |
| M5 | Kernel-algebra cubic head bound | ✅ done | Medium |
| M6 | Strong inequality, profile bound, integral form, and sharpness | ✅ done | Medium |
| M7 | Final source, statement, build, and axiom audit | ✅ done | Easy |

Status key: ✅ done · 🚧 work in progress · ❌ not started.

Target paper: `../alternating_cycles_density_semi_inducibility.tex`.

---

## 0. Target and completion standard

Let `W` be a graphon on an arbitrary probability space, let

```text
p = t(K_2,W),   q = 1-p,
```

and let `m >= 3` be odd. Under

```text
(5 - sqrt 5)/10 <= p <= (5 + sqrt 5)/10,
```

the formalization proves

```text
Alt_{2m}(W) + t(C_{2m},W-p) <= (p*q)^m,
Alt_{2m}(W) <= (p*q)^m.
```

The constant graphon calculation

```text
Alt_{2m}(p) = (p*q)^m
```

is included as a regression theorem showing that the upper bound is sharp. No uniqueness statement
is part of this project.

Completion requires:

1. The strong inequality and its profile consequence in trace form.
2. The same inequalities in integral cycle-density form.
3. A theorem for arbitrary probability spaces, with no step-graphon assumption.
4. Inclusion of both endpoints of the central density interval.
5. The constant-graphon sharpness calculation.
6. `lake build` with no project warnings or errors.
7. No `sorry`, `admit`, declaration-level `axiom`, or `native_decide`.
8. `CheckAxioms.lean` reports only `propext`, `Classical.choice`, and `Quot.sound`.

The verified environment is:

```text
Lean 4.31.0
Mathlib v4.31.0
lean/.lake/packages
  -> discussions/goodman-style-bound/new_lean/.lake/packages
```

---

## 1. Lean proof route

The graphon theorem uses a finite diagonal spectral model obtained directly from the Krylov
compression. It does not require a fixed-density theorem for arbitrary symmetric matrices.

The proof pipeline is:

```text
graphon W of density p
  -> normalized centered kernel K = (W-p)/sqrt(pq)
  -> finite Krylov compression preserving moments through degree 2m
  -> diagonal eigenvalue model (lambda_i,e_i)
  -> weighted Schur coefficient inequality
  -> universal rank-one moment expression
  -> strong graphon inequality.
```

The implementation principles are:

1. Use the diagonal spectrum produced inside the Krylov construction; do not add a conjugation
   theorem for the density-dependent matrix inequality.
2. Define the normalized centered operator directly from the graphon operator and the projection
   onto constants; do not redesign the bounded-kernel operator API.
3. Use specialized variance and Bessel estimates for the normalized centered kernel; do not create
   a generic Hilbert--Schmidt abstraction.
4. Define the weighted coefficients by
   ```text
   densityBeta delta n = beta n - delta*nu n
   ```
   and prove a weighted double-sum representation only where positivity is needed.
5. Prove the cubic first-coefficient estimate in the kernel algebra from nonnegative red and blue
   kernels.
6. Reuse the formal resolvent, logarithmic derivative, size-two Schur, divided-difference, and odd
   coefficient machinery.

---

## 2. Public definitions and statements

### 2.1 Central density

Use the polynomial predicate internally:

```lean
def CentralDensity (p : Real) : Prop :=
  0 < p /\ p < 1 /\ (2*p-1)^2 <= p*(1-p)
```

Prove the public interval equivalence:

```lean
theorem centralDensity_iff_interval :
    CentralDensity p <->
      (5 - Real.sqrt 5)/10 <= p /\
      p <= (5 + Real.sqrt 5)/10
```

For `CentralDensity p`, define a parameter package containing

```text
q     = 1-p,
s     = sqrt(p*q),
a     = s/p,
b     = s/q,
delta = b-a.
```

The package exposes:

```text
p > 0,
q > 0,
s > 0,
s^2 = p*q,
a*b = 1,
delta = (p-q)/s,
abs delta <= 1.
```

Downstream modules consume these identities without unfolding square roots.

### 2.2 Centered kernels

Define

```lean
def centered (W : Omega -> Omega -> Real) (p : Real) :=
  fun x y => W x y - p

def normalizedCentered (W : Omega -> Omega -> Real) (p s : Real) :=
  fun x y => (W x y - p)/s
```

Prove the `GoodK`, symmetry, scalar-composition, trace, and cycle-density lemmas required by the
kernel algebra and `Positivity.lean`.

Use `edgeDensity W mu = p` as the public density hypothesis and prove the bridge to
`doubleMean mu W = p` once.

### 2.3 Public theorems

The trace-form statements should have the shape

```lean
theorem fixedDensity_strong
    (hW : IsGraphon W mu)
    (hp : edgeDensity W mu = p)
    (hcentral : CentralDensity p)
    (hm : Odd m) (hm3 : 3 <= m) :
    altDensity W mu m
      + signedCycleDensity (centered W p) mu (2*m)
        <= (p*(1-p))^m

theorem fixedDensity_alt_le
    (hW : IsGraphon W mu)
    (hp : edgeDensity W mu = p)
    (hcentral : CentralDensity p)
    (hm : Odd m) (hm3 : 3 <= m) :
    altDensity W mu m <= (p*(1-p))^m
```

Add `fixedDensity_strong_integral`, `fixedDensity_alt_le_integral`, and the constant graphon theorem
`constant_fixedDensity_alt`.

---

## 3. Period-two rank-one word

For scalars `a,b`, define

```text
colorPattern a b (2r)   = a,
colorPattern a b (2r+1) = -b.
```

Using the generic normal form in `Necklace/RankOne.lean`, prove

```text
word (colorPattern a b) j k (2m)
  = ((j+a*k)*(j-b*k))^m,

alphaC (colorPattern a b) (2m)
  = (-a*b)^m.
```

If `a*b=1` and `m` is odd, cyclic trace gives

```text
tau (((j+a*k)*(j-b*k))^m) + tau(k^(2m))
  = N_m(colorPattern a b, moments).
```

### Kernel specialization

Let

```text
K = (W-p)/s,
a = s/p,
b = s/q.
```

In the kernel algebra prove

```text
j+a*K = W/p,
j-b*K = (1-W)/q.
```

Therefore

```text
tau (((j+a*K)*(j-b*K))^m)
  = Alt_{2m}(W)/(p*q)^m,

tau(K^(2m))
  = t(C_{2m},W-p)/(p*q)^m.
```

The result is an equality between the normalized sum of graphon densities and a universal
expression in the normalized centered moments.

Gate M2-A: this identity compiles for arbitrary probability spaces.

---

## 4. Parameterized diagonal Schur model

For spectral data `lambda : Fin n -> Real`, coordinates `e : Fin n -> Real`, and scalars `a,b`, use

```text
A = diagonal lambda,
P = e outer e,
u = A e,
Y = A^2,
L = (P+a*A)*(P-b*A).
```

The rank-two decomposition is

```text
I-zL = I+zA^2 + U V,
U = z [e,-a*u],
V = [b*u-e; e].
```

Parameterize the constructions in `Matrix/Model.lean` that depend on `L`, `U`, and `V`. The generic
files

```text
Matrix/Series/Resolvent.lean
Matrix/Series/Schur.lean
Matrix/Series/Jacobi2.lean
Matrix/Scalar/LogDeriv.lean
```

remain independent of `a,b`.

For

```text
h = <e,(I+zA^2)^(-1)e>,
k = <e,A(I+zA^2)^(-1)e>,
l = <e,A^2(I+zA^2)^(-1)e>,
```

the size-two Schur matrix has entries

```text
[ 1+z(b*k-h)   z(a*k-l) ]
[ z*h           1-z*a*k ]
```

and, using `a*b=1`,

```text
det M2 = 1-z*F,
F = h^2-delta*k+z*k^2,
delta = b-a.
```

The established trace-series identity then yields, for odd `m`,

```text
Tr(L^m)+Tr(A^(2m))
  = coeff m (logDeriv(1-z*F)).
```

Gate M2-B: the determinant and trace identities compile for diagonal `A` and match numerical
regressions at both density endpoints.

---

## 5. Weighted excursion coefficients

Retain the spectral moments

```text
tau  = sum_i lambda_i^2,
mu r = sum_i e_i^2*lambda_i^(2r),
nu r = sum_i e_i^2*lambda_i^(2r+1).
```

Define

```text
densityBeta delta n = beta n - delta*nu n.
```

### Series identity

Derive

```text
h^2-delta*k+z*k^2 = betaSeries (densityBeta delta)
```

from the formulas already available for `h^2+z*k^2` and `k`. Do not repeat the Cauchy-product proof.

### Weighted representation

Prove

```text
densityBeta delta n =
  sum_i sum_j e_i^2*e_j^2*c_n(lambda_i,lambda_j)
    *(1-delta*(lambda_i+lambda_j)/2).
```

This uses

```text
(lambda_i+lambda_j)*c_n(lambda_i,lambda_j)
  = lambda_i^(2n+1)+lambda_j^(2n+1).
```

### Monotonicity hypotheses

The diagonal theorem assumes

```text
sum_i e_i^2 = 1,
tau <= 1,
nu 0 = 0,
2*mu 1-delta*nu 1 <= 1,
abs delta <= 1.
```

From these prove:

1. `abs lambda_i <= 1`.
2. `1-delta*(lambda_i+lambda_j)/2 >= 0`.
3. `densityBeta delta n >= 0`.
4. `densityBeta delta 0 = 1`, using `nu 0=0`.
5. `densityBeta delta 1 = 2*mu 1-delta*nu 1`.
6. For `n>=1`,
   ```text
   densityBeta delta (n+1) <= tau*densityBeta delta n.
   ```

Thus

```text
1 = densityBeta delta 0
  >= densityBeta delta 1
  >= densityBeta delta 2 >= ... >= 0.
```

Apply `coeff_logDeriv_betaSeries_le_one` directly to conclude the diagonal inequality

```text
Tr(((P+a*A)*(P-b*A))^m)+Tr(A^(2m)) <= 1.
```

No theorem for a nondiagonal symmetric matrix is required.

Gate M3: `matrix_fixedDensity_diagonal` compiles and passes the axiom audit.

---

## 6. Normalized centered operator and Krylov spectrum

Let `s=sqrt(p*q)`. Define the continuous linear operator directly by

```text
centeredOp = (1/s) * kernelOpCLM W - (p/s) * oneProj.
```

Prove:

```text
centeredOp is symmetric,
centeredOp acts by the kernel (W-p)/s,
<1,centeredOp 1> = 0.
```

### Square budget

First prove

```text
kernelSqNorm (W-p) <= p*q.
```

Use the pointwise inequality

```text
(W-p)^2 <= (1-2p)*W+p^2,
```

whose difference is `W-W^2 >= 0`, and then integrate using `doubleMean W=p`. Scale by `s^2=p*q` to
obtain

```text
kernelSqNorm ((W-p)/s) <= 1.
```

Adapt the finite-family Bessel estimate specifically to `centeredOp`:

```text
sum_i ||centeredOp(v_i)||^2 <= 1
```

for every finite orthonormal family. A generic bounded-kernel theorem is not required.

### Diagonal Krylov output

Use the generic Krylov subspace definitions with

```text
T = centeredOp,
g = oneL2,
cutoff = 2*m.
```

Package the eigenvalues and coordinates of the compressed symmetric operator directly as spectral
data. Prove

```text
sum_i e_i^2 = 1,
sum_i lambda_i^2 <= 1,
sum_i e_i^2*lambda_i^j = centeredMoment j  for j <= 2*m.
```

Since `m>=3`, degrees `1,2,3` needed by the weighted coefficient theorem are within the cutoff.

There is no intermediate arbitrary symmetric matrix theorem and no density-dependent conjugation
module.

Gate M4: `exists_fixedDensity_spectrum` provides the diagonal data and exact moment agreement.

---

## 7. Cubic head bound in the kernel algebra

Let `k` be the normalized centered kernel element and define

```text
r = j+a*k = W/p,
bK = j-b*k = (1-W)/q.
```

The kernels of `r` and `bK` are pointwise nonnegative. Therefore

```text
phi(r*bK*r) >= 0,
phi(bK*r*bK) >= 0.
```

Using `phi(k)=0`, the rank-one identity for `j`, and cyclicity, prove

```text
phi(r*bK*r) = 1-2*mu_2-a*mu_3,
phi(bK*r*bK) = 1-2*mu_2+b*mu_3.
```

The convex combination with weights `q,p` is

```text
q*phi(r*bK*r)+p*phi(bK*r*bK)
  = 1-2*mu_2+delta*mu_3 >= 0.
```

Hence

```text
2*mu_2-delta*mu_3 <= 1.
```

Prove positivity before algebraic expansion. The order argument then depends only on nonnegative
kernels, while the identity is handled separately by ring and moment rules.

Transport the degree-two and degree-three moments to the diagonal Krylov spectrum.

Implemented in `AlternatingCycle/Compression/DensityCubic.lean`. The kernel positivity certificate,
both cubic expansions, the weighted head inequality, and its finite-spectrum transport compile.

Gate M5: the spectral data satisfy the first-coefficient hypothesis of
`matrix_fixedDensity_diagonal`.

---

## 8. Main inequality

The graphon and diagonal matrix instances of the period-two rank-one word produce the same universal
moment expression. Moment agreement through degree `2*m` identifies them term by term.

Apply the diagonal matrix inequality to obtain

```text
Alt_{2m}(W)/(p*q)^m
  + t(C_{2m},W-p)/(p*q)^m
  <= 1.
```

Since `p*q>0`, multiply through to prove `fixedDensity_strong`.

Apply even-cycle nonnegativity to the symmetric centered kernel:

```text
t(C_{2m},W-p) >= 0.
```

Dropping this term proves `fixedDensity_alt_le`.

Use `altDensity_eq_integral` and `signedCycleDensity_eq_integral` to prove the integral forms. The
Fubini machinery already accepts arbitrary `GoodK` kernels.

Finally calculate the constant graphon:

```text
Alt_{2m}(p) = p^m*q^m = (p*q)^m,
t(C_{2m},p-p) = 0.
```

Implemented in `AlternatingCycle/DensityMain.lean`. The strong and profile inequalities compile in
trace and integral form on the closed central interval, and the constant-graphon equality compiles.

Gate M6: all public theorems in Section 2.3 compile for arbitrary probability spaces.

---

## 9. Module plan

Add:

```text
AlternatingCycle/Parameters.lean
```

Concentrate theorem-specific changes in:

```text
AlternatingCycle/Defs.lean
AlternatingCycle/Necklace/Trace.lean
AlternatingCycle/Necklace/MatrixInstance.lean
AlternatingCycle/Necklace/KernelInstance.lean
AlternatingCycle/Matrix/Model.lean
AlternatingCycle/Matrix/Spectral.lean
AlternatingCycle/Matrix/Beta.lean
AlternatingCycle/Matrix/MatrixMain.lean
AlternatingCycle/Compression/L2.lean
AlternatingCycle/Compression/HSBound.lean
AlternatingCycle/Compression/Krylov.lean
AlternatingCycle/Main.lean
AlternatingCycle/Sharp.lean
AlternatingCycle.lean
CheckAxioms.lean
```

Use without density-specific changes:

```text
AlternatingCycle/Matrix/Scalar/Cn.lean
AlternatingCycle/Matrix/Scalar/LogDeriv.lean
AlternatingCycle/Matrix/Scalar/OddLog.lean
AlternatingCycle/Matrix/Series/Resolvent.lean
AlternatingCycle/Matrix/Series/Schur.lean
AlternatingCycle/Matrix/Series/Jacobi2.lean
AlternatingCycle/Necklace/RankOne.lean
AlternatingCycle/Necklace/Unitize.lean
the generic Krylov subspace definitions
AlternatingCycle/Fubini.lean
AlternatingCycle/Positivity.lean
AlternatingCycle/Foundation/*
```

`Matrix/Conjugation.lean` is not on the dependency path of the fixed-density theorem.

---

## 10. Milestones and gates

### M0 — baseline and numerical harness

- Record the clean Lean build and axiom audit.
- Check `a*b=1`, `abs delta<=1`, and the endpoint values.
- Check the parameterized rank-one word.
- Check the rank-two determinant.
- Check the weighted coefficient series and monotonicity.
- Check the end-to-end inequality on finite weighted graphons.
- Reproduce an even-`m` parity counterexample at `p=1/2`.

Gate: all algebraic identities agree to `1e-10`; inequality excess is at most `2e-9`.

### M1 — parameters and definitions

- Implement `CentralDensity` and its interval equivalence.
- Package `p,q,s,a,b,delta` and their identities.
- Define centered and normalized centered kernels.

Gate: downstream tests use parameter lemmas without unfolding square roots.

### M2 — color word and Schur model

- Prove the period-two word and pure coefficient.
- Add kernel and diagonal matrix instances.
- Parameterize the rank-two model and prove `det M2=1-zF`.

Gate: the Schur and universal-moment identities compile.

### M3 — weighted coefficients and diagonal inequality

- Define `densityBeta=beta-delta*nu`.
- Prove its weighted representation, positivity, normalization, and contraction.
- Identify the Schur series.
- Apply the odd logarithmic coefficient theorem.

Gate: `matrix_fixedDensity_diagonal` passes `#print axioms`.

### M4 — centered operator and Krylov spectrum

- Implement `centeredOp` as a graphon-operator/projection combination.
- Prove its pointwise kernel action, symmetry, mean zero, and square budget.
- Adapt the finite Bessel estimate.
- Return diagonal spectral data and moment agreement from Krylov compression.

Gate: `exists_fixedDensity_spectrum` supplies all spectral hypotheses except the cubic head bound.

### M5 — cubic positivity

- Define normalized red and blue kernel elements.
- Prove nonnegativity of the two triple products.
- Expand their convex combination into the first-coefficient defect.
- Transport the bound to the Krylov spectrum.

Gate: the diagonal spectrum satisfies `densityBeta delta 1 <= 1`.

### M6 — graphon theorem

- Match the graphon and diagonal universal moment expressions.
- Prove the strong inequality and profile consequence.
- Add integral forms and constant sharpness.

Gate: all public theorem statements compile on arbitrary probability spaces.

### M7 — final audit

- Remove unused declarations, imports, and theorem wrappers.
- Ensure documentation describes the final mathematical objects directly.
- Run the numerical regressions, full build, placeholder search, and axiom audit.
- Compare each public Lean statement against the corresponding paper formula.

Completed on 2026-08-23:

- `lake build` succeeded with 8596 jobs.
- `CheckAxioms.lean` reports only `propext`, `Classical.choice`, and `Quot.sound` for every new
  public theorem.
- The project-wide Lean scan found no `sorry`, `admit`, declaration-level `axiom`, or
  `native_decide`.
- Both numerical regression suites passed, including both central-interval endpoints.
- `git diff --check` reported no whitespace errors.

Gate: every requirement in Section 0 is satisfied.

Estimated effort after M0 is 4--7 focused working days for a contributor familiar with the project.
The main technical risk is the normalized centered Krylov operator; the scalar and power-series
engines are already available.

---

## 11. Regression and axiom audit

The numerical suite covers:

```text
p = 1/2,
both central interval endpoints,
interior densities 0.35 and 0.65,
dimensions 2,4,7,10,
odd m = 3,5,7,9,
repeated and nearly zero eigenvalues,
finite weighted graphons of exact prescribed density,
an even-m counterexample.
```

For each appropriate sample verify:

```text
a*b = 1,
abs delta <= 1,
det(I-zL) = det(I+zA^2)*(1-zF),
F = sum_n (-1)^n*densityBeta_n*z^n,
1 = densityBeta_0 >= densityBeta_1 >= ... >= 0,
Tr(L^m)+Tr(A^(2m)) <= 1,
normalized graphon sum = universal moment expression.
```

`CheckAxioms.lean` covers at least:

```text
centralDensity_iff_interval
normalizedCentered_mean_zero
normalizedCentered_kernelSqNorm_le_one
RankOne.word_colorPattern
RankOne.tau_colorPattern_add
alt_add_centeredCycle_eq_necklace
det_M2
densityBeta_zero
densityBeta_nonneg
densityBeta_antitone
densityBeta_series
matrix_fixedDensity_diagonal
exists_fixedDensity_spectrum
cubic_head_le_one
centeredCycleDensity_nonneg
fixedDensity_strong
fixedDensity_alt_le
fixedDensity_strong_integral
fixedDensity_alt_le_integral
constant_fixedDensity_alt
```

---

## 12. Source-writing rules

Module and declaration comments state the mathematical object, hypotheses, and role in the proof.
Repository provenance, migrations, compatibility notes, and development chronology are omitted from
mathematical documentation.

- Include declarations only when they support the final inequality or its verification.
- Describe specialization at `p=1/2` as a mathematical regression case.
- Keep implementation decisions in this plan or the running log, not in theorem docstrings.
- The source should read as a self-contained formal proof of the fixed-density inequality.
