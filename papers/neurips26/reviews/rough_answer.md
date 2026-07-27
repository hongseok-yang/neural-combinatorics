### How many runs

For every experiments, we repeated the experiment once for each hyperparameter configuration, which sweeps over two activation functions ($\sin$ and $\mathrm{GeLU}$) and four learning rates $10^{-3}, 3 \times 10^{-4}, 10^{-4}, 3\times 10^{-5}$, total 8 configurations for each experiments. 

### Property & Numerical Stability of implicit gradient

One can show that our implicit gradient is consistent. 
1. Assume that the output $f_\theta[0](x, y) \in [-M, M]$ for some $M>0$, which is assured by constructions of our network and from the assumption on the input that $x, y \in [0, 1]$.
2. Then, the optimal $c^*$ is bounded by $[-M + \mathrm{logit}(p), M + \mathrm{logit}(p)]$.
3. By the uniform law of large number, we can see that $\frac{1}{|\Epsilon|}\sum_{(x_1, x_2) \in \Epsilon}f_\theta[c](x_1, x_2)$ almost surely converges to expected value uniformly over $c \in [-M + \mathrm{logit}(p), M + \mathrm{logit}(p)]$.
4. Since the function $c \mapsto \frac{1}{|\Epsilon|}\sum_{(x_1, x_2) \in \Epsilon}f_\theta[c](x_1, x_2)$ is continuous, the optimal $c^*$ converges to the population-optimal $c^*$ almost surely also.
5. Finally, the continuous mapping theorem asserts that the implicit gradient converges to the true gradient almost surely.

Our implicit gradient is a biased estimator, due to the finite sample term appearing in the denominator.

Finally, our implicit gradient is numerically stable. 
The possible numerical instability can arise from the deminator term $\sum_{\mathbb{z} \in \Epsilon} \mathrm{sm}'(h_\theta(z) + c_\theta)$ being close to zero.
However, one can view this as weighting factors on $\nabla_\theta h_\theta(\mathbb{y})$, similar to the attention mechanism excpet we have $\mathrm{sm}'$ as nonlinearity instead of $\exp$ in attention.
We also didn't observe any numerical instability in our experiments.

Detail usable in the response: writing $h_\theta$ for the pre-sigmoid logit, the implicit derivative of the scalar bias has the form
$$\nabla_\theta \widehat{c} = -\sum_i w_i \nabla_\theta h_\theta(x_i), \qquad w_i \ge 0, \quad \sum_i w_i = 1,$$
(for a general homomorphism-density constraint the weights also include the products of the other edge probabilities), so $\|\nabla_\theta \widehat{c}\| \le \max_i \|\nabla_\theta h_\theta(x_i)\|$: small sigmoid derivatives shrink numerator and denominator together and do not amplify the implicit gradient. Clipping is only needed for the separate forward Newton root solve (already in Appendix D; move this explanation forward).

### Connection between the KL-divergence and the large deviation problem

For $N = n(n-1)/2$, consider the event that $rN$ edges are present in a random graph $G \sim G(n, p)$.
The probability of this event is given by
$$
P(B(N, p) = qN) = \binom{N}{qN} p^{qN} (1-p)^{(1-q)N}.
$$
From Stirling's approximation, we have
$$
\binom{N}{qN} \approx \exp(N h(q) + o(N))
$$
where $h(q) = -q \log q - (1-q) \log (1-q)$.
Therefore, 
$$
  \log P(B(N, p) = qN) \approx N h(q) + Nq \log p + N(1-q) \log (1-p) +o(N) = - N \left(q \log \frac{q}{p} + (1-q) \log \frac{1-q}{1-p} \right) + o(N).
$$

So the exponential cost of an atypical edge fraction is the Bernoulli KL divergence. The graphon large-deviation principle generalises this from a single edge fraction to a full edge-probability profile $W$, whose cost is the integrated KL divergence $h_q(W)$; conditioning on an atypical $H$-density restricts the admissible profiles, the exponential probability is controlled by the minimum of $h_q$ over them, and the conditioned graphs concentrate near the minimising graphons. Add this short explanation before the formal variational statement.

### Too large sample size

$2^{28}$ is only used for final evaluation, while training uses $2^{12}$-$2^{16}$ samples. 
As estimated homomorphism densities are bounded by $[0, 1]$, for any fixed permutation set the estimator is an average of $N$ independent tuple contributions in $[0, 1]$, so Hoeffding's inequality gives
$$\Pr(|\widehat{t} - t| \ge \epsilon) \le 2 e^{-2N\epsilon^2}.$$
At $N = 2^{28}$ the distribution-free 95% absolute-error bound is about $8.3 \times 10^{-5}$. Three caveats to state: this is an upper bound, not a claim that $2^{28}$ is necessary; it is absolute error, so it gives no useful relative-error guarantee when the true motif density is extremely small.

### Comparison to Graphon-INR literatures

Graphon learning is a problem in network analysis, where one aims to find underlying structure given finite graphs, as social networks. 
Specifically, we are given a set of graphs $\{G_i\}_{i=1}^N$ that are assumed to be sampled from a common underlying graphon $W$, and the goal is to estimate $W$ from these samples.
These problems were tested against on application for mixup-like data augmentation in graphon learning, and the synthetic graphons. 
As their main purpose is reconstructing the graphon that is similar to true graphon, they often fails to sharp details on the true graphon, for instance, see Figure 3(b) and Figure 9 in [1].
To apply graphon learning problem to extremal graph theory problem like our problems, one first requires to find the near optimal finite graphs $G$ and then estimate the underlying graphon $W$ from these finite graphs, which requires both hard discrete optimisation and graphon learning.

[1] Scalable Implicit Graphon Learning, Ali Aziz pour, Nicolas Zilberstein, and Santiago Segarra, AISTATS 2025.

On Xia, Mishne, and Wang (2023) specifically: they introduced implicit neural graphon representations for this reconstruction task, using a SIREN with a Gromov-Wasserstein loss, with extensions to graph generation and representation learning. Our task observes no target graphon or graph dataset; we directly optimise homomorphism-density or KL functionals under a density constraint. Contributions specific to our setting: progressive per-layer input encoding for discontinuous extremisers, symmetry-aware Monte Carlo estimators, embedded monotone constraint solver with implicit differentiation. We add the citation and narrow the novelty wording so we do not claim to introduce neural graphon representations.
The promised parameter-matched SIREN control is already covered by the ablation: the plain-MLP variant with sinusoidal activations *is* a parameter-matched SIREN under our objective, solver, and estimator (no separate run needed; quote its number).

### Some theoretical idea when works well or not? 

We don't have clear theoretical idea when it works well or not, but we have some empirical observations.
Often, the problems we study have trivial solutions, for instance, the constant graphon $W \equiv p$ or $W \equiv q$ are the trivial solutions for (P1) and (P2) respectively.
When these trivial solutions are comparable to the optimal solution (the difference of objective is less than 1e-5), then the trained model often converges to the trivial solution. 

What theory does support (usable alongside the above): (i) the empirical scalar constraint has a unique root; (ii) the homomorphism-density estimator is unbiased for a fixed graphon; (iii) the implicit formula is the exact derivative of the empirical constrained problem; (iv) continuous neural graphons approximate step graphons in $L^1$, and $|t(H,W) - t(H,U)| \le e(H) \|W - U\|_1$, so approximation transfers to the objective. None of this gives global convergence of the nonconvex optimisation; state that limitation prominently.
Suitability summary: best for dense-graph problems with one monotone scalar constraint, moderate motif density, and a low-complexity block/geometric optimiser; less suitable for sparse limits, extremely rare motifs, large motifs under tight memory, multiple nonmonotone constraints, or landscapes with many competitive local minima.

### What about wavelet basis?

We tested the four non-neural representation methods, Fourier basis, Haar wavelet basis, Legendre polynomial basis, and Bernstein polynomial basis, parameterising $W(x,y) = \sum_{i,j} C_{ij} \varphi_i(x) \varphi_j(y)$ exactly, with no output nonlinearity (implemented in `short_exps/other_representations.ipynb`; task: $K_3$ minimisation at $p = 7/9$; numbers below are the committed seed-41 run).
- Density optimisation: all four failed to satisfy $W(x, y) \in [0, 1]$ — the clip projection is not representable in a fixed linear basis, so the iterates leave $[0,1]$ and diverge to meaningless values (e.g., $t(K_3, W) \approx -2 \times 10^6$; the runs even pass near the true optimum before instability throws them out).
- Supervised fit to the known optimal solution (closed-form least squares = the global optimum of supervised training): Fourier, Legendre, and Bernstein still violate $W \in [0,1]$ on about 45% of the domain, overshooting the step boundaries by about $\pm 0.3$ (Gibbs phenomenon; Legendre and Bernstein span the same polynomial space, so their fits coincide).
- The Haar wavelet fit *does* stay in $[0, 1]$ (it is a local averaging), but it cannot represent the boundaries, which do not lie on dyadic points, and gives $t(K_3, W) = 0.446430$ — worse than the fixed-grid SBM baseline ($0.435817$) and the optimum $98/225 \approx 0.435556$.
- Conclusion for the response: a wavelet parameterisation still needs an output nonlinearity as in our architecture; sinusoidal features were chosen because they are simple to differentiate and their frequency is controlled directly by $U^{(\ell)}$; discuss wavelet INRs as an important comparison rather than claiming sinusoids are uniquely suitable.
(Careful with wording: "none satisfy the bounds" is too strong — Haar satisfies the bounds but fails on expressiveness.)

### Practical Application

- Some extremal graph theory often helps, as expander graph does. But our model is limited to the dense problems, and cannot be applied to this sparse problem.
- The large deviation analysis is often related to sociological science where...
- The primary intended application is mathematical discovery, and it already has concrete outcomes: the three theorems proved after submission (see the "Three theorems" section below). The large-deviation theorem in particular describes the typical structure of dense Erdős–Rényi graphs conditioned on an upper-tail event.
- Related computational uses we can mention: constrained dense-graph generation, and rare-event importance-sampling proposals. Do not claim downstream graph-ML performance we have not evaluated.

### The P2 error seems too large. 

We use 64-bit floating point numbers for the results, therefore the difference is large enough to be significant. 

More precisely: the reported $h_q$ and constraint values are computed by deterministic numerical integration, not Monte Carlo, so the paired differences contain no sampling error. From Table 6 they are $0.0954, 0.1044, 0.0968$ at $q=0.05$ and $0.0031, 0.0053, 0.0045$ at $q=0.10$, for $r = 0.4, 0.5, 0.6$.
Also usable: the suboptimality claim is witnessed by the exhibited graphon itself — any feasible graphon with strictly smaller $h_q$ shows $W_{\mathrm{LZ}}$ is not optimal, independently of run-to-run variability (variability only measures how reliably the method finds such a graphon).

**Bipodal certification (new; code and reference output in the last cell of `short_exps/sbm_check.ipynb`).** Restricting to bipodal graphons — value $a$ on $[0,t)^2$, $b$ on the mixed blocks, $c$ on $[t,1]^2$ — both $t(K_3,W)$ and $h_q(W)$ are exact closed forms in $(a,b,c,t)$, so (P2) restricted to this family is a 4-dimensional problem with no network, no sampling, no discretisation. Multi-start SLSQP with analytic gradients + a strict feasibility check gives explicit feasible graphons:

| $q$ | $r$ | $h_q(W_{\mathrm{LZ}})$ | $h_q(W_{\mathrm{ours}})$ | $h_q(\text{bipodal})$ | LZ $-$ bip |
|---|---|---|---|---|---|
| 0.05 | 0.4 | 0.556057 | 0.460698 | 0.463083 | 0.092974 |
| 0.05 | 0.5 | 0.830366 | 0.726014 | 0.727151 | 0.103215 |
| 0.05 | 0.6 | 1.144945 | 1.048169 | 1.050275 | 0.094670 |
| 0.10 | 0.4 | 0.311239 | 0.308116 | 0.308803 | 0.002436 |
| 0.10 | 0.5 | 0.510826 | 0.505543 | 0.505990 | 0.004836 |
| 0.10 | 0.6 | 0.750684 | 0.746170 | 0.746713 | 0.003971 |

Strictly below $h_q(W_{\mathrm{LZ}})$ in every cell, so $W_{\mathrm{LZ}}$ is certified suboptimal in all six cells, including the small-gap $q=0.10$ regime, independently of the network and of any numerical error (a witness suffices; global optimality is not needed for the certificate). Verified three ways: exhaustive grid over $(a,c,t)$ with $b$ eliminated via the active constraint ($601 \times 601 \times 599$ points); polished SLSQP; and multi-start searches over 3-block and 4-block step graphons, which give exactly the same optima — so these are the exact optima over step graphons with up to 4 blocks. Sanity check: $h_q(W_{\mathrm{LZ}})$ in the table equals $\mathrm{KL}(r\,\|\,q)$, the replica-symmetric (constant-graphon) value, in every cell.

**IMPORTANT, unresolved before posting:** the Table-6 network values sit slightly *below* the exact bipodal optima in every cell (by $4.5\times10^{-4}$ to $2.4\times10^{-3}$), which no bipodal (or $\le4$-block) graphon can achieve. Via the Lagrange multiplier $\lambda = dh^*/d(r^3)$ ($\approx 4.9, 3.9, 3.3, 3.7, 2.9, 2.4$ for the six cells), the gap corresponds to a $t(K_3)$ deficit of only $1.5\times10^{-4}$–$6.5\times10^{-4}$, i.e. 0.1–0.8% of $r^3$. Most likely the learnt graphons slightly violate the population-level constraint. Check $t(K_3, W_{\mathrm{ours}}) - r^3$ at high precision before posting; a careful reviewer comparing our numbers could spot this. Once confirmed, consider quoting the certified bipodal values as the primary comparison — they are immune to every numerical-error question raised.

### Why does 11.8% suboptimal error happens?

Among 11.8% suboptimal error, 7% was due to converging to local optimum, and 4.8% was due to training and inference instability, resulting either NaN or OOM errors.


### What is power of NN?

For tree-based baselines or fixed-grid SBM, it is generally hard to change the decision boundary, and almost all $\{0, 1\}$ solutions are local optimum that can't be escaped without reset. 
Therefore, these methods strongly depend on the initialisation, and often can't escape the geometry of initialisation solution.
On the other hand, neural network can easily change the decision boundary, and excels to represent the optimal solution by jointly optimising the value of each region and the boundaries.
The idea of parameterising the decision boundary together (second and third figure in Figure 15), fails due to the fact that the optimisation landscape being very sharp, therefore converges to constant solution always.

We also note that all the non-neural baselines were expressive enough to represent the optimal solution.

Therefore, we view the main benefit of neural network is that it can flexibly tune the solution in terms of both value and boundary, while having favorable optimisation landscape.

### No sinusoidal encoding baseline

We repeated the ablation study in our paper, but with no sinusoidal encoding.

- Ours, without sinusoidal encoding: $t(K_3, W) = 0.436118$
- ResNet, without sinusoidal encoding: $t(K_3, W) = 0.436457$
- Constant-scale $s$, without sinusoidal encoding: $t(K_3, W) = 0.436500$
- Regulariser, without sinusoidal encoding: $t(K_3, W) = 0.437376$
- Constant LR (low), without sinusoidal encoding: $t(K_3, W) = 0.442499$
- Constant LR (high), without sinusoidal encoding: $t(K_3, W) = 0.436795$

Interpretation note: every no-sin number here (0.4361–0.4425) is worse than every sin-encoding variant in the paper's ablation table (0.4272–0.4344), so pairing each variant with its no-sin counterpart attributes the gain to the sinusoidal features themselves, not merely to the per-layer injection — this is exactly the disentanglement BFdn and 6KFF asked for. Add the plain-MLP number when available; with sinusoidal activations it doubles as the parameter-matched Xia/SIREN control.

### P2 has no good lower bound?

Up to our knowledge, computational lower bound for problems like P2 is not known.
There are some empirical tests that can be used to check comparable lower bound:
- Using some advanced sampling methods to directly sample from the conditional distribution $G \sim G(n, p) | t(K_3, G) \ge r^3$ and compare the sampled finite graph with the trained model. However, this is not feasible for large $n$ and $r$.
- Under assumption that the optimal solution is bipodal, we can reduce the problem to a 4-dimensional optimisation problem, and use constrained optimisation methods to find the solution. Results are in the "P2 error" section above: the 4-dimensional bipodal optimisation certifies suboptimality of $W_{\mathrm{LZ}}$ in all six cells by explicit feasible constructions with closed-form values.

### How much dependency on the initialisation, frequency schedule, and MC permutations? 

We repeated the $K_3$ density minimisation experiment under best hyperparameter configuration 10 times:
- Mean : $0.435711$
- Gaussian CI (95%): $[0.435705, 0.435718]$.

For the 

### How many error in population level constraint, from the solver?

The constraint solver runs also on the final trained graphon (the reported values re-solve the scalar bias at evaluation), so no training-time batch shift persists in the reported graphon. The right question is the stability of the solved bias under random sampling. Plan: report the distribution of the solved bias and of the resulting constraint value over repeated independent batches at the final graphon, plus the value from a very large reference sample. (The same computation resolves the bipodal-gap issue flagged in the "P2 error" section.)

### Uncertainty estimate on training?

Same as the dependency on init.

### Do you have good construction on C7 and H6?

While the conjecture described in Section E considers specific constructions for $C_7$ (in fact, for all odd cycles), our trained model does not follow this construction. 
This does not imply that the trained model is not optimal, as there can be multiple optimal solutions, and the stated construction is only one of them.
For $H_6$, we only have symbolic construction for the case $p = 4/5$:
$$W(x, y) = \begin{cases} 1 \text{ if } |x-y| \in [0.1, 0.9] \\ 0 \text{ otherwise}. \end{cases}$$
We do not have proof for the optimality of these constructions. 

### Comparison

- Rediscover of known results
  + Figure 1: Rediscover of Razborov's theorem
  + Figure 2: Rediscover of Reiher's theorem
  + Figure 3: Rediscover of Bennet et al.'s result
- Labels to use consistently in the responses (s6Ge asked for this): (i) recovery of a proven optimum (the figures above); (ii) candidate matching an independent lower bound; (iii) numerically competitive candidate, including candidates improving on a reference construction.
- TODO

### LZ is only designed for K3, not C4 or C5

While LZ construction is only designed to prove non-optimality of constant graphon not as optimal solution, it is not limited to $K_3$ but is applicable to any d-regular graphs.
So for $C_4$ and $C_5$ we use $W_{\mathrm{LZ}}$ as the available reference construction, without claiming that improving on it implies near-optimality; restrict the "outperforms Lubetzky–Zhao" headline claim to $K_3$.

### Three theorems proved after submission (with the help of our framework)

1. **Odd cycles.** $t(C_m, W) \ge p^m - p(1-p)^{m-1}$ for every graphon $W$ of edge density $p$ and every odd $m \ge 3$; for $m = 3$ this is Goodman's inequality, so the theorem extends Goodman to all odd cycles. Nontrivial for $p > 1/2$; sharp at every balanced complete $k$-partite graphon, so those are minimisers at $p = 1 - 1/k$. It is a lower bound valid for every graphon, NOT a classification of the exact minimiser at every density — keep "candidate" language for the displayed $C_7$ graphons and for $H_6$. Journal manuscript in preparation; the proof is analytic apart from two exact-rational univariate Bernstein positivity certificates for $m = 9$.
2. **Chordal graphs.** For every chordal $H$ (no induced cycle of length greater than 3) whose maximal cliques all have the same size $r \ge 3$, the minimiser of (P1) at $p = 1 - 1/k$ is the balanced complete $k$-partite graphon, for every integer $k \ge r$. This settles 17 cases of the 175-graph study (page 8) that were previously unproven. (Note: $k$-partite, not $r$-partite.)
3. **Large deviations.** For every $d$-regular $H$ with $d \ge 2$ and every phase-boundary point with $r \ne (d-1)/d$, there is a nontrivial open neighbourhood in which, on the symmetry-breaking side, the optimiser is unique up to relabelling and bipodal; its block parameters and optimal value are analytic in $(p, r)$, and the conditioned dense random graphs concentrate in cut distance around this bipodal structure. Partial answer to Chatterjee's first open problem (explicit nonconstant solutions or provable qualitative properties). The result is local — it does not certify Table 6 entries.

Disclosure (decided: include in reviewer-facing text): the theorems were proved with the help of ChatGPT 5.5 and formalised in Lean 4 with the help of Claude Opus 4.8. Lean status, stated precisely: the odd-cycle and chordal theorems are formalised in full with no conditional assumptions; the formalisation of the large-deviation theorem takes some established results from the literature and parts of graphon theory as axioms. Responses may not contain links — offer an anonymised link to the formalised proofs through the AC during the discussion phase.

Framing to keep: the intended workflow is candidate discovery followed by independent mathematics; the theorems do not retroactively certify every numerical candidate.

### Computational cost and complexity

- Dominant neural forward/backward cost $\approx O(N v(H)^2 L d^2)$ (width $d$, depth $L$, batch $N$, cached evaluations on at most $\binom{v(H)}{2}$ unordered pairs per tuple), plus $O(N |\mathcal{S}| e(H))$ for motif-product aggregation. Activation memory $\approx O(N v(H)^2 L d)$. Monte Carlo absolute error scales as $N^{-1/2}$, so halving it needs about $4\times$ samples.
- All experiments on a single RTX A5000 (per the paper — stick to A5000, not 3090). A full 20000-epoch run including evaluation: about 16 minutes for $K_3$, about 1 hour for $C_5$, up to a few hours for the Petersen graph. Batch size is chosen to fill GPU memory (larger batches reduce estimator variance at fixed wall time); gradient accumulation achieves the same batch under smaller memory.
- Pushback available for the "cost is very high" weakness: the total cost is modest by current standards — every experiment fits on one workstation GPU.
- Microbenchmark plan (cheap, answers "how does runtime scale with motif size, MC sample size, and width"): measure seconds/iteration (average ~50 iterations after ~10 warm-up, with `torch.cuda.synchronize`) and peak memory (`torch.cuda.max_memory_allocated`) varying one axis at a time from the default config: motif $\in \{K_3, C_5, C_7, H_6, \text{Petersen}\}$; $N \in \{2^{12}, 2^{14}, 2^{16}\}$; $d \in \{64, 128, 256\}$. Check the measured scaling against the formula.

### Why progressive sinusoidal encoding (architecture justification)

- A step boundary requires increasingly high spatial frequencies to approximate. Early low-scale features provide the coarse block geometry; later high-scale features provide short paths that refine boundaries without forcing every preceding layer to preserve high-frequency information. The per-layer injection and the increasing frequency schedule play different roles; the no-sin paired ablation above separates the sinusoid from the injection, and the constant-scale control separately tests the multiscale schedule.
- Initialisation (6KFF, line 165): the $d^{-1/2}$ initialisation of residual matrices controls activation growth with fan-in, while the range of each row of $U^{(\ell)}$ directly controls the initialised spatial frequency — increasing $s(\ell)$ gives later layers progressively finer scales without increasing hidden-state magnitude.
- Promised in the draft: a boundary-refinement visualisation.

### Running / planned robustness protocols (for the sensitivity answers)

- Learning-rate schedule robustness at a fixed budget of 20000 epochs: cosine-annealing cycles $20000\times1$, $10000\times2$, $5000\times4$, $2500\times8$, $1000\times20$.
- MC-permutation study on $C_5$: identity only, the two cyclic permutations $(0\,1\,2\,3\,4)$ and $(0\,2\,4\,1\,3)$, and the full permutation set. All unbiased — the choice affects only variance and cost; for cycles the main estimator averages all coset representatives, so the choice of representatives does not change the symmetrised estimator.
- Same repetition protocol on the open instances to follow ($C_7$ at $p=5/8$, $H_6$, triangle P2 at $q=0.10$) — these are the distributions the reviewers weighted most.
- If s6Ge's "frequency schedule" means the encoding scale schedule: compare $s(\ell) = \ell$ vs $s(\ell) = 2^{\ell-1}$ under the same protocol (the paper says $2^{\ell-1}$ was used in pilot runs, so the logs may already cover this).

### Internal notes (do not volunteer in responses)

- The internal $C_7, p = 2/3$ reference value has a typo: the balanced complete tripartite value is $14/243 \approx 0.05761317$, not $0.05763169$. Only relevant if a corrected table is discussed.
- Guideline constraints: 10000 characters per review; no links (code only via anonymised link to the AC on request); no PDF revisions; keep anonymity. The BFdn response is the longest — trim there first (e.g., theorem display math to inline).
- Phase 2 (author/reviewer discussion) runs to Aug 3: results that miss the initial response can be posted as follow-ups; engage early.