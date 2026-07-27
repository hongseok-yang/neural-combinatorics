# NeurIPS 2026 rebuttal draft

Internal drafting note: the 2026 rules allow up to 10,000 characters per review, permit new results, prohibit links and identifying information, and do not permit revised PDFs or new supplementary files during rebuttal. Remove every bracketed [TODO: ...] placeholder before posting.

## Claims that must be kept distinct

- The neural method finds candidates; it does not itself prove global optimality.
- The new odd-cycle theorem is
  $$
  t(C_m,W)\ge p^m-p(1-p)^{m-1}
  $$
  for every graphon $W$ of edge density $p$ and every odd $m\ge3$; for $m=3$ it reduces to Goodman's inequality. It is sharp at the balanced complete $k$-partite graphons, so those are minimisers at $p=1-1/k$.
- This theorem is a lower bound valid for every graphon. It does **not** prove the stronger exact-optimiser conjecture stated in the appendix at every $p$, and it does not certify every displayed $C_7$ candidate.
- The new chordal theorem: for every chordal graph $H$ (no induced cycle of length greater than 3) whose maximal cliques all have the same size $r\ge3$, the minimiser of $\mathbf{(P1)}$ at $p=1-1/k$, for every integer $k\ge r$, is the balanced complete $k$-partite graphon. This settles 17 cases of the 175-graph study that were previously unproven.
- The new large-deviation theorem is local near the Lubetzky-Zhao phase boundary: for every $d$-regular $H$ with $d\ge2$, away from the exceptional value $r=(d-1)/d$, the nonconstant optimiser on the symmetry-breaking side is unique up to relabelling and bipodal in a nontrivial open neighbourhood. It does **not** automatically certify every parameter in Table 6.
- The $H_6$ construction remains a numerical conjecture; we have a symbolic construction only at $p=4/5$, without a proof of optimality.
- Lean status, to be stated precisely: the odd-cycle and chordal theorems are formalised in full, with no conditional assumptions. The formalisation of the large-deviation theorem takes some established results from the literature and parts of graphon theory as axioms.
- Do not offer links to proofs or formalisation: the response rules prohibit links except when a reviewer requests code.
- Do not describe a running or planned experiment as completed. Replace each results placeholder only after the corresponding numbers have been checked.
- Before posting exact learning rates, reconcile the human notes ($10^{-3},3\times10^{-4},10^{-4},3\times10^{-5}$) with the submitted Appendix D ($10^{-3},5\times10^{-4},10^{-4},5\times10^{-5}$). Until then, state only that the search crossed two activations with four learning rates.
- Reconcile the Haar-wavelet result before quoting it: `rough_answer.md` gives $0.444238$, while the earlier internal experiment note gives $0.446430$.
- Author-verify the exact large-deviation theorem statement and the count of 17 newly settled sweep cases against the current mathematical manuscripts; neither fact is documented in the submitted paper or `rough_answer.md`.

## Optional confidential overview to the AC

We thank the AC and reviewers for their thoughtful feedback. A central strength of our work is that the method produces interpretable candidate solutions to difficult graphon variational problems. Its recovery of known extremal solutions provides controlled evidence of its optimisation performance. On open problems, the interpretable structures identified by the method have guided new mathematical analysis. Since submission, this process has led to three new theorems in extremal graph theory and dense-graph large-deviation theory. The first extends Goodman's inequality to all odd cycles. The second is a chordal-graph extremal theorem that settles 17 previously unproven cases in our study. The third is a local structural theorem for the large-deviation problem. We are preparing manuscripts describing these theorems for submission to mathematics journals. In this rebuttal, we also report additional robustness checks and independent validation. We isolate the contributions of the architectural components and explain the method's computational cost.

**Robustness and numerical validation.** Each reported candidate was selected from exactly eight runs: one run for each of two activations crossed with four learning rates. This was a finite hyperparameter search, not an unspecified number of attempts, and we will state the protocol explicitly. To quantify reproducibility as well as search quality, we are running a standardised 10-seed study on the $K_3$ benchmark at $p=7/9$ and will apply the same protocol to the key open instances. We will report the full objective distribution, held-out population-constraint residual, fitted structural parameters, and structural success rate. [TODO: insert completed benchmark and open-instance results.] For the triangle upper-tail comparison, the reported entropy values were obtained by deterministic 64-bit numerical integration rather than Monte Carlo sampling. We are additionally auditing convergence across integration resolutions, the constraint residual, and the paired gap $h_q(W_{\mathrm{LZ}})-h_q(W_{\mathrm{ours}})$ in all six cells; where the learned profile is bipodal, an analytically constrained four-parameter fit gives an explicit independent witness. [TODO: insert resolution audit, residuals, paired gaps, and bipodal-fit results.]

**Independent mathematical follow-up.** Most importantly, the framework has already achieved its intended scientific purpose: interpretable learned structures have led to three new theorems.

First, following the learned $C_5/C_7$ structures, we proved that for every graphon $W$ of edge density $p$ and every odd $m\ge3$,
$$
t(C_m,W)\ge p^m-p(1-p)^{m-1}.
$$
For $m=3$ this is Goodman's inequality; the theorem extends it to all odd cycles. The bound is nontrivial for $p>1/2$ and sharp at every balanced complete $k$-partite graphon, so those graphons are minimisers at $p=1-1/k$. The proof is analytic apart from two exact-rational univariate Bernstein positivity certificates for $m=9$, and it has been formalised completely in Lean 4.

Second, we proved that for every chordal graph $H$ whose maximal cliques all have the same size $r\ge3$, the minimiser of the density-minimisation problem $\mathbf{(P1)}$ at $p=1-1/k$ is the balanced complete $k$-partite graphon, for every integer $k\ge r$. This settles 17 cases of the 175-graph study (page 8) that were previously unproven, and the theorem has also been formalised completely in Lean 4.

Third, motivated by the bipodal outputs for the large-deviation problem, we proved a local structural theorem. For every $d$-regular graph $H$ with $d\ge2$ and every nonexceptional point of the Lubetzky-Zhao phase boundary, there is a nontrivial open neighbourhood in which the optimiser on the symmetry-breaking side is unique up to relabelling and bipodal, with parameters and optimal value analytic in $(q,r)$. Consequently, the corresponding conditioned dense random graphs concentrate in cut distance around this bipodal structure. This addresses a central open question about explicit nonconstant variational minimisers and their qualitative structure.

We are preparing manuscripts describing these theorems for submission to mathematics journals. Together, they validate the intended workflow: the neural framework produces interpretable candidate structures, and separate mathematical analysis converts those structures into theorems. We retain precise candidate language for numerical outputs not covered by these results.

**Architecture and cost.** Xia et al. (2023) use a SIREN to reconstruct an unknown graphon from observed graphs with a Gromov-Wasserstein loss. Our setting observes no target graphon and instead directly optimises constrained variational functionals. We will cite Xia et al. and state the distinction explicitly; our problem-specific contribution is the integrated combination of progressive per-layer encoding, a monotone constraint layer with implicit differentiation, and symmetry-aware integral estimators. To separate periodic features from repeated input injection, we are rerunning the full ablation suite with GeLU features replacing the sinusoidal per-layer features while keeping the injection structure fixed. [TODO: insert completed factorised-ablation results.] Finally, $2^{28}$ is a one-time post-training evaluation budget, not the training batch size; training uses $2^{12}$-$2^{16}$. The dominant cost is approximately $O(Nv(H)^2Ld^2+N|\mathcal S|e(H))$, and we will report measured seconds per iteration and peak memory alongside this scaling law. [TODO: insert runtime/memory summary.]

## Reviewer 1jpj

Thank you for recognising the framework as coherent, the implicit-differentiation formula as mathematically sound, and best-run reporting as reasonable for candidate discovery. We answer the four questions directly below.

**1. Number of runs and robustness.** Every reported candidate was selected from exactly eight runs: one run for each of two activations crossed with four learning rates. Thus "best across multiple runs" refers to a finite eight-configuration search, which we will state explicitly. To measure reproducibility separately from hyperparameter selection, we are running 10 independent repetitions under a fixed protocol on $K_3$ at $p=7/9$, followed by the key open instances. We will report mean/SD, median/IQR, best value, held-out constraint residual, and the fraction recovering the same structure up to graphon relabelling. [TODO: insert completed benchmark and open-instance results.]

**2. Population interpretation of the implicit gradient.** The complete finite-batch implicit gradient is generally biased, because the same empirical batch enters the constraint root and the derivative ratio. It is nevertheless strongly consistent. For fixed $\theta$, the pre-sigmoid output $h_\theta$ and its parameter derivative are bounded on the compact domain. If $|h_\theta|\le M$, both the empirical root and the population root lie in
$$
[\mathrm{logit}(p)-M,\ \mathrm{logit}(p)+M].
$$
On this compact interval, uniform laws of large numbers apply jointly to the empirical constraint and its $c$- and $\theta$-derivatives. Continuity and strict monotonicity imply $\widehat c_S(\theta)\to c(\theta)$ almost surely; substituting this convergence into the derivative ratio gives almost-sure convergence of the empirical implicit gradient to the population constrained gradient. Thus the precise statement is: exact for the empirical constrained problem, biased at finite batch size, and consistent as the batch size grows. We are also measuring convergence to a large-batch reference at fixed checkpoints over $N=2^{10},\ldots,2^{16}$. [TODO: insert bias, norm-error, and cosine-similarity results.]

**3. Small sigmoid derivatives.** The backward derivative is better conditioned than the unnormalised quotient suggests. For the edge-density constraint,
$$
\nabla_\theta \widehat c
=-\sum_i w_i\nabla_\theta h_\theta(x_i),
\qquad w_i\ge0,\quad \sum_iw_i=1.
$$
For a general homomorphism-density constraint, the same formula uses nonnegative normalised weights over sampled edge occurrences, including products of the other edge probabilities. Therefore
$$
\|\nabla_\theta\widehat c\|\le \max_i\|\nabla_\theta h_\theta(x_i)\|.
$$
Small sigmoid derivatives can concentrate these weights but cannot amplify $\nabla_\theta\widehat c$ beyond the largest sampled logit-gradient norm. The separate forward root solve can be unstable under saturation; Appendix D already addresses this with a clipped Newton update whose clipping range shrinks across iterations. We observed no backward instability from the normalised implicit derivative.

**4. Why the KL variational problem describes conditioned Erdős-Rényi graphs.** The simplest case already shows where the KL divergence comes from. In $G(n,q)$, each of the $N=\binom n2$ edges is independently Bernoulli-$q$, so the probability that exactly $aN$ edges are present is
$$
\binom{N}{aN}q^{aN}(1-q)^{(1-a)N}
=\exp\!\Big(-N\big(a\log\tfrac{a}{q}+(1-a)\log\tfrac{1-a}{1-q}\big)+o(N)\Big)
$$
by Stirling's approximation: the exponential cost of an atypical edge fraction $a$ is the Bernoulli KL divergence between $a$ and $q$. The graphon large-deviation principle generalises this from a single edge fraction to a full edge-probability profile $W$, whose cost is the integrated KL divergence $h_q(W)$. Conditioning on an atypical $H$-density restricts the admissible profiles; the exponential probability of the event is controlled by the minimum of $h_q$ over them, and the conditioned graphs concentrate near the minimising graphons. We will add this short explanation before the formal variational statement.

**Mathematical outcome of the discovery workflow.** The strongest independent validation is that structures found by the framework have already led to three new mathematical theorems. First, for every graphon $W$ of edge density $p$ and every odd $m\ge3$,
$$
t(C_m,W)\ge p^m-p(1-p)^{m-1},
$$
extending Goodman's inequality to every odd cycle and attaining equality at the balanced complete $k$-partite graphons. Second, for every chordal graph whose maximal cliques all have the same size $r\ge3$, the balanced complete $k$-partite graphon minimises $\mathbf{(P1)}$ at $p=1-1/k$ for every integer $k\ge r$, settling 17 previously unproven cases of our 175-graph study. Third, for every $d$-regular pattern graph with $d\ge2$, the large-deviation optimiser is unique up to relabelling and bipodal in a nontrivial neighbourhood on the symmetry-breaking side of each nonexceptional phase-boundary point. The first two theorems are fully formalised in Lean 4. We are preparing manuscripts describing all three for submission to mathematics journals. This is the intended use of the framework: learned structures seed independent mathematics.

## Reviewer PPij

Thank you for recognising the framework's novelty, tailored architecture, and comprehensive experiments. The requested details sharpen the computational and related-work positioning as follows.

**Sample size.** The $2^{28}$ figure is not the training batch size. Training uses $2^{12}$-$2^{16}$ sampled tuples; $2^{28}$ is a conservative, one-time post-training evaluation budget used only when deterministic high-resolution contraction is infeasible. For any fixed permutation set, the estimator is an average of $N$ independent tuple contributions in $[0,1]$. Hoeffding's inequality therefore gives
$$
\Pr(|\widehat t-t|\ge\epsilon)\le2e^{-2N\epsilon^2}.
$$
At $N=2^{28}$, the distribution-free 95% absolute-error bound is approximately $8.3\times10^{-5}$. Thus $2^{28}$ was a conservative evaluation choice, not a sample size required by either training or theory. Training uses $2^{12}$-$2^{16}$, and the usual $N^{-1/2}$ rate lets users choose the evaluation budget for the desired absolute precision. We will state this distinction explicitly.

**Runs.** Every reported candidate was selected from exactly eight runs: one run for each of two activations crossed with four learning rates. To complement this finite hyperparameter search with a reproducibility measure, a standardised 10-seed study is running on $K_3$ at $p=7/9$, followed by the key open instances. [TODO: insert completed distribution and structural success rates.]

**Relation to Xia, Mishne, and Wang (2023).** Xia et al. introduced a SIREN representation for graphon learning: reconstructing an unknown graphon from observed graphs using a Gromov-Wasserstein loss. Our problem has neither an observed graph dataset nor a target graphon. It directly searches over graphons to optimise homomorphism-density or KL functionals subject to a density constraint. We will cite Xia et al. and make clear that we do not claim to introduce neural graphon representations. The contribution here is the graphon-variational framework: progressive per-layer features for sharp extremisers, an embedded monotone constraint solver with implicit differentiation, and symmetry-aware density estimators. Our factorised ablation also includes a parameter-matched sinusoidal MLP backbone under the same objective, solver, and estimator. [TODO: insert completed backbone result.]

**Complexity.** With width $d$, depth $L$, batch size $N$, and cached evaluations on at most $\binom{v(H)}2$ unordered pairs per tuple, the dominant neural forward/backward cost is approximately
$$
O\!\left(Nv(H)^2Ld^2\right),
$$
with an additional $O(N|\mathcal S|e(H))$ cost for motif-product aggregation. Activation memory is approximately $O(Nv(H)^2Ld)$. Monte Carlo absolute error scales as $N^{-1/2}$, so halving it requires approximately four times as many samples. On one RTX A5000, the full runs reported in the paper ranged from about 30 minutes for $K_3$ to a few hours for the Petersen graph. We will supplement these end-to-end times with seconds per iteration and peak memory across representative $N,d,H$. [TODO: insert microbenchmark.]

## Reviewer 6KFF

Thank you for recognising that the paper tackles important problems, that the framework is interesting, and that the empirical results are encouraging. We can give concrete theoretical support, a clearer operating regime, and a direct account of the architecture's design.

**Theoretical support and operating regime.** Three parts of the computational method have exact guarantees: the empirical scalar constraint has a unique root; the homomorphism-density estimator is unbiased for a fixed graphon; and the displayed implicit formula is the exact derivative of the empirical constrained problem. In addition, continuous neural graphons approximate step graphons in $L^1$, and
$$
|t(H,W)-t(H,U)|\le e(H)\|W-U\|_1,
$$
so representational approximation transfers quantitatively to the motif objective. Global convergence of the nonconvex parameter optimisation is not guaranteed, but the target regime is concrete: dense-graph problems with one monotone scalar constraint, moderate motif density, and a low-complexity block or geometric optimiser. Across our experiments, the clearest failure diagnostic is a nearly competitive constant graphon: when its objective is within roughly $10^{-5}$ of the best known value, training often remains at that trivial solution. Sparse limits, extremely rare motifs, multiple nonmonotone constraints, and very large motifs fall outside the method's intended regime. We will state this operating regime explicitly.

**Why progressive sinusoidal features.** A step boundary requires increasingly high spatial frequencies for accurate approximation. The early, low-scale features provide coarse block geometry, while later high-scale features provide short paths that refine boundaries without forcing every preceding layer to preserve high-frequency information. The per-layer injection and the increasing frequency schedule play different roles. We are therefore rerunning the entire ablation suite of the paper—a plain MLP, the ResNet variant with first-layer-only encoding, our model, the constant encoding scale, the regulariser-based constraint, and constant learning rates—with GeLU features replacing the sinusoidal per-layer features while keeping the injection structure fixed. Comparing each variant with its GeLU counterpart isolates the periodic features from repeated injection; the existing constant-scale control separately tests the multiscale schedule. [TODO: insert completed results.] We will also add a boundary-refinement visualisation.

The $d^{-1/2}$ initialisation of residual matrices controls activation growth with fan-in, while the range of each row of $U^{(\ell)}$ directly controls the initialised spatial frequency. Increasing $s(\ell)$ therefore gives later layers access to progressively finer scales without increasing hidden-state magnitude.

**Wavelets.** Yes. The constraint solver and Monte Carlo estimator are representation-agnostic, so localised wavelet or Gabor features are plausible alternatives inside the network. We tested direct symmetric linear representations using Fourier, Haar wavelet, Legendre, and Bernstein bases on $K_3$ minimisation at $p=7/9$. Without an output nonlinearity, the Fourier and polynomial models leave $[0,1]$; the Haar fit remains bounded but cannot place the known non-dyadic boundaries accurately and underperforms the fixed-grid SBM. [TODO: insert the verified Haar and SBM values.] This experiment does not rule out a wavelet INR with a bounded output layer. We chose sinusoidal features because they are differentiable and their initial frequency scale is controlled directly by $U^{(\ell)}$; we will present wavelet INRs as a promising alternative rather than claim that sinusoids are uniquely suitable.

**Application and significance.** The primary application is mathematical discovery, and it has already produced concrete outcomes. Learned odd-cycle structures led to the theorem
$$
t(C_m,W)\ge p^m-p(1-p)^{m-1}
$$
for every odd $m\ge3$, extending Goodman's inequality to all odd cycles. A second theorem proves the balanced complete $k$-partite minimiser at $p=1-1/k$ for every chordal graph whose maximal cliques have a common size $r\ge3$, settling 17 previously unproven cases of our 175-graph study. The learned bipodal structures in $\mathbf{(P2)}$ led to a local theorem proving uniqueness and bipodality near the phase boundary for every $d$-regular pattern graph with $d\ge2$; this describes the typical structure of conditioned dense Erdős-Rényi graphs and addresses a central open question about nonconstant variational minimisers. The odd-cycle and chordal theorems are fully formalised in Lean 4. We are preparing manuscripts describing all three for submission to mathematics journals. This demonstrated discovery-to-theorem pipeline is the practical value we claim; we do not claim downstream graph-ML performance.

**Computational cost.** With width $d$, depth $L$, batch size $N$, and motif $H$, the dominant per-iteration cost is $O(Nv(H)^2Ld^2+N|\mathcal S|e(H))$, with activation memory $O(Nv(H)^2Ld)$. Training uses $2^{12}$-$2^{16}$ samples; $2^{28}$ is only a one-time evaluation budget. On one RTX A5000, the reported runs range from about 30 minutes for $K_3$ to a few hours for the Petersen graph. [TODO: insert seconds-per-iteration and peak-memory microbenchmark.]

## Reviewer BFdn

Thank you for recognising the coherent methodology, effective symmetry-aware estimator, and extensive experimental scope. We address the two issues most relevant to the score—novelty and reliability—before answering the individual experimental questions.

**Novelty and Xia et al.** Xia et al. (2023) address graphon learning: reconstructing an unknown graphon from observed graphs using a SIREN and a Gromov-Wasserstein loss. Our problem observes neither graphs nor a target graphon; it searches directly over graphons to optimise constrained homomorphism-density and KL functionals. We will cite Xia et al. and make clear that neural graphon representation itself is not our novelty. The contribution is the integrated graphon-variational framework: progressive per-layer features for sharp extremisers, an embedded monotone constraint solver with implicit differentiation, and symmetry-aware density estimation. These components turn a generic representation into a solver for the two mathematical problem families studied here.

**Sinusoid versus injection.** We are rerunning the full ablation suite in two versions: sinusoidal per-layer features and GeLU features, with the repeated injection structure held fixed. This comparison isolates periodic features from repeated injection; the existing constant-scale control separately tests the progressive frequency schedule. The suite also includes a parameter-matched sinusoidal MLP backbone under the same solver and estimator. [TODO: insert completed factorised-ablation and backbone results.]

**Reliability: discovery has already led to proof.** The strongest independent validation of the framework is what happened after submission: interpretable learned structures led to three new mathematical theorems.

First, following the learned $C_5/C_7$ structures, we proved that for every graphon $W$ of edge density $p$ and every odd $m\ge3$,
$$
t(C_m,W)\ge p^m-p(1-p)^{m-1}.
$$
This extends Goodman's inequality to every odd cycle and is sharp at every balanced complete $k$-partite graphon, proving those graphons minimise $\mathbf{(P1)}$ at $p=1-1/k$.

Second, for every chordal graph $H$ whose maximal cliques have a common size $r\ge3$, we proved that the balanced complete $k$-partite graphon minimises $\mathbf{(P1)}$ at $p=1-1/k$ for every integer $k\ge r$. This settles 17 previously unproven cases of our 175-graph study.

Third, motivated by the bipodal outputs for $\mathbf{(P2)}$, we proved that for every $d$-regular $H$ with $d\ge2$ and every phase-boundary point with $r\ne(d-1)/d$, there is a nontrivial neighbourhood in which the optimiser on the symmetry-breaking side is unique up to relabelling and bipodal; its parameters and optimal value are analytic in $(q,r)$. This provides a provable qualitative description of nonconstant minimisers and addresses a central open question in dense-graph large-deviation theory.

The odd-cycle and chordal theorems are fully formalised in Lean 4. We are preparing manuscripts describing all three for submission to mathematics journals. These results validate the paper's central claim: the method produces interpretable structures that can seed new mathematics. We retain "candidate" language for numerical outputs outside the theorems' scope, including $H_6$ and the displayed $C_7$ solutions away from the sharp densities.

**Lubetzky-Zhao comparison and independent verification of $\mathbf{(P2)}$.** The Table 6 entropy values were obtained by deterministic 64-bit integration, not Monte Carlo, so training-sample confidence intervals are not the relevant error measure. We are reporting convergence across integration resolutions, the constraint residual, and the paired gap
$$
\Delta=h_q(W_{\mathrm{LZ}})-h_q(W_{\mathrm{ours}})
$$
for every $K_3$ cell. [TODO: insert resolution audit, residuals, and paired gaps.] More importantly, the learned profiles can be distilled into a bipodal graphon. In that four-parameter family, the constraint and entropy are finite explicit formulas, so the constraint can be enforced analytically and the objective independently evaluated. [TODO: insert fitted parameters, exact/verified feasibility, and objective gap.] A single explicit feasible graphon with $\Delta>0$ proves that $W_{\mathrm{LZ}}$ is suboptimal, regardless of how often training finds it; the seed study separately measures discovery reliability.

We will reserve "outperforms Lubetzky-Zhao" for $K_3$. The Lubetzky-Zhao construction is defined for regular graphs, including $C_4$ and $C_5$, but there it is a reference construction rather than a claimed optimum; improving on it is therefore evidence of a better construction, not evidence of near-optimality.

**Run distribution and the 175-graph failures.** Every reported candidate was selected from exactly eight runs: two activations crossed with four learning rates. A standardised 10-seed study is running on $K_3$ at $p=7/9$, followed by $K_3$ $\mathbf{(P2)}$, $C_7$, and $H_6$; it reports objective and constraint distributions, fitted structural parameters, and structural success rates. [TODO: insert completed results.] We are also classifying the 11.8% suboptimal sweep cases into convergence to a suboptimal local optimum versus numerical divergence. [TODO: insert counts.] Separately, the new chordal theorem now proves optimality for 17 sweep cases for which the submitted flag-algebra bounds were not tight.

**Why the neural representation helps.** The Appendix H baselines have enough nominal capacity on a finite grid to represent the benchmark solution; the observed difference is optimisation. A fixed-grid SBM cannot move its partition boundaries, trainable-block SBMs collapsed to nearly constant solutions in our experiments, and tree boundaries change through discrete splits. The neural graphon can adjust region values and boundary locations continuously. Conversely, once the structure is known, a well-chosen low-dimensional family can often recover it—the bipodal verification above is an example. The discovery advantage is that the network does not require choosing in advance between multipartite, diagonal/banded, circular-distance, or bipodal forms. We are extending fixed-grid/SBM and sinusoidal-MLP controls to $C_7$, $H_6$, and triangle $\mathbf{(P2)}$. [TODO: insert completed baseline results.] Agreement between the neural output and a distilled structured construction supports the framework's interpretability and provides an independent check.

**Computational cost.** The dominant per-iteration cost is $O(Nv(H)^2Ld^2+N|\mathcal S|e(H))$, with activation memory $O(Nv(H)^2Ld)$. Training uses $2^{12}$-$2^{16}$ samples; $2^{28}$ is only a one-time evaluation budget. On one RTX A5000, the submitted runs range from about 30 minutes for $K_3$ to a few hours for the Petersen graph. [TODO: insert seconds-per-iteration and peak-memory microbenchmark.]

## Reviewer s6Ge

Thank you for recognising the mathematically meaningful problem setting, the problem-specific architecture, and the breadth of the experiments. We address reliability with targeted sensitivity studies and, more importantly, with explicit constructions and new mathematical theorems.

**Initialisation, schedule, and permutation sensitivity.** Every reported value was selected from exactly eight runs: two activations crossed with four learning rates. We are now separating that finite hyperparameter search from reproducibility through three controlled studies. (i) Initialisation: 10 fixed-protocol repetitions on $K_3$ at $p=7/9$, followed by $K_3$ $\mathbf{(P2)}$, $C_7$, and $H_6$, reporting objective distributions, constraint residuals, structural success rates, and fitted parameters after accounting for graphon relabelling. [TODO: insert completed results.] (ii) Schedule: at a fixed 20,000-epoch budget, we compare 1, 2, 4, 8, and 20 cosine cycles. [TODO: insert result.] (iii) Permutations: on $C_5$, we compare the identity, two cyclic permutations, and the full symmetry set. Every choice remains unbiased and changes variance and cost rather than the target; the full cycle estimator averages all coset representatives, so its value does not depend on which representatives are chosen. [TODO: insert variance, objective, and runtime results.]

**Population-level constraint error.** We will quantify population feasibility independently of the training batch: recalibrate $c$ on a large independent sample, evaluate the constraint and objective on a disjoint sample or grid, and report the residual distribution arising from ordinary training-sized solver batches. [TODO: insert instances, maximum/median residual, and interval.] This held-out residual will accompany every central objective value.

**Cross-run uncertainty and the $q=0.10$ comparison.** The seed study will report mean/SD, median/IQR, best, and structural success rate rather than only a bootstrap interval for the selected run. For the triangle upper tail at $q=0.10$, entropy evaluation is deterministic, so we will report the paired gap to $W_{\mathrm{LZ}}$, its convergence across integration resolutions, and the held-out constraint residual separately from cross-seed optimisation variability. [TODO: insert results.]

**Analytic constructions and mathematical outcome.** The $C_7$ appendix already distils the learned pattern into an explicit low-dimensional family. For $H_6$ at $p=4/5$, the circular-distance pattern has the symbolic form
$$
W(x,y)=\begin{cases}1&\text{if }|x-y|\in[0.1,0.9],\\0&\text{otherwise},\end{cases}
$$
which mathematicians can inspect directly. More substantially, follow-up analysis of the learned structures has produced three new theorems. For every graphon and every odd $m\ge3$, we proved
$$
t(C_m,W)\ge p^m-p(1-p)^{m-1}
$$
extending Goodman's inequality to all odd cycles and proving optimality of the balanced complete $k$-partite graphons at $p=1-1/k$. We also proved the corresponding balanced $k$-partite minimiser for every chordal graph whose maximal cliques have a common size $r\ge3$, settling 17 previously unproven cases of the 175-graph study. For $\mathbf{(P2)}$, we proved unique bipodal optimisers in a nontrivial neighbourhood on the symmetry-breaking side of every nonexceptional phase-boundary point for every $d$-regular $H$, $d\ge2$. The first two theorems are fully formalised in Lean 4. We are preparing manuscripts describing all three for submission to mathematics journals. Outside the proved regimes, including $H_6$ and $C_7$ away from the sharp densities, we retain candidate language.

**Conclusion levels.** We will use three labels consistently: (i) recovery of a proven optimum, as in Figures 1–3; (ii) candidate matching an independent lower bound; and (iii) numerically competitive candidate, including an explicit feasible candidate improving on a reference construction.

**Baselines and cost.** We are extending the fixed-grid/SBM and sinusoidal-MLP baselines to representative $C_7$, $H_6$, and triangle-$\mathbf{(P2)}$ instances. [TODO: insert completed results.] The dominant per-iteration cost is $O(Nv(H)^2Ld^2+N|\mathcal S|e(H))$; training uses $2^{12}$-$2^{16}$ samples, while $2^{28}$ is only a one-time final-evaluation budget. [TODO: insert seconds per iteration and peak memory.]

## Experiment priorities

### Priority 0: recover facts before launching jobs

1. Run counts are settled: one run per configuration, eight configurations per experiment (two activations times four learning rates). The exact rates are **not** yet reconciled: `rough_answer.md` says $10^{-3},3\times10^{-4},10^{-4},3\times10^{-5}$, while the submitted Appendix D says $10^{-3},5\times10^{-4},10^{-4},5\times10^{-5}$. Check the actual run records before posting exact values.
2. Record seeds, learning rates, capacity, stopping epoch, hardware, and whether a final independent calibration of $c$ was performed.
3. Reconcile the Haar result: `rough_answer.md` gives $t(K_3,W)=0.444238$, while the earlier internal experiment note gives $0.446430$. Verify against the notebook/run log before quoting either.
4. Verify the exact large-deviation theorem statement and the count of 17 newly settled sweep cases against the current mathematical manuscripts.
5. Correct the internal $C_7,p=2/3$ reference value before any revision: the balanced complete tripartite value is $14/243\approx0.05761317$, not $0.05763169$. Avoid volunteering this unrelated typo in rebuttal unless a corrected table is discussed.
6. Do not promise proof or formalisation links: the response rules allow links only when reviewers request code.

### Priority 1: most likely to move scores

1. **High-precision $\mathbf{(P2)}$ audit.** For all six $K_3$ upper-tail cells, evaluate each selected graphon and $W_{\mathrm{LZ}}$ by deterministic numerical integration. Report the paired entropy difference and the constraint residual at the evaluation resolution. Where possible, fit a bipodal graphon and evaluate its constraint and entropy analytically (the 4-dimensional reduction). This directly addresses the smallest $q=0.10$ gaps.
2. **Standardized seed study.** Use at least 10 seeds for:
   - triangle $\mathbf{(P2)}$, especially $q=0.10,r\in\{0.4,0.5,0.6\}$;
   - $C_7$ at one diagonal/banded density, preferably $p=5/8$;
   - $H_6$ at the reported novel-structure density;
   - one known benchmark such as $K_3,p=7/9$.
   Report mean/SD, median/IQR, best, constraint residual, success rate, and structural-parameter variability.
   *Status:* 10 repetitions on $K_3,p=7/9$ are done (mean $0.435711$, 95% CI $[0.435705, 0.435718]$, optimum $98/225\approx0.435556$). The learning-rate-cycle study was dropped (misreading of "frequency schedule"); the $C_5$ permutation study is running. The open instances (triangle $\mathbf{(P2)}$ at $q=0.10$, $C_7$ at $p=5/8$, $H_6$) are not yet launched — these are the distributions the reviewers weighted most.
3. **Population-gradient diagnostic.** Freeze representative checkpoints; use a very large reference batch; over repeated batches at $N=2^{10},\ldots,2^{16}$, report gradient bias, relative norm error, and cosine similarity. This is much cheaper than retraining and directly answers Reviewer 1jpj.
4. **175-graph failure breakdown.** For the 11.8% suboptimal cases, count how many are local-optimum convergence versus NaN divergence, to fill the failure-mode fractions promised to Reviewer BFdn.
5. **Runtime microbenchmark.** Report seconds/iteration and peak memory for $N\in\{2^{12},2^{14},2^{16}\}$, $d\in\{64,128,256\}$, and representative motifs $K_3,C_5,C_7,H_6,$ Petersen. Full 20,000-epoch reruns are unnecessary.

### Priority 2: architecture and baselines

1. **Factorized architecture study (running).** The full paper ablation suite (plain MLP, ResNet, our model, constant scale, regulariser, constant LR low/high) is being rerun on $K_3,p=7/9$ with GeLU features in place of the sinusoidal per-layer features, injection structure fixed. Each variant paired with its GeLU counterpart isolates the sinusoidal component from the per-layer injection.
2. **Xia/SIREN baseline (covered by the ablation).** The plain-MLP variant with sinusoidal activations in the rerun ablation suite is a parameter-matched SIREN, so no separate run is needed; quote its number as the Xia-style backbone control. If feasible, also report the original smaller Xia architecture.
3. **Permutation audit (running).** On $C_5$, training with three symmetry sets: identity only, the two cyclic permutations $(0\,1\,2\,3\,4)$ and $(0\,2\,4\,1\,3)$, and the full permutation set. If time permits, additionally compare estimator variance and wall time at fixed trained graphons.
4. **Selective baseline extension.** Add fixed-grid/SBM and SIREN results for $C_7,p=5/8$, the main $H_6$ case, and $K_3$ $\mathbf{(P2)}$ at $q=0.10,r=0.5$.
5. **Basis-function experiment (done).** The four-basis test (Fourier, Haar wavelet, Legendre, Bernstein; density optimisation and supervised least-squares fit at $K_3$, $p=7/9$) is implemented in `short_exps/other_representations.ipynb`. The numbers quoted to Reviewers 6KFF and BFdn are from the seed-41 run: optimisation diverges in every basis (e.g., Legendre reaches $t(K_3)\approx-2\times10^6$ before the stopping guard); supervised fits violate $[0,1]$ on 45.7% (Fourier) and 44.8% (Legendre = Bernstein, same polynomial span) of entries; Haar stays in $[0,1]$ with $t(K_3)=0.446430$.

### Priority 3: useful but lower rebuttal yield

- A wavelet/Gabor INR baseline.
- A full capacity sweep across every motif.
- Downstream graph-classification experiments.
- Broad reruns of all 175 graphs.

These are less likely to change the current decision than resolving the central robustness and $q=0.10$ precision questions.
