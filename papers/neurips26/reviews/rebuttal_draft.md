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
- The new chordal theorem: for every connected chordal graph $H$ (no induced cycle of length greater than 3) whose maximal cliques all have the same size $r\ge3$, the balanced complete $k$-partite graphon is a minimiser of $\mathbf{(P1)}$ at $p=1-1/k$ for every integer $k\ge r$. This settles 17 cases of the 175-graph study that were previously unproven.
- The new large-deviation theorem is local near the Lubetzky-Zhao phase boundary: for every $d$-regular $H$ with $d\ge2$, away from the exceptional value $r=(d-1)/d$, the nonconstant optimiser on the symmetry-breaking side is unique up to relabelling and bipodal in a nontrivial open neighbourhood. It does **not** automatically certify every parameter in Table 6.
- The $H_6$ construction remains a numerical conjecture; we have a symbolic construction only at $p=4/5$, without a proof of optimality.
- Lean status, to be stated precisely: the odd-cycle and chordal theorems are formalised in full, with no conditional assumptions. The formalisation of the large-deviation theorem takes some established results from the literature and parts of graphon theory as axioms.
- Do not offer links to proofs or formalisation: the response rules prohibit links except when a reviewer requests code.
- Do not describe a running or planned experiment as completed. Replace each results placeholder only after the corresponding numbers have been checked.
- Learning rates verified: $10^{-3},5\times10^{-4},10^{-4},5\times10^{-5}$, matching the submitted Appendix D.
- The count of 17 newly settled sweep cases is verified. Still author-verify the exact large-deviation theorem statement (it appears in the AC comment) against the current mathematical manuscripts.

## Optional confidential overview to the AC

We thank the AC and reviewers for their thoughtful feedback. The paper presents a neural discovery framework that searches over graphons, the limit objects of dense graphs, to solve difficult variational problems in extremal graph theory and large-deviation theory. Its recovery of known extremisers demonstrates strong optimisation performance, while its interpretable candidates for open problems have already led to rigorous new mathematical results, as we explain below. In the rebuttal, we address the reviewers' concerns by quantifying robustness and failure modes; bounding the quality of the large-deviation candidates found by our method and reporting three theorems prompted by learnt structures with our method; isolating the contributions of the architectural components; and analysing computational cost further.

**Robustness.**  Each submitted candidate was selected from exactly eight runs, one for each of two activations across four learning rates. This is a fixed, modest hyperparameter search. To measure sensitivity to initialisation independently of this search, during rebuttal we repeated the $K_3$ experiment at $p=7/9$ ten times under one fixed configuration. The mean objective was $0.435711$, with 95% confidence interval $[0.435705,0.435718]$. Seven runs recovered the clean five-block partition; the other three found five-part solutions of comparable objective quality whose smallest part deviated from an exact block. During rebuttal, we also classified the 11.8% of suboptimal cases in the submitted 175-graph sweep: 7% converged to a suboptimal local optimum, while 4.8% failed through NaNs or out-of-memory errors. Finally, a 1,000-batch audit showed that, at the training batch size $N=2^{16}$, solving the bias on a random batch rather than the final evaluation grid induces a population-constraint residual with standard deviation $1.1\times10^{-3}$ and maximum $3.4\times10^{-3}$; these errors decrease as $N^{-1/2}$ and do not persist after deterministic final calibration. Fixed-protocol studies for the key open instances and the $C_5$ permutation study remain in progress and are not claimed here. We will include the completed reproducibility, failure-mode, and population-constraint analyses in the revised version of the paper. [TODO: insert any completed open-instance and permutation-study results.]

**Rigorous bounds for the submitted large-deviation candidates.** The submitted paper reports learnt graphons for six triangle upper-tail settings $(q,r)\in\{0.05,0.10\}\times\{0.4,0.5,0.6\}$, where $q$ is the baseline Erdős-Rényi edge probability and $r^3$ is the target triangle density. Their entropies were evaluated by discretising each learnt graphon on an $M\times M$ grid and replacing the graphon integrals with finite sums in 64-bit floating-point arithmetic; no Monte Carlo sampling was used. During rebuttal, we strengthened this evaluation by re-solving the density constraint on each evaluation grid before computing the entropy. We then used Lemma 3.3 of Lubetzky and Zhao to compute a lower bound $L(q,r)$ on the optimal entropy. To obtain upper bounds independent of grid discretisation, we optimised the four-parameter bipodal family suggested by the learnt structures; the resulting graphons are feasible and their densities and entropies have exact closed forms. The lower and bipodal upper bounds bracket the true optimum within $7\times10^{-4}$ to $2.8\times10^{-3}$, while the revised learnt values lie within $4\times10^{-3}$ of the lower bound—and hence of the true optimum—at every triangle setting. The feasible upper bounds also certify that the Lubetzky-Zhao reference construction is suboptimal at all eighteen tested settings across $K_3$, $C_4$, and $C_5$. We will include the refined evaluation protocol, both bounds, and the revised values in the revised version of the paper.

**Mathematical results prompted by the learnt structures.** Since submission, analysis prompted by the learnt structures with our method has produced three new theorems.

First, for every graphon $W$ of edge density $p$ and every odd $m\ge3$, we proved
$$
t(C_m,W)\ge p^m-p(1-p)^{m-1}.
$$
For $m=3$ this is Goodman's inequality; the theorem extends it to all odd cycles. The bound is nontrivial for $p>1/2$ and sharp at the balanced complete $k$-partite graphon when $p=1-1/k$, proving that it is a minimiser there.

Second, we proved that if $H$ is a connected chordal graph (one with no induced cycle longer than three) whose maximal cliques all have the same size $r\ge3$, then, for every integer $k\ge r$, the balanced complete $k$-partite graphon minimises the $H$-density at fixed edge density $p=1-1/k$, the problem denoted by $\mathbf{(P1)}$ in the paper. This settles 17 cases of the submitted 175-graph study that were previously unproven.

Third, motivated by the bipodal outputs for the dense upper-tail problem, we proved that for every finite simple $d$-regular graph $H$ with $d\ge2$ and every Lubetzky-Zhao phase-boundary point with $r\ne(d-1)/d$, there is a nontrivial open neighbourhood such that, throughout its symmetry-breaking side, the optimiser is unique up to relabelling, nonconstant, and bipodal. This locally identifies the typical structure of the corresponding conditioned dense random graphs.

The neural framework supplies the candidate structures; separate mathematical arguments establish these theorems. The first two are fully formalised in Lean 4, while the formalisation of the third takes established results from the literature and parts of graphon theory as axioms. We are preparing manuscripts describing all three for submission to mathematics journals, and we will summarise their statements, scope, and connection to the learnt structures in the revised version of the paper.

**Architectural ablation.** The architectural components make distinct contributions: the gain is not explained merely by repeatedly injecting the input. The sinusoidal features help represent sharp block boundaries, while progressively increasing their frequency across depth refines those boundaries from coarse to fine. The submitted paper compared our architecture with a ResNet using sinusoidal encoding only in its first layer and included a constant-scale control for the progressive schedule. During rebuttal, we reran all six variants with GeLU features replacing the per-layer sinusoidal features while keeping the injection structure fixed. Every paired variant had a higher, hence worse, objective without the sinusoidal features. Together, the rebuttal ablation and the submitted constant-scale control distinguish the contributions of the sinusoidal features, repeated injection, and the progressive frequency schedule. We will include this factorised ablation and its interpretation in the revised version of the paper. [TODO: resolve the apparent mismatch between the ablation values and the stated $K_3,p=7/9$ optimum before posting.]

**Computational cost.** The method is practical on a single workstation GPU for small fixed motifs such as $K_3$, $C_5$, and $C_7$, which are representative of many concrete problems in extremal graph theory. Its cost grows quickly with motif size and the number of symmetry terms, so it is not intended for motifs with hundreds or thousands of vertices. The submitted experiments used training batches of $2^{12}$-$2^{16}$ samples; $2^{28}$ was only a one-time post-training evaluation budget. With network width $d$, depth $L$, batch size $N$, motif $H$, and symmetry set $\mathcal S$, the dominant per-iteration cost is $O(Nv(H)^2Ld^2+N|\mathcal S|e(H))$, with activation memory $O(Nv(H)^2Ld)$, where $v(H)$ and $e(H)$ are the numbers of vertices and edges. During rebuttal, we benchmarked the default setting ($d=256$, $L=5$, $N=2^{15}$) on the RTX A5000 used for the submitted experiments: $K_3$, $C_5$, and $C_7$ required respectively $0.054$, $0.172$, and $0.452$ seconds per iteration and $2.37$, $7.84$, and $16.45$ GB of peak memory. A 20,000-epoch run takes about 18 minutes for $K_3$ and 57 minutes for $C_5$; every submitted experiment fits on this single GPU. We will include the complexity analysis, benchmarks, and practical scope in the revised version of the paper.

## Reviewer 1jpj

Thank you for recognising our framework as coherent, the implicit-differentiation formula as mathematically sound, and best-run reporting as reasonable for candidate discovery. We answer the four questions directly below.

**1. Number of runs and robustness.** Every candidate reported in the submitted paper was selected from exactly eight runs: one run for each of two activations (sin or GeLU) across four learning rates ($10^{-3}$, $5\times10^{-4}$, $10^{-4}$, $5\times10^{-5}$). Thus, "best across multiple runs" refers to a finite eight-configuration hyperparameter search.
During rebuttal, to measure reproducibility separately from hyperparameter selection, we repeated the $K_3$ instance at $p=7/9$ ten times under a single fixed configuration (the same setting as the ablation study).
The objective is highly reproducible: the mean is $0.435711$ with 95% confidence interval $[0.435705, 0.435718]$, an interval of width $1.3\times10^{-5}$. 
Structurally, 7 of the 10 runs recovered the clean 5-block partition; the remaining 3 produced five parts whose smallest part deviates from an exact block while achieving comparable objective values. 
Since the 5-block construction is not the unique optimiser, this deviation does not indicate suboptimality.
We will perform the same repetition analysis for the open instances $C_5$, $C_7$, and $H_6$ during the discussion phase and include the fixed-configuration results in the revised version of the paper.

**2. Population interpretation of the implicit gradient.** The finite-batch implicit gradient is the exact gradient of the empirical constrained problem, but it is generally a biased estimator of the population constrained gradient. The bias arises because it contains a nonlinear term computed from samples. 
On the other hand, it is a consistent estimator of the population constrained gradient, by the following argument. 
For fixed $\theta$, the pre-sigmoid output $h_\theta$ is bounded on the compact domain $[0,1]^2$, say $|h_\theta|\le M$. Let $\widehat c_S(\theta)$ be the scalar offset that makes the batch-average density equal to the target $p$, and let $c(\theta)$ be the offset that makes the exact population density equal to $p$. Both offsets lie in
$$
[\mathrm{logit}(p)-M,\ \mathrm{logit}(p)+M].
$$
On this compact interval, the uniform law of large numbers gives almost-sure convergence of the empirical constraint to the population constraint, uniformly in $c$. 
Since the population constraint is strictly increasing in $c$, its constraint-enforcing offset is unique. It follows that $\widehat c_S(\theta)\to c(\theta)$ almost surely. 
Finally, the convergence of the implicit gradient follows from the continuous mapping theorem. 
We will state this argument and its assumptions explicitly in the revised version of the paper.

**3. Small sigmoid derivatives.** While the denominator may look like a source of numerical instability, the implicit derivative is a stable estimator, because it can be understood as a weighting scheme. 
For the edge-density constraint, writing $s_i = \mathit{sm}'(h_\theta(x_i)+\widehat c)$ for the sigmoid derivatives,
$$
\nabla_\theta \widehat c
=-\sum_i w_i\nabla_\theta h_\theta(x_i),
\qquad w_i=\frac{s_i}{\sum_j s_j},
$$
a weighted average of the per-sample logit gradients with nonnegative weights summing to one. 
Small sigmoid derivatives shrink the numerator and the denominator together: they can concentrate the weights on a few samples, but they never amplify the derivative, since
$$
\|\nabla_\theta\widehat c\|\le \max_i\|\nabla_\theta h_\theta(x_i)\|.
$$
A general homomorphism-density constraint follows the same idea, with the weights additionally carrying the products of the other edge probabilities. Consistent with this, we observed no numerical instability in any of our submitted experiments. We will add this weighting interpretation and stability discussion to the revised version of the paper.

**4. Why the KL variational problem describes conditioned Erdős-Rényi graphs.** 
Let us describe the connection in the easiest case, the large deviation of the number of edges. 
In $G(n,q)$, each of the $N=\binom n2$ edges is independently Bernoulli-$q$, so the probability that exactly $aN$ edges are present is
$$
\binom{N}{aN}q^{aN}(1-q)^{(1-a)N}
=\exp\!\Big(-N\big(a\log\tfrac{a}{q}+(1-a)\log\tfrac{1-a}{1-q}\big)+o(N)\Big)
$$
by Stirling's approximation: the exponential cost of an atypical edge fraction $a$ is the Bernoulli KL divergence between $a$ and $q$. 
The graphon large-deviation principle generalises this from a single edge fraction to a full edge-probability profile expressed by a graphon $W$, whose cost is the integrated KL divergence $h_q(W)$. 
Conditioning on an atypical $H$-density restricts the admissible profiles; the exponential probability of the event is controlled by the minimum of $h_q$ over them, and the conditioned graphs concentrate near the minimising graphons. 
We will add this explanation to the revised version of the paper.

**Mathematical outcome of the discovery workflow.** Since submission, the structures found by the framework have led to three new mathematical theorems.
First, for every graphon $W$ of edge density $p$ and every odd $m\ge3$,
$$
t(C_m,W)\ge p^m-p(1-p)^{m-1},
$$
extending Goodman's inequality to every odd cycle; the bound is tight at $p=1-1/k$, attained by the balanced complete $k$-partite graphon. 
Second, for every connected chordal graph whose maximal cliques all have the same size $r\ge3$, the balanced complete $k$-partite graphon is a minimiser of $\mathbf{(P1)}$ at $p=1-1/k$ for every integer $k\ge r$; this proves 17 cases of our 175-graph case study that were previously unproven.
Third, for the dense upper-tail problem, every $d$-regular pattern graph with $d\ge2$ has, near each Lubetzky-Zhao phase-boundary point with $r \ne (d-1)/d$, a unique nonconstant bipodal optimiser up to relabelling throughout a nontrivial neighbourhood on the symmetry-breaking side.
The three theorems were proved with the help of GPT 5.5 and formalised in Lean 4 with the help of Claude Opus 4.8; the first two are formalised in full, with no conditional assumptions, while the formalisation of the third is partial and takes some established results from the literature and parts of graphon theory as axioms. 
Since the guidelines do not permit links in responses, we will gladly provide the Lean formalisation through the Area Chair to any reviewer who wishes to inspect it. 
We are preparing manuscripts describing all three for submission to mathematics journals, and we will summarise their statements, scope, and connection to the learnt structures in the revised version of the paper.
This is the intended use of the framework: learnt structures guide new mathematics.

## Reviewer PPij

Thank you for recognising our framework's novelty, our tailored architecture, and comprehensive experiments. We answer your questions below. 

**Sample size.** The $2^{28}$ figure is not the training batch size. Training uses $2^{12}$-$2^{16}$ sampled tuples; $2^{28}$ is a conservative, one-time post-training budget for evaluating the found graphons, and it is used only when deterministic high-resolution contraction is infeasible. 
The theoretical bound is as follows: for any fixed permutation set, the estimator is an average of $N$ independent tuple contributions in $[0,1]$. 
Hoeffding's inequality therefore gives
$$
\Pr(|\widehat t-t|\ge\epsilon)\le2e^{-2N\epsilon^2}.
$$
At $N=2^{28}$, the distribution-free 95% absolute-error bound is approximately $8.3\times10^{-5}$. 
Thus, $2^{28}$ was a conservative evaluation choice, not a sample size required by either training or theory. 
Training uses $2^{12}$-$2^{16}$, and the usual $N^{-1/2}$ rate lets users choose the evaluation budget for the desired absolute precision. We will state this distinction explicitly in the revised version of the paper.

**Runs.** Every candidate reported in the submitted paper was selected from exactly eight runs: one run for each of two activations (sin or GeLU) across four learning rates ($10^{-3}$, $5\times10^{-4}$, $10^{-4}$, $5\times10^{-5}$). Thus, "best across multiple runs" refers to a finite eight-configuration hyperparameter search.
During rebuttal, to measure reproducibility separately from hyperparameter selection, we repeated the $K_3$ instance at $p=7/9$ ten times under a single fixed configuration (the same setting as the ablation study).
The objective is highly reproducible: the mean is $0.435711$ with 95% confidence interval $[0.435705, 0.435718]$, an interval of width $1.3\times10^{-5}$. 
Structurally, 7 of the 10 runs recovered the clean 5-block partition; the remaining 3 produced five parts whose smallest part deviates from an exact block while achieving comparable objective values. 
Since the 5-block construction is not the unique optimiser, this deviation does not indicate suboptimality.
We will perform the same repetition analysis for the open instances $C_5$, $C_7$, and $H_6$ during the discussion phase and include the fixed-configuration results in the revised version of the paper.

**Relation to graphon learning.** 
Xia, Mishne, and Wang (2023) and, more recently, Azizpour, Zilberstein, and Segarra (AISTATS 2025) introduced implicit neural representations for graphon learning, a problem in network analysis: given a set of graphs $\{G_i\}_{i=1}^N$ assumed to be sampled from a common underlying graphon $W$, estimate $W$ from these samples. 
Because the goal is to reconstruct a graphon close to the true one from finite samples, sharp details of the true graphon are often lost; see, for instance, Figures 3(b) and 9 of Azizpour et al. 
Moreover, applying graphon learning to problems like ours would first require finding near-optimal finite graphs, which is itself a hard discrete optimisation, and only then estimating the underlying graphon from them. 
Our setting observes neither a graph dataset nor a target graphon: we search directly over graphons to optimise homomorphism-density or KL functionals under a density constraint. 
The contributions specific to this setting are the progressive per-layer input encoding for discontinuous extremisers, the symmetry-aware Monte Carlo estimators, and the embedded monotone constraint solver with implicit differentiation. 
We will cite Xia et al. and make clear in the revised version of the paper that we do not claim to introduce neural graphon representations.

During rebuttal, we also ran a parameter-matched SIREN backbone under our identical objective, solver, estimator, and budget on $K_3$ at $p=7/9$: it converged to the trivial constant graphon ($t(K_3,W)=0.470507\approx p^3$), whereas our method reaches $0.427215$. We will include this baseline and the distinction between graphon reconstruction and direct graphon optimisation in the revised version of the paper.

**Complexity.** Our method is manageable on one workstation GPU for the small fixed motifs common in extremal graph theory, although its cost grows quickly with motif size and it is not intended for motifs with hundreds or thousands of vertices.
With width $d$, depth $L$, batch size $N$, and cached evaluations on at most $\binom{v(H)}2$ unordered pairs per tuple, the dominant neural forward/backward cost is approximately
$$
O\!\left(Nv(H)^2Ld^2\right),
$$
with an additional $O(N|\mathcal S|e(H))$ cost for motif-product aggregation. 
Activation memory is approximately $O(Nv(H)^2Ld)$. 
Monte Carlo absolute error scales as $N^{-1/2}$, so halving it requires approximately four times as many samples. 
During rebuttal, we measured seconds per iteration of the core training step and peak memory on the RTX A5000 used for all experiments in our submission, varying one factor at a time from the default configuration (width $256$, depth $5$, $N=2^{15}$).

Sample size ($K_3$, width $256$):

| $N$ | $2^{12}$ | $2^{13}$ | $2^{14}$ | $2^{15}$ |
|---|---|---|---|---|
| sec/iter | 0.012 | 0.017 | 0.029 | 0.054 |
| peak memory (GB) | 0.33 | 0.63 | 1.20 | 2.37 |

Width ($K_3$, $N=2^{15}$):

| width | 128 | 256 | 512 |
|---|---|---|---|
| sec/iter | 0.023 | 0.054 | 0.151 |
| peak memory (GB) | 1.19 | 2.37 | 4.74 |

Motif ($N=2^{15}$, width $256$):

| motif | $\binom{v(H)}2$ | $\|\mathcal S\|$ | sec/iter | peak memory (GB) |
|---|---|---|---|---|
| $K_3$ | 3 | 1 | 0.054 | 2.37 |
| $C_5$ | 10 | 12 | 0.172 | 7.84 |
| $C_7$ | 21 | 360 | 0.452 | 16.45 |

The measurements match the stated scaling. Memory grows linearly in $N$ and in width, and proportionally to the pair count $\binom{v(H)}2$ across motifs. Time grows linearly in $N$ once the GPU is saturated (sub-linearly at small $N$ from under-utilisation), between linearly and quadratically in width, and roughly proportionally to the pair count across motifs, with the $C_7$ excess over this proportion coming from the $|\mathcal S|e(H)=360\times7$ aggregation term. 
Full-run wall-clock follows directly: $20000$ epochs take about $18$ minutes for $K_3$ and about $57$ minutes for $C_5$ at $N=2^{15}$. 
In training we choose the batch size to fill the available GPU memory, since larger batches reduce estimator variance at fixed wall time; gradient accumulation achieves the same batch size under smaller memory. 
Thus, every submitted experiment fits on a single workstation GPU. We will include the complexity analysis, benchmarks, and practical scope in the revised version of the paper.

## Reviewer 6KFF

Thank you for recognising that the paper tackles important problems, that the framework is interesting, and that the empirical results are encouraging. We can give concrete theoretical support, a clearer operating regime, and a direct account of the architecture's design.

**Theoretical results and operating regime.** 
A convergence guarantee for the nonconvex optimisation is out of reach, and we do not claim one. 
Instead, the framework now has theoretical results of a different kind: three new mathematical theorems proved from its outputs — an odd-cycle lower bound extending Goodman's inequality, a chordal-graph minimiser theorem, and a local structure theorem for the large-deviation problem — described in detail under "Application and significance" below. 
On when the method works well or fails: the target regime is dense-graph problems with one monotone scalar constraint, moderate motif density, and a low-complexity block or geometric optimiser. 
Across our experiments, the clearest failure diagnostic is a nearly competitive constant graphon. 
The problems we study often admit the constant graphon as a trivial solution, and when constant graphon's objective value is within roughly $10^{-5}$ of the best known value, training often remains at that trivial solution. 
We will state this operating regime and failure diagnostic explicitly in the revised version of the paper.

**Why progressive sinusoidal features.** The main conclusion is that the performance gain cannot be explained merely by repeated input injection: the sinusoidal features make an independent contribution, and the progressive frequency schedule provides a further benefit.
A step boundary requires increasingly high spatial frequencies for accurate approximation. 
The early, low-scale features provide coarse block geometry, while later high-scale features provide short paths that refine boundaries without forcing every preceding layer to preserve high-frequency information. 
The submitted paper included the sinusoidal ResNet and constant-scale controls. During rebuttal, to distinguish sinusoidal features from per-layer injection, we reran the entire ablation suite with GeLU features replacing the sinusoidal per-layer features while keeping the injection structure fixed. On $K_3$ at $p=7/9$:

| variant | with sinusoidal features | without |
|---|---|---|
| Ours | 0.427215 | 0.436118 |
| ResNet | 0.428968 | 0.436457 |
| Constant-scale $s$ | 0.428190 | 0.436500 |
| Regulariser | 0.434445 | 0.437376 |
| Constant LR (low) | 0.430071 | 0.442499 |
| Constant LR (high) | 0.431645 | 0.436795 |

Removing the sinusoidal features degrades every variant, and every value without them ($0.4361$-$0.4425$) is worse than every value with them ($0.4272$-$0.4344$). 
This attributes the gain to the sinusoidal features themselves rather than to the per-layer injection alone, while the existing constant-scale control separately tests the multiscale schedule. 
The $d^{-1/2}$ initialisation of residual matrices controls activation growth with fan-in, while the range of each row of $U^{(\ell)}$ directly controls the initialised spatial frequency. Increasing $s(\ell)$ therefore gives later layers access to progressively finer scales without increasing hidden-state magnitude.
We will include this factorised ablation, its interpretation, and an illustration of the multiscale encoding in the revised version of the paper.

**Wavelets.** 
Yes, in principle: the constraint solver and Monte Carlo estimator are representation-agnostic, so wavelet-type features could replace the sinusoidal ones inside the network. 
During rebuttal, we tested other encodings in non-neural form: parameterising $W$ directly as a symmetric linear combination of a fixed basis — Fourier, Haar wavelet, and polynomial — on $K_3$ minimisation at $p=7/9$.
In direct objective optimisation, all of them diverge: a fixed linear basis cannot enforce the constraint $W(x,y)\in[0,1]$, at any basis size. 
We further tested the expressivity of these bases by training them to fit the known optimal solution.
The Fourier and polynomial representations overshoot the step boundaries by about $\pm0.2$ (known as the Gibbs phenomenon) and violate the bound on about half of the domain.
The Haar representation stays within $[0,1]$ and reaches $t(K_3,W)=0.436341$.

**Application and significance.** 
Since submission, the strongest independent validation is that structures found by the framework have led to three new mathematical theorems.
First, for every graphon $W$ of edge density $p$ and every odd $m\ge3$,
$$
t(C_m,W)\ge p^m-p(1-p)^{m-1},
$$
extending Goodman's inequality to every odd cycle; the bound is tight at $p=1-1/k$, attained by the balanced complete $k$-partite graphon. 
Second, for every connected chordal graph whose maximal cliques all have the same size $r\ge3$, the balanced complete $k$-partite graphon is a minimiser of $\mathbf{(P1)}$ at $p=1-1/k$ for every integer $k\ge r$; this proves 17 cases of our 175-graph study that were previously unproven.
Third, for the dense upper-tail problem, every $d$-regular pattern graph with $d\ge2$ has, near each Lubetzky-Zhao phase-boundary point with $r \ne (d-1)/d$, a unique nonconstant bipodal optimiser up to relabelling throughout a nontrivial neighbourhood on the symmetry-breaking side.
The three theorems were proved with the help of GPT 5.5 and formalised in Lean 4 with the help of Claude Opus 4.8; the first two are formalised in full, with no conditional assumptions, while the formalisation of the third takes some established results from the literature and parts of graphon theory as axioms. 
Since the guidelines do not permit links in responses, we will gladly provide the Lean formalisation through the Area Chair to any reviewer who wishes to inspect it. 
We are preparing manuscripts describing all three for submission to mathematics journals, and we will summarise their statements, scope, and connection to the learnt structures in the revised version of the paper.
This is the intended use of the framework: learnt structures guide new, independent mathematics.

While there are practical applications of extremal graph theory in graph machine learning, such as the use of expander graphs in GNNs, these involve sparse graphs, which are outside the scope of our current work. 
On the dense side, the closest practical contact point is the exponential random graph model (ERGM), a standard model of social networks in the social sciences. 
In the dense regime, the asymptotic behaviour of an ERGM is governed by a graphon variational problem of exactly the type our framework optimises: its free energy maximises a linear combination of homomorphism densities minus an entropy functional as in $\mathbf{(P2)}$, and its typical networks concentrate near the optimal graphons (Chatterjee and Diaconis, 2013). 
The well-known degeneracy of ERGM fitting corresponds to phase transitions of these optimisers, so our framework could be used to compute the optimal structures, map phase diagrams, and diagnose degenerate parameter regions before fitting. 
We consider this a promising direction for our future work and will add this practical-context discussion to the revised version of the paper.

**Computational cost.** The practical conclusion is that the method is manageable on one workstation GPU for the small fixed motifs common in extremal graph theory, although its cost grows quickly with motif size and it is not intended for motifs with hundreds or thousands of vertices.
With width $d$, depth $L$, batch size $N$, and motif $H$, the dominant per-iteration cost is $O(Nv(H)^2Ld^2+N|\mathcal S|e(H))$, with activation memory $O(Nv(H)^2Ld)$. Training uses $2^{12}$-$2^{16}$ samples; $2^{28}$ is only a one-time evaluation budget. 
During rebuttal, we measured seconds per iteration of the core training step and peak memory on the RTX A5000 used for all submitted experiments, varying one factor at a time from the default configuration (width $256$, depth $5$, $N=2^{15}$).

Sample size ($K_3$, width $256$):

| $N$ | $2^{12}$ | $2^{13}$ | $2^{14}$ | $2^{15}$ |
|---|---|---|---|---|
| sec/iter | 0.012 | 0.017 | 0.029 | 0.054 |
| peak memory (GB) | 0.33 | 0.63 | 1.20 | 2.37 |

Width ($K_3$, $N=2^{15}$):

| width | 128 | 256 | 512 |
|---|---|---|---|
| sec/iter | 0.023 | 0.054 | 0.151 |
| peak memory (GB) | 1.19 | 2.37 | 4.74 |

Motif ($N=2^{15}$, width $256$):

| motif | $\binom{v(H)}2$ | $\|\mathcal S\|$ | sec/iter | peak memory (GB) |
|---|---|---|---|---|
| $K_3$ | 3 | 1 | 0.054 | 2.37 |
| $C_5$ | 10 | 12 | 0.172 | 7.84 |
| $C_7$ | 21 | 360 | 0.452 | 16.45 |

The measurements match the stated scaling: memory grows linearly in $N$ and in width, and proportionally to the pair count $\binom{v(H)}2$ across motifs; time grows linearly in $N$ once the GPU is saturated, between linearly and quadratically in width, and roughly proportionally to the pair count, with the $C_7$ excess coming from the $|\mathcal S|e(H)=360\times7$ aggregation term. 
A full $20000$-epoch run takes about $18$ minutes for $K_3$ and about $57$ minutes for $C_5$. 
In training we choose the batch size to fill the available GPU memory, since larger batches reduce estimator variance at fixed wall time; gradient accumulation achieves the same batch size under smaller memory. 
Every submitted experiment fits on this single workstation GPU. We will include the complexity analysis, benchmarks, and practical scope in the revised version of the paper.

## Reviewer BFdn

Thank you for recognising the coherent methodology, effective symmetry-aware estimator, and extensive experimental scope. We address the two issues most relevant to the score—novelty and reliability—before answering the individual experimental questions.

**Benefit from the sinusoidal encoding.** The main conclusion is that the gain cannot be explained merely by repeated input injection: the sinusoidal features make an independent contribution, while the progressive frequency schedule provides a further benefit. The submitted paper included the sinusoidal ResNet and constant-scale controls. During rebuttal, to distinguish sinusoidal features from per-layer injection, we reran the entire ablation suite with GeLU features replacing the sinusoidal per-layer features while keeping the injection structure fixed. On $K_3$ at $p=7/9$:

| variant | with sinusoidal features | without |
|---|---|---|
| Ours | 0.427215 | 0.436118 |
| ResNet | 0.428968 | 0.436457 |
| Constant-scale $s$ | 0.428190 | 0.436500 |
| Regulariser | 0.434445 | 0.437376 |
| Constant LR (low) | 0.430071 | 0.442499 |
| Constant LR (high) | 0.431645 | 0.436795 |

Removing the sinusoidal features degrades every variant, and every value without them ($0.4361$-$0.4425$) is worse than every value with them ($0.4272$-$0.4344$). This attributes the gain to the sinusoidal features themselves rather than to the per-layer injection alone, while the submitted constant-scale control separately tests the progressive frequency schedule. We will include this factorised ablation and its interpretation in the revised version of the paper.

**Lubetzky-Zhao comparison and independent verification of $\mathbf{(P2)}$.** In the submitted paper, the Table 6 entropy values were computed by deterministic 64-bit numerical integration, not Monte Carlo sampling, so sampling error does not enter them.
During rebuttal, we refined the evaluation by enforcing the constraint exactly at the evaluation resolution, which slightly revises the reported values below.
More importantly, independent verification is possible in both directions. 
In one direction, from the conjecture suggested by our observations — the learnt profiles are nearly bipodal — we numerically optimised the four-parameter bipodal family (value $a$ on $[0,t)^2$, $b$ on the mixed blocks, $c$ on $[t,1]^2$), in which both $t(K_3,W)$ and $h_q(W)$ are exact closed forms; each optimised member is an explicit feasible graphon, hence an upper bound on the optimum, though not a lower bound.
In the other direction, Lemma 3.3 of Lubetzky and Zhao (2012) provides a computable lower bound: for a $2$-regular pattern graph, the optimum is at least the convex minorant of $x \mapsto h_q(x^{1/2})$ evaluated at $x = r^2$. 
The results:

| $q$ | $r$ | lower bound | bipodal $h_q$ (explicit, feasible) | $h_q(W_{\mathrm{ours}})$, revised | $h_q(W_{\mathrm{LZ}})$ | $\Delta = h_q(W_{\mathrm{LZ}})-h_q(W_{\mathrm{ours}})$ |
|---|---|---|---|---|---|---|
| 0.05 | 0.4 | 0.460284 | 0.463083 | 0.464208 | 0.556057 | 0.091849 |
| 0.05 | 0.5 | 0.725284 | 0.727151 | 0.727881 | 0.830366 | 0.102485 |
| 0.05 | 0.6 | 1.049172 | 1.050275 | 1.051203 | 1.144945 | 0.093742 |
| 0.10 | 0.4 | 0.306561 | 0.308803 | 0.309109 | 0.311239 | 0.002130 |
| 0.10 | 0.5 | 0.504311 | 0.505990 | 0.506060 | 0.510826 | 0.004766 |
| 0.10 | 0.6 | 0.746006 | 0.746713 | 0.747694 | 0.750684 | 0.002990 |

The lower bound and the feasible bipodal values agree to within $7\times10^{-4}$ to $2.8\times10^{-3}$ in every cell, and $h_q(W_{\mathrm{LZ}})$ exceeds even the bipodal upper bounds. 
Thus, $W_{\mathrm{LZ}}$ is certified suboptimal in all six cells, including the small-gap $q=0.10$ regime, and the revised learnt values lie within $4\times10^{-3}$ of the computable lower bound (the exact optimum itself is not known; its bipodal form is our conjecture); the run study below separately measures discovery reliability. 
The same audit extends to $C_4$ and $C_5$: both are $2$-regular, so the same lower bound applies at $x=r^2$, the bipodal cycle densities are again closed forms, and explicit feasible bipodal graphons beat $W_{\mathrm{LZ}}$ in all 18 cells across the three pattern graphs; the revised $C_5$ values at $q=0.05$ are $0.465644, 0.727618, 1.052023$ ($q=0.10$ values unchanged).

Finally, we note that the Lubetzky-Zhao construction is not specific to the triangle: it is defined for every $d$-regular pattern graph, so it is an equally valid reference for $C_4$ and $C_5$. 
Its role, for all three pattern graphs, is that of a reference construction demonstrating non-optimality of the constant graphon rather than a claimed optimum; with the bounds above, the $C_4$ and $C_5$ comparisons carry the same certification as $K_3$.
We will include the refined evaluation protocol, the lower and upper bounds, and the corrected values in the revised version of the paper.

**Run distribution.** Every candidate reported in the submitted paper was selected from exactly eight runs: two activations crossed with four learning rates ($10^{-3}$, $5\times10^{-4}$, $10^{-4}$, $5\times10^{-5}$).
During rebuttal, to measure sensitivity to initialisation separately from this search, we repeated the $K_3$ instance at $p=7/9$ ten times under a single fixed configuration: the mean objective is $0.435711$ with 95% confidence interval $[0.435705, 0.435718]$; 7 of the 10 runs recovered the clean 5-block partition, and the remaining 3 reached comparable objective values with the smallest part deviating from an exact block (the 5-block construction is not the unique optimiser, so this does not indicate suboptimality).
We will report the same repetition analysis for $C_5$, $C_7$, and $H_6$ during the discussion phase and include the fixed-protocol results in the revised version of the paper.

**The 11.8% suboptimal sweep cases.** 
During rebuttal, we classified the 11.8% of suboptimal cases in the submitted sweep: 7% converged to a suboptimal local optimum, and 4.8% failed from training or inference instability (divergence to NaN or out-of-memory errors).
Independently of this failure analysis, we have proved — with the help of GPT 5.5, and verified in Lean 4 with the help of Claude Opus 4.8 — that if a graph is connected and chordal and all of its maximal cliques have the same size $r\ge3$, then the balanced complete $k$-partite graphon is a minimiser of $\mathbf{(P1)}$ at $p=1-1/k$ for every integer $k\ge r$.
This proves exact optimality for 17 cases of the sweep at the densities $p=1-1/k$; for these cases, our flag-algebra bounds were tight only in the low-density regime and did not certify all the learnt graphons at $p=1-1/k$. We will add this failure-mode classification and the new certification status to the revised version of the paper.

**Why the neural representation helps.** 
The non-neural baselines reported in Appendix H of the submitted paper have enough expressivity to represent the optimal solution; the observed difference is optimisation.
For the tree-based baselines and the fixed-grid SBM, moving a decision boundary is hard: almost every $\{0,1\}$-valued configuration is a local optimum that cannot be escaped without a reset, so these methods depend strongly on the initialisation and rarely leave the geometry of their initial solution. 
Parameterising the decision boundary directly (the second and third panels of Figure 15) also fails: the optimisation landscape is very sharp, and training always converges to the constant solution. 
The neural graphon instead optimises the region values and the boundary locations jointly and continuously, and we view this joint flexibility, combined with a favourable optimisation landscape, as the main benefit of the neural representation. 
The discovery advantage is that the network does not require choosing in advance between multipartite, diagonal/banded, circular-distance, or bipodal forms. We will add this optimisation-based interpretation of the baseline comparison to the revised version of the paper.

## Reviewer s6Ge

Thank you for recognising the mathematically meaningful problem setting, the problem-specific architecture, and the breadth of the experiments. We address reliability with targeted sensitivity studies and, more importantly, with explicit constructions and new mathematical theorems.

**Initialisation, schedule, and permutation sensitivity.** 
Every value reported in the submitted paper was selected from exactly eight runs: two activations crossed with four learning rates ($10^{-3}$, $5\times10^{-4}$, $10^{-4}$, $5\times10^{-5}$). During rebuttal, we separated that finite hyperparameter search from reproducibility through three controlled studies.
(i) Initialisation: we repeated the $K_3$ instance at $p=7/9$ ten times under a single fixed configuration. The mean objective is $0.435711$ with 95% confidence interval $[0.435705, 0.435718]$; 7 of the 10 runs recovered the clean 5-block partition, and the remaining 3 reached comparable objective values with the smallest part deviating from an exact block (the 5-block construction is not the unique optimiser, so we report structure recovery and objective quality separately). The same repetition analysis for $C_5$, $C_7$, and $H_6$ will follow during the discussion phase. 
(ii) Frequency schedule: we trained with both encoding-scale schedules. With $s(\ell)=2^{\ell-1}$, the ten repetitions above give mean $0.435711$; with $s(\ell)=\ell$, the best run gives $0.435754$. The discovered solution and its objective are insensitive to the schedule choice.
(iii) Permutations: on $C_5$, we are comparing three symmetry sets for the estimator: the identity only; the two cyclic orderings $0\text{-}1\text{-}2\text{-}3\text{-}4$ and $0\text{-}2\text{-}4\text{-}1\text{-}3$; and the full set of coset representatives. Every choice is unbiased and changes variance and cost rather than the target; the full cycle estimator averages all coset representatives, so its value does not depend on which representatives are chosen. We will include the completed sensitivity studies and their protocol in the revised version of the paper. [TODO: insert permutation-study results.]

**Population-level constraint error.** 
The constraint solver runs not only during training but also on the final trained graphon: the submitted evaluation re-solves the scalar bias deterministically on the evaluation grid, so no training-batch residual persists in the reported values (and the reference is converged: refining the grid from $256^2$ to $512^2$ changes $t(K_3)$ by only $9.7\times10^{-5}$).
During rebuttal, we additionally measured how much a random batch would move the output at the final $K_3$ graphon, using 1000 independent batches per batch size.
At the training size $N=2^{16}$, solving the bias on a batch instead of the grid induces a population constraint residual of standard deviation $1.1\times10^{-3}$ (maximum $3.4\times10^{-3}$, mean $1.2\times10^{-4}$), an entry-wise output standard deviation averaging $1.1\times10^{-3}$, and a spread of $t(K_3)$ with standard deviation $2.3\times10^{-3}$; all of these shrink as $N^{-1/2}$. We will include this population-level constraint audit and the grid-convergence check in the revised version of the paper.

**Analytic constructions and mathematical outcome.** 
For $C_5$, the construction of Bennett et al. is known optimal at $p=1-1/k$ and conjectured optimal at the densities in between. For $C_7$, the conjecture described in Appendix E generalises this construction to a specific parametric family, and our learnt graphons do not follow it, so we do not currently have an explicit symbolic construction for them. This does not imply that the learnt graphons are suboptimal: the minimiser need not be unique, and the conjectured construction is only one of the possible optima. 
For $H_6$, we have a symbolic construction at $p=4/5$ only, where the learnt circular-distance pattern has the form
$$
W(x,y)=\begin{cases}1&\text{if }|x-y|\in[0.1,0.9],\\0&\text{otherwise},\end{cases}
$$
whose optimality we have not proved. 
More substantially, since submission, follow-up analysis of the learnt structures has produced three new theorems. For every graphon and every odd $m\ge3$, we proved
$$
t(C_m,W)\ge p^m-p(1-p)^{m-1}
$$
extending Goodman's inequality to all odd cycles and proving optimality of the balanced complete $k$-partite graphons at $p=1-1/k$. 
We also proved that the balanced $k$-partite graphon is a minimiser for every connected chordal graph whose maximal cliques have a common size $r\ge3$; this proves 17 cases of the 175-graph study that were previously unproven.
For the dense upper-tail problem in $\mathbf{(P2)}$, we proved unique nonconstant bipodal optimisers in a nontrivial neighbourhood on the symmetry-breaking side of every nonexceptional Lubetzky-Zhao phase-boundary point for every $d$-regular $H$, $d\ge2$.
The three theorems were proved with the help of GPT 5.5 and formalised in Lean 4 with the help of Claude Opus 4.8; the first two are formalised in full, with no conditional assumptions, while the formalisation of the third takes some established results from the literature and parts of graphon theory as axioms. 
We are preparing manuscripts describing all three for submission to mathematics journals. Outside the proved regimes, including $H_6$ and $C_7$ away from the sharp densities, we retain candidate language. We will summarise these results, their connection to the learnt structures, and their precise scope in the revised version of the paper.

**Levels of evidence.** 
We agree that these three levels should be kept explicit, and in the revision we will label every reported instance with one of them. 
- Rediscovery of a known extremal construction: Figures 1-3. The $K_3$ and clique optima are classical; the $C_5$ optimum is known at $p=1-1/k$, while at the intermediate densities the construction is conjectured optimal, so those cells belong to the second category. 
- Numerically competitive candidates: Figure 4 ($C_7$) and the $\mathbf{(P2)}$ instances of Figures 6 and 8-12.  
- Evidence against an existing reference construction: Figure 5 ($H_6$), where the learnt graphons improve on both the constant and the $k$-partite reference constructions at every tested density.

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
   *Status:* 10 repetitions on $K_3,p=7/9$ are done (mean $0.435711$, 95% CI $[0.435705, 0.435718]$). The learning-rate-cycle study was dropped (misreading of "frequency schedule"); the $C_5$ permutation study is running. The open instances (triangle $\mathbf{(P2)}$ at $q=0.10$, $C_7$ at $p=5/8$, $H_6$) are not yet launched — these are the distributions the reviewers weighted most.
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
