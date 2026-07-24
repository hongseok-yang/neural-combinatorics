# NeurIPS 2026 rebuttal draft

Internal drafting note: the 2026 rules allow up to 10,000 characters per review, permit new results, prohibit links and identifying information, and do not permit revised PDFs or new supplementary files during rebuttal. Remove every bracketed placeholder before posting.

## Claims that must be kept distinct

- The neural method finds candidates; it does not itself prove global optimality.
- The post-submission odd-cycle theorem is
  \[
  t(C_m,W)\ge p^m-p(1-p)^{m-1}
  \]
  for every graphon \(W\) of edge density \(p\) and every odd \(m\ge3\). It is sharp at balanced complete multipartite graphons, at the Turán densities \(p=1-1/k\).
- This theorem is a universal lower envelope. It does **not** prove the stronger exact-optimizer conjecture stated in the NeurIPS appendix at every \(p\), and it does not certify every displayed \(C_7\) candidate.
- The post-submission large-deviation theorem applies locally near the Lubetzky-Zhao phase boundary: for every \(d\)-regular \(H\) with \(d\ge2\), away from the exceptional value \(r=(d-1)/d\), the nonconstant optimizer on the symmetry-breaking side is unique up to relabelling and bipodal in a nontrivial open neighborhood. It does **not** automatically certify every parameter in Table 6.
- The \(H_6\) construction remains a numerical conjecture.

## Optional confidential overview to the AC

We thank the AC and reviewers for identifying four points that were under-documented: cross-run variability, independent validation of candidates, architectural disentanglement, and computational scaling. We agree that the neural optimizer alone is a discovery tool rather than a proof of global optimality, and we will sharpen the manuscript’s language to distinguish (i) recovery of theorem-backed optima, (ii) candidates matching independent lower bounds, and (iii) numerically competitive candidates.

**Robustness and numerical validation.** The original submission reports best-of-runs values but does not state the exact number of runs or cross-run variability. The exact counts were [INSERT COUNTS FROM LOGS]. We have now rerun the central claims under a standardized protocol with [N] independent seeds and report the objective, held-out population-constraint residual, fitted structural parameters, and success rate rather than only the best run. [INSERT 2-3 SENTENCE SUMMARY OF RESULTS.] For the triangle upper-tail comparison, we independently evaluated \(h_q(W)\) and the constraint on held-out samples and report the paired difference \(h_q(W_{\mathrm{LZ}})-h_q(W_{\mathrm{ours}})\). At \(q=0.10\), the 95% intervals are [INSERT], so [STATE WHETHER EACH IMPROVEMENT IS RESOLVED ABOVE NUMERICAL AND OPTIMIZATION VARIABILITY].

**Independent mathematical follow-up.** Following the learned \(C_5/C_7\) structures in the submission, we isolated a tractable universal consequence and have since proved that, for every graphon \(W\) of edge density \(p\) and every odd \(m\ge3\),
\[
t(C_m,W)\ge p^m-p(1-p)^{m-1}.
\]
The bound is nontrivial for \(p>1/2\) and sharp at every balanced complete multipartite graphon. This is a lower-envelope theorem, not a classification of the exact minimizer at every density. A journal manuscript is in preparation. The proof is analytic apart from two exact-rational univariate Bernstein positivity certificates for \(m=9\), and an earlier proof architecture covering the nontrivial regimes has been checked modularly in Lean.

Motivated independently by the bipodal outputs for the large-deviation problem, we have also proved a local structural theorem. For every \(d\)-regular graph \(H\) with \(d\ge2\) and every nonexceptional point of the Lubetzky-Zhao phase boundary, there is a nontrivial open neighborhood in which the optimizer on the symmetry-breaking side is unique up to relabelling and bipodal, with parameters and optimal value analytic in \((p,r)\). Consequently, the corresponding conditioned dense random graphs concentrate in cut distance around this bipodal structure. This gives a partial answer to Chatterjee’s first open problem, which asks for explicit nonconstant solutions or mathematically provable qualitative properties of them. The result is local and is not being used to claim certification of every Table 6 entry. These developments support the intended scientific role of the submitted framework: it produces interpretable structures that can seed rigorous mathematics, while the proofs are separate mathematical work.

**Architecture and cost.** We will add Xia et al. (2023), who use a SIREN to reconstruct graphons from observed graphs with a Gromov-Wasserstein loss, and narrow our novelty claim accordingly. Our setting has no observed target graphon: it directly optimizes variational functionals and adds a progressive per-layer encoding, a monotone constraint layer, and symmetry-aware integral estimators. We have also added [INSERT FACTORIZED ABLATION SUMMARY], including a parameter-matched SIREN control. Finally, \(2^{28}\) is a one-time post-training evaluation budget, not the training batch size; training uses \(2^{12}\)-\(2^{16}\). The dominant network cost is approximately \(O(Nv(H)^2Ld^2)\), plus \(O(N|\mathcal S|e(H))\) for motif-product aggregation. [INSERT MEASURED RUNTIME/MEMORY TABLE SUMMARY.]

## Reviewer 1jpj

Thank you for the careful assessment. We agree that the paper should be more explicit about run variability and about the distinction between an empirical constrained gradient and the population constrained gradient.

**1. Number of runs and robustness.** The exact protocol for the submitted tables was [INSERT: number of initializations, learning rates, and total runs per instance; recover from logs rather than inferring “four” from the four listed learning rates]. We have additionally run [N] independent seeds under a fixed protocol on [LIST KEY INSTANCES]. We will report mean, standard deviation, median/IQR, best value, held-out constraint residual, and the fraction recovering the same structure up to graphon relabelling. [INSERT RESULTS.] This directly replaces the ambiguous “best across multiple runs” wording.

**2. Population interpretation of the implicit gradient.** The reviewer is correct that unbiasedness of the density estimator does not imply finite-batch unbiasedness of the complete implicit gradient. For a sampled batch \(S\), our formula is the exact gradient of the empirical constrained objective whose empirical root is \(\widehat c_S(\theta)\). Because solving for a random root is nonlinear, its expectation is generally not exactly the population constrained gradient; we will not claim otherwise. Under the standard conditions that the empirical constraint and its first derivatives converge uniformly near the population root and that the population derivative with respect to \(c\) is nonzero, the implicit-function/Z-estimator argument gives \(\widehat c_S\to c\) and convergence of the empirical implicit gradient to the population constrained gradient as \(N\to\infty\). We will state this consistency claim and its assumptions explicitly. At fixed checkpoints, we also compared the gradient with a large-batch reference over \(N=2^{10},\ldots,2^{16}\): [INSERT BIAS/COSINE-ERROR RESULT].

**3. Small sigmoid derivatives.** There are two distinct issues. The raw Newton step can indeed become unstable under saturation; Appendix D already describes our clipped Newton update, and we will move this explanation forward. Backpropagation is better behaved than a bare “division by a small number” suggests. Writing \(h_\theta\) for the pre-sigmoid logit, the implicit derivative of the scalar bias has the form
\[
\nabla_\theta \widehat c
=-\sum_i w_i\nabla_\theta h_\theta(x_i),
\qquad w_i\ge0,\quad \sum_iw_i=1.
\]
For a general homomorphism-density constraint, the index \(i\) runs over sampled edge occurrences and the nonnegative weights also include the products of the other edge probabilities. Thus
\[
\|\nabla_\theta\widehat c\|\le \max_i\|\nabla_\theta h_\theta(x_i)\|.
\]
Small sigmoid derivatives shrink numerator and denominator together and do not intrinsically amplify the implicit gradient. Clipping is needed for the separate forward root solve. Floating-point underflow is a distinct implementation concern, so we additionally measured [MINIMUM DERIVATIVE / SOLVER FAILURE RATE / GRADIENT NORM: INSERT].

**4. Why the KL variational problem describes conditioned Erdős-Rényi graphs.** In \(G(n,q)\), each edge is independently Bernoulli-\(q\). A macroscopic edge-probability profile \(W\) has per-edge log-likelihood cost \(h_q(W)\), the integrated Bernoulli KL divergence from \(q\). Conditioning on an atypical \(H\)-density restricts the admissible profiles. The graphon large-deviation principle states that the exponential probability of this event is controlled by the minimum KL cost, and that conditioned graphs concentrate near the minimizing graphons. We will add this short explanation before the formal variational statement.

Finally, we agree that numerical discovery is not a proof. Following the learned odd-cycle structures, we have since proved the universal Goodman-style bound
\[
t(C_m,W)\ge p^m-p(1-p)^{m-1}
\]
for every graphon and every odd \(m\ge3\), sharp at the balanced complete multipartite densities. Separately, the bipodal large-deviation outputs motivated a theorem proving unique bipodal optimizers in a nontrivial neighborhood on the symmetry-breaking side of the phase boundary for every \(d\)-regular pattern graph with \(d\ge2\). These are post-submission mathematical manuscripts in preparation and demonstrate the discovery-to-proof use case, without retroactively certifying every numerical candidate.

## Reviewer PPij

Thank you. We agree that the sample budget, run count, and relation to Xia et al. should have been explained more clearly.

**Sample size.** The \(2^{28}\) figure is not the training batch size. Training uses \(2^{12}\)-\(2^{16}\) sampled tuples; \(2^{28}\) is a conservative, one-time post-training evaluation budget used only when deterministic high-resolution contraction is infeasible. For any fixed permutation set, the estimator is an average of \(N\) independent tuple contributions in \([0,1]\). Hoeffding’s inequality therefore gives
\[
\Pr(|\widehat t-t|\ge\epsilon)\le2e^{-2N\epsilon^2}.
\]
At \(N=2^{28}\), the distribution-free 95% absolute-error bound is approximately \(8.3\times10^{-5}\). This is an upper bound, not a claim that \(2^{28}\) is necessary, and it does not provide a useful relative-error guarantee when the true motif density is extremely small. We will clarify all three points.

**Runs.** The submitted protocol used [INSERT EXACT COUNT AND BREAKDOWN]. We have now added [N]-seed statistics on [INSTANCES], reporting the distribution and success rate rather than only the best run: [INSERT SUMMARY].

**Relation to Xia, Mishne, and Wang (2023).** Thank you for identifying this important omission. Xia et al. introduced implicit neural graphon representations for a different task: reconstructing an unknown graphon from observed finite graphs using a SIREN and a Gromov-Wasserstein reconstruction loss, with extensions to graph generation and graph representation learning. Our task observes no target graphon or graph dataset. We directly optimize homomorphism-density or KL functionals under a density constraint. The contributions specific to this setting are the progressive per-layer input encoding for discontinuous extremizers, the symmetry-aware Monte Carlo estimators, and the embedded monotone constraint solver with implicit differentiation. We will add the citation, narrow our novelty wording so that we do not claim to introduce neural graphon representations, and compare against a parameter-matched Xia/SIREN backbone under our same objective, solver, and estimator. [INSERT BASELINE RESULT.]

**Complexity.** With width \(d\), depth \(L\), batch size \(N\), and cached evaluations on at most \(\binom{v(H)}2\) unordered pairs per tuple, the dominant neural forward/backward cost is approximately
\[
O\!\left(Nv(H)^2Ld^2\right),
\]
with an additional \(O(N|\mathcal S|e(H))\) cost for motif-product aggregation. Activation memory is approximately \(O(Nv(H)^2Ld)\). Monte Carlo absolute error scales as \(N^{-1/2}\), so halving it requires approximately four times as many samples. On one RTX A5000, the submitted full runs ranged from about 30 minutes for \(K_3\) to a few hours for the Petersen graph; our new microbenchmark reports [INSERT SECONDS/ITERATION AND PEAK MEMORY].

## Reviewer 6KFF

Thank you. We agree that the paper should explain more clearly what is guaranteed, why the architecture is appropriate, and where it is likely to fail.

**What theory does and does not support.** Our guarantees concern three pieces: the empirical scalar constraint has a unique root; the homomorphism-density estimator is unbiased for a fixed graphon; and the displayed implicit formula is the exact derivative of the empirical constrained problem. Continuous neural graphons can approximate step graphons in \(L^1\), and
\[
|t(H,W)-t(H,U)|\le e(H)\|W-U\|_1,
\]
so representational approximation transfers directly to the motif objective. None of these facts gives global convergence for the nonconvex optimization, and we will state that limitation more prominently. The method is best suited to dense-graph problems with one monotone scalar constraint, moderate motif density, and a low-complexity block or geometric optimizer. It is less suitable for sparse limits, extremely rare motifs, large motifs under tight memory, multiple nonmonotone constraints, or landscapes with many competitive local minima.

**Why progressive sinusoidal features.** A step boundary requires increasingly high spatial frequencies for accurate approximation. The early, low-scale features provide coarse block geometry, while later high-scale features provide short paths that refine boundaries without forcing every preceding layer to preserve high-frequency information. The per-layer injection and the increasing frequency schedule play different roles; we agree that the original ablation did not isolate them completely. We have therefore added a matched [2-by-2 / LIST VARIANTS] comparison that changes (i) sinusoidal versus non-sinusoidal injected features and (ii) first-layer-only versus per-layer injection, while keeping scale and parameter count fixed; the existing constant-scale control separately tests the multiscale schedule. [INSERT RESULT.] We will also add a boundary-refinement visualization.

The \(d^{-1/2}\) initialization of residual matrices controls activation growth with fan-in, while the range of each row of \(U^{(\ell)}\) directly controls the initialized spatial frequency. Increasing \(s(\ell)\) therefore gives later layers access to progressively finer scales without increasing hidden-state magnitude.

**Wavelets.** Yes: the constraint solver and Monte Carlo estimator are representation-agnostic, and localized wavelet or Gabor features are plausible alternatives. We chose sinusoidal features because they are simple to differentiate and their frequency is controlled directly by \(U^{(\ell)}\). We will discuss wavelet INRs as an important comparison rather than claiming that sinusoids are uniquely suitable.

**Applications.** The intended application is mathematical discovery rather than a downstream node-classification task. The concrete practical outcome is already visible after submission. The learned odd-cycle structures led us to a universal Goodman-style theorem for every odd cycle, and the learned bipodal structures in the large-deviation problem led to a local theorem proving uniqueness and bipodality near the phase boundary for every \(d\)-regular pattern graph with \(d\ge2\). The latter describes the typical structure of dense Erdős-Rényi graphs conditioned on an upper-tail event and partially answers Chatterjee’s first open problem on nonconstant variational minimizers. Related computational uses include constrained dense-graph generation and rare-event importance-sampling proposals, but we will not claim downstream graph-ML performance that we have not evaluated.

## Reviewer BFdn

Thank you for identifying the central issues. We agree that the method should be positioned as a graphon-variational workflow with problem-specific adaptations, not as the first neural representation of a graphon, and that numerical candidates require independent checks.

**Novelty and Xia et al.** Xia et al. (2023) use a SIREN to reconstruct graphons from observed graphs with a Gromov-Wasserstein loss. Our setting has no observed target graphon: it searches directly over graphons to optimize constrained mathematical functionals. The specific contributions are the progressive per-layer encoding for sharp extremizers, the monotone constraint layer and its implicit derivative, and the symmetry-aware density estimator. We will add Xia et al., narrow our novelty statement, and report a parameter-matched SIREN backbone under the same optimization loop: [INSERT RESULT].

**Sinusoid versus injection.** We agree that the original controls do not fully identify the source of the gain. We have added a factorized comparison among [PLAIN RESNET], [NON-SINUSOIDAL PER-LAYER INJECTION], [FIRST-LAYER SINUSOIDAL ENCODING], [CONSTANT-SCALE PER-LAYER SINUSOIDAL ENCODING], and [FULL PROGRESSIVE PER-LAYER SINUSOIDAL ENCODING], with matched parameter counts and [N] seeds on [KNOWN TASK] and [DIFFICULT TASK]. [INSERT MAIN RESULT.] This separates periodic features, repeated injection, and progressive scale.

**Reliability and post-submission proofs.** We agree that a learned graphon is not a certificate. The intended workflow is candidate discovery followed by independent mathematics, and this has now occurred twice.

First, following the learned \(C_5/C_7\) structures, we proved that for every graphon \(W\) of edge density \(p\) and every odd \(m\ge3\),
\[
t(C_m,W)\ge p^m-p(1-p)^{m-1}.
\]
The bound is sharp at every balanced complete multipartite graphon. It is a universal lower envelope, not a proof of the exact optimizer away from those sharp densities; in particular, we retain “candidate” language for the displayed \(C_7\) graphons and for \(H_6\). A journal manuscript is in preparation, and an earlier proof architecture covering the nontrivial regimes has been checked modularly in Lean.

Second, motivated by the two-block outputs for \(\mathbf{(P2)}\), we proved the following independent structural result. For every \(d\)-regular \(H\) with \(d\ge2\) and every phase-boundary point with \(r\ne(d-1)/d\), there is a nontrivial open neighborhood in which, on the symmetry-breaking side, the large-deviation optimizer is unique up to relabelling and bipodal; its block parameters and optimal value are analytic in \((p,r)\). This supplies a mathematically provable qualitative description of nonconstant minimizers in a local regime, partially answering Chatterjee’s first open problem. It does not certify every Table 6 parameter, which is why we separately audit those numerical comparisons below.

**Lubetzky-Zhao comparison and numerical error.** We reevaluated every \(K_3\) upper-tail candidate on held-out samples, separately from training and calibration, and computed paired intervals for
\[
\Delta=h_q(W_{\mathrm{LZ}})-h_q(W_{\mathrm{ours}}).
\]
We also report cross-run variation and the held-out constraint residual. [INSERT TABLE OR COMPACT NUMBERS FOR ALL SIX CELLS.] Thus the smaller \(q=0.10\) improvements are [RESOLVED / NOT RESOLVED] relative to both integration error and optimization variability. We will restrict the “outperforms Lubetzky-Zhao” claim to \(K_3\). For \(C_4,C_5\), \(W_{\mathrm{LZ}}\) is only an available regular-graph reference, not a claimed optimum.

An even stronger independent check is possible because the learned profiles are close to bipodal. We fitted a low-dimensional bipodal graphon, enforced its constraint analytically, and evaluated both \(t(K_3,W)\) and \(h_q(W)\) by their exact finite polynomials: [INSERT FIT RESIDUAL AND OBJECTIVE GAP]. This certifies that the explicit feasible construction beats the reference without claiming global optimality.

**Run distribution and the 175-graph failures.** The main results now include [N]-seed distributions on [INSTANCES]. For the 11.8% suboptimal sweep cases, we compared additional restarts, longer training, and increased capacity on [SUBSET]. [INSERT WHETHER FAILURES ARE MAINLY OPTIMIZATION OR CAPACITY; DO NOT SPECULATE WITHOUT THIS TEST.]

**Structured parameterizations.** A sufficiently well-chosen structured family can often recover a solution after its form is known. The value of the neural search is that it does not require choosing in advance whether the answer is multipartite, diagonal/banded, circular-distance, or bipodal. We have added post-hoc structured fits and [SBM/SIREN] baselines on \(C_7\), \(H_6\), and triangle \(\mathbf{(P2)}\): [INSERT RESULT]. Agreement with a distilled construction validates interpretability rather than weakening the exploratory role of the network.

## Reviewer s6Ge

Thank you. We agree that the best-of-runs presentation obscured the reliability of the discovered structures and that conclusion levels should be labelled more explicitly.

**Seed, frequency, and permutation sensitivity.** We ran [N] independent initializations under the fixed main protocol on [KEY INSTANCES], and additionally varied the frequency schedule between \(s(\ell)=\ell\) and \(s(\ell)=2^{\ell-1}\). We report objective distributions, success rates, and fitted structural parameters after accounting for measure-preserving relabellings: [INSERT SUMMARY]. At fixed trained graphons, we also compared the identity estimator, the chosen symmetry set, and matched-cost alternatives over repeated batches. All are unbiased; the selected set changes variance and cost, not the target. [INSERT VARIANCE/TIME RESULT.] For cycles, the main estimator averages all coset representatives, so the choice of representatives does not change the symmetrized estimator.

**Population-level constraint error.** The solver enforces the constraint on its current batch, so empirical residual zero is not itself evidence of population feasibility. We now (i) calibrate \(c\) on an independent large sample, (ii) evaluate the constraint and objective on a disjoint sample or grid, and (iii) report the residual distribution produced by ordinary training-sized solver batches. Across [INSTANCES], the held-out residual was [INSERT MAX/MEDIAN/INTERVAL]. We will add this quantity to the main result tables.

**Cross-run uncertainty.** We now report mean/SD, median/IQR, best, and structural success rate rather than only a bootstrap interval for the selected run. For the triangle upper tail at \(q=0.10\), the paired improvement over \(W_{\mathrm{LZ}}\) was [INSERT] across seeds, with held-out 95% interval [INSERT].

**Analytic constructions and mathematical status.** The \(C_7\) appendix already converts the learned pattern into an explicit low-dimensional construction, but the manuscript did not clearly separate that candidate formula from a proof. Following these learned odd-cycle structures, we have since proved the universal Goodman-style lower bound
\[
t(C_m,W)\ge p^m-p(1-p)^{m-1}
\]
for all graphons and all odd \(m\ge3\), sharp at balanced complete multipartite graphons. This does not certify the exact \(C_7\) optimizer at every density, and the \(H_6\) structure remains conjectural. We have distilled \(H_6\) into [INSERT CIRCULAR-DISTANCE PARAMETERIZATION/FIT] so that it can be inspected independently.

For \(\mathbf{(P2)}\), the bipodal candidates have now led to a rigorous local theorem: near every nonexceptional point of the Lubetzky-Zhao phase boundary, on the symmetry-breaking side, the optimizer for every \(d\)-regular \(H\) with \(d\ge2\) is unique up to relabelling and bipodal. We will use the following labels consistently: “recovery of a theorem-backed optimum,” “candidate matching an independent lower bound,” and “numerically competitive candidate/counterexample to a reference construction.”

**Baselines and cost.** We extended the fixed-grid/SBM and SIREN baselines to [C7 INSTANCE], [H6 INSTANCE], and [P2 INSTANCE]: [INSERT RESULT]. The dominant per-iteration cost is approximately \(O(Nv(H)^2Ld^2+N|\mathcal S|e(H))\); training uses \(2^{12}\)-\(2^{16}\) samples, while \(2^{28}\) is only one-time final evaluation. Measured seconds/iteration and peak memory are [INSERT].

## Experiment priorities

### Priority 0: recover facts before launching jobs

1. Recover the exact original run count for every table/figure from logs. Do not infer four runs from the four learning rates.
2. Record seeds, learning rates, capacity, stopping epoch, hardware, and whether a final independent calibration of \(c\) was performed.
3. Correct the internal \(C_7,p=2/3\) reference value before any revision: the balanced complete tripartite value is \(14/243\approx0.05761317\), not \(0.05763169\). Avoid volunteering this unrelated typo in rebuttal unless a corrected table is discussed.

### Priority 1: most likely to move scores

1. **High-precision \(\mathbf{(P2)}\) audit.** For all six \(K_3\) upper-tail cells, evaluate each selected graphon and \(W_{\mathrm{LZ}}\) with common held-out samples. Report the paired entropy difference, its 95% interval, and the held-out constraint residual. Where possible, fit a bipodal graphon and evaluate its constraint and entropy analytically. This directly addresses the smallest \(q=0.10\) gaps.
2. **Standardized seed study.** Use at least 10 seeds for:
   - triangle \(\mathbf{(P2)}\), especially \(q=0.10,r\in\{0.4,0.5,0.6\}\);
   - \(C_7\) at one diagonal/banded density, preferably \(p=5/8\);
   - \(H_6\) at the reported novel-structure density;
   - one known benchmark such as \(K_3,p=7/9\).
   Report mean/SD, median/IQR, best, constraint residual, success rate, and structural-parameter variability.
3. **Population-gradient diagnostic.** Freeze representative checkpoints; use a very large reference batch; over repeated batches at \(N=2^{10},\ldots,2^{16}\), report gradient bias, relative norm error, and cosine similarity. This is much cheaper than retraining and directly answers Reviewer 1jpj.
4. **Runtime microbenchmark.** Report seconds/iteration and peak memory for \(N\in\{2^{12},2^{14},2^{16}\}\), \(d\in\{64,128,256\}\), and representative motifs \(K_3,C_5,C_7,H_6,\) Petersen. Full 20,000-epoch reruns are unnecessary.

### Priority 2: architecture and baselines

1. **Minimal factorized architecture study.** On one known and one hard task, run at least five seeds for:
   - plain ResNet;
   - non-sinusoidal per-layer coordinate injection;
   - first-layer-only sinusoidal encoding;
   - constant-scale per-layer sinusoidal encoding;
   - full progressive per-layer sinusoidal encoding.
   Match parameter counts and optimization budgets.
2. **Xia/SIREN baseline.** Keep the objective, solver, estimator, width, depth, and budget fixed; replace only the backbone with a parameter-matched SIREN. If feasible, also report the original smaller Xia architecture.
3. **Permutation audit.** At fixed graphons, compare estimator variance and wall time for identity, the chosen symmetry set, and matched-cost alternatives. Retrain identity versus the chosen set on one hard task if time permits.
4. **Selective baseline extension.** Add fixed-grid/SBM and SIREN results for \(C_7,p=5/8\), the main \(H_6\) case, and \(K_3\) \(\mathbf{(P2)}\) at \(q=0.10,r=0.5\).

### Priority 3: useful but lower rebuttal yield

- A wavelet/Gabor INR baseline.
- A full capacity sweep across every motif.
- Downstream graph-classification experiments.
- Broad reruns of all 175 graphs.

These are less likely to change the current decision than resolving the central robustness and \(q=0.10\) precision questions.
