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

### Too large sample size

$2^{28}$ is only used for final evaluation, while training uses $2^{12}$-$2^{16}$ samples. 
As estimated homomorphism densities are bounded by $[0, 1]$, by standard ...

### Comparison to Graphon-INR literatures

Graphon learning is a problem in network analysis, where one aims to find underlying structure given finite graphs, as social networks. 
Specifically, we are given a set of graphs $\{G_i\}_{i=1}^N$ that are assumed to be sampled from a common underlying graphon $W$, and the goal is to estimate $W$ from these samples.
These problems were tested against on application for mixup-like data augmentation in graphon learning, and the synthetic graphons. 
As their main purpose is reconstructing the graphon that is similar to true graphon, they often fails to sharp details on the true graphon, for instance, see Figure 3(b) and Figure 9 in [1].

[1] Scalable Implicit Graphon Learning, Ali Aziz pour, Nicolas Zilberstein, and Santiago Segarra, AISTATS 2025.

### Some theoretical idea when works well or not? 

We don't have clear theoretical idea when it works well or not, but we have some empirical observations.
Often, the problems we study have trivial solutions, for instance, the constant graphon $W \equiv p$ or $W \equiv q$ are the trivial solutions for (P1) and (P2) respectively.
When these trivial solutions are comparable to the optimal solution (the difference of objective is less than 1e-5), then the trained model often converges to the trivial solution. 

### What about wavelet basis?

We tested the four non-neural representation methods, Fourier basis, Haar wavelet basis, Legendre polynomial basis, and Bernstein polynomial basis.
Throughout the experiments, all four methods failed to satisfy the constraint of $W(x, y) \in [0, 1]$ and gave invalid resulting values like $t(K_3, W) \approx -44752$.
We also performed supervised training on these methods, i.e., we trained the model to fit the optimal solution, and except for wavelet basis, all other methods still failed to satisfy the constraint of $W(x, y) \in [0, 1]$ (45% of the input were invalid).
For wavelet basis, while it satisfies the constraint, it fails to represent the optimal solution accurately mostly due to the discrete boundary, and resulted $t(K_3, W) = 0.444238$, which is worse than fixed grid SBM solution ($t(K_3, W) = 435817$).

### Practical Application

- Some extremal graph theory often helps, as expander graph does. But our model is limited to the dense problems, and cannot be applied to this sparse problem.
- The large deviation analysis is often related to sociological science where...

### The P2 error seems too large. 

We use 64-bit floating point numbers for the results, therefore the difference is large enough to be significant. 

### Why does 11.8% suboptimal error happens?

Among 11.8% suboptimal error, ... was due to converging to local optimum, and ... was due to training instability, as diverging to NaN. 

### What is power of NN?

For tree-based baselines or fixed-grid SBM, it is generally hard to change the decision boundary, and almost all $\{0, 1\}$ solutions are local optimum that can't be escaped without reset. 
Therefore, these methods strongly depend on the initialisation, and often can't escape the geometry of initialisation solution.
On the other hand, neural network can easily change the decision boundary, and excels to represent the optimal solution by jointly optimising the value of each region and the boundaries.
The idea of parameterising the decision boundary together (second and third figure in Figure 15), fails due to the fact that the optimisation landscape being very sharp, therefore converges to constant solution always.

We also note that all the non-neural baselines were expressive enough to represent the optimal solution.

Therefore, we view the main benefit of neural network is that it can flexibly tune the solution in terms of both value and boundary, while having favorable optimisation landscape.

### No sinusoidal encoding baseline

TODO

### P2 has no good lower bound?

Up to our knowledge, computational lower bound for problems like P2 is not known.
There are some empirical tests that can be used to check comparable lower bound:
- Using some advanced sampling methods to directly sample from the conditional distribution $G \sim G(n, p) | t(K_3, G) \ge r^3$ and compare the sampled finite graph with the trained model. However, this is not feasible for large $n$ and $r$.
- Under assumption that the optimal solution is bipodal, we can reduce the problem to a 4-dimensional optimisation problem, and use constrained optimisation methods to find the solution. We report the results: TODO

### How much dependency on the initialisation, frequency schedule, and MC permutations? 

TODO

### How many error in population level constraint, from the solver?

TODO

### Uncertainty estimate on training?

TODO

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
- TODO

### LZ is only designed for K3, not C4 or C5

While LZ construction is only designed to prove non-optimality of constant graphon not as optimal solution, it is not limited to $K_3$ but is applicable to any d-regular graphs.