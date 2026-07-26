### How many runs

For every experiments, we repeated the experiment once for each hyperparameter configuration, which sweeps over two activation functions ($\sin$ and $\mathrm{GeLU}$) and four learning rates $10^{-3}, 3 \times 10^{-4}, 10^{-4}, 3\times 10^{-5}$, total 8 configurations for each experiments. 

### Property & Numerical Stability of implicit gradient



### Connection between the KL-divergence and the large deviation problem



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

We tested the ... on non-neural baselines, i.e., parameterising graphon $W$ as a linear combinations of basis functions.
We found out that none of these representations match with the bound requirements $W(x, y) \in [0, 1]$, and invalidates the constraints. 
We also further tested if these representations are expressive enough to represent the optimal solution, and found out that the optimal solution being either $0$ or $1$ makes...

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
- Under assumption that the optimal solution is bipodal, we can reduce the problem to a 4-dimensional optimisation problem, and use constrained optimisation methods to find the solution. We report the results:...

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
- 