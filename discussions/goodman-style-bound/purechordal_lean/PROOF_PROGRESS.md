# Pure-chordal graphon bound: proof audit

Status key: ✅ DONE · 🚧 WIP · ❌ TODO

| Milestone / principal lemma | Short description | Hardness | Status |
|---|---|---:|:---:|
| Standalone `purechordal_lean` project | Build against the read-only Mathlib installation without modifying `complete_lean`. | Medium | ✅ |
| `cliquePoly` algebra | Define $A_s(p)=\prod_{a<s}(1-a(1-p))$ and prove recurrence, positivity, and elementary bounds. | Easy | ✅ |
| Graphon and homomorphism density layer | Define measurable symmetric $[0,1]$-kernels, graph weights, finite-product hom densities, and clique densities. | Hard | ✅ |
| Hom-density bounds | Prove measurability, integrability, nonnegativity, and upper bounds by $1$. | Medium | ✅ |
| Regularisation $W_\varepsilon$ | Define $\varepsilon+(1-\varepsilon)W$ and prove the edge-count continuity estimate for hom densities. | Medium | ✅ |
| Local Gibbs inequality | Prove the bounded positive-density logarithmic inequality used by entropy gluing. | Hard | ✅ |
| Rooted pure clique-tree certificate | Encode equal-size clique bags, rooted parent order, covers, and the exact old-vertex/separator property. | Hard | ✅ |
| Separator-size lemmas | Prove every non-root separator has size $<r$, hence at most $r-1$. | Medium | ✅ |
| Finite product deficit inequalities | Prove the exactly-one-failure and incidence double-counting inequalities. | Hard | ✅ |
| Pointwise graph cube inequality | Prove the general edge-deletion/vertex-deletion cube inequality used for Moon–Moser. | Hard | ✅ |
| Coordinate relabeling invariance | Prove graph weights and hom densities are invariant under finite graph isomorphism. | Hard | ✅ |
| Weighted integral Cauchy–Schwarz | Prove $(\int A\eta)^2\le(\int A)(\int A\eta^2)$ directly from nonnegative quadratic integrals. | Hard | ✅ |
| One-vertex clique conditioning | Factor $K_{s+1}$ pointwise and prove $t_{s+1}=\int K_s\,\eta_s$. | Very hard | ✅ |
| Two-vertex missing-edge conditioning | Identify the $K_{s+2}$ minus one edge density with $\int K_s\,\eta_s^2$. | Very hard | ✅ |
| Clique conditional Cauchy–Schwarz | Derive $t_{s+1}^2\le t_s J_s$, where $J_s$ is the missing-edge clique density. | Hard | ✅ |
| Integrated general cube inequality | Integrate the pointwise cube inequality and express it as a hom-density inequality for edge/vertex deletions. | Hard | ✅ |
| Clique deletion symmetry | Identify every vertex-deleted term with $t_m$ and every edge-deleted term with the common missing-edge moment $J$. | Very hard | ✅ |
| Graphon Moon–Moser recurrence | Prove $m t_m^2\le t_{m-1}t_m+(m-1)t_{m-1}t_{m+1}$ for $m\ge2$. | Very hard | ✅ |
| Adjacent clique-ratio lower bound | From Moon–Moser and $p=t_2$, derive $t_j/t_{j-1}\ge1-(j-1)(1-p)$, including zero/positivity cases. | Very hard | ✅ |
| Clique-density polynomial lower bound | Deduce $t_r\ge A_r(p)$ under $p\ge1-1/(r-1)$. | Hard | ✅ |
| New-vertex partition | Prove the rooted certificate’s $N_i=C_i\setminus S_i$ form a partition of the graph vertices. | Hard | ✅ |
| Vertex-count identity | Prove $\|V(H)\|=mr-\sum_{i\ne\rho}\|S_i\|$. | Medium | ✅ |
| Edge-weight multiplicity identity | Prove $\prod_i\kappa_{C_i}=\kappa_H\prod_{i\ne\rho}\kappa_{S_i}$ pointwise. | Very hard | ✅ |
| Ambient clique-weight integral | Split finite product coordinates and prove $\int\kappa_A=t(K_{\|A\|},W)$ for every ambient vertex subset $A$. | Hard | ✅ |
| Equal-size clique separator marginals | Prove that equal-cardinality clique laws have identical marginals on a common subset. | Very hard | ✅ |
| Junction prefix bag-marginal invariant | Prove inductively that every inserted bag has its normalized clique law as marginal, while later fresh-coordinate extensions preserve earlier marginals. | Extreme | ✅ |
| Junction law has total mass one | Deduce that the completed normalized junction product integrates to one. | Hard | ✅ |
| Junction/graph pointwise factorization | Cross-multiply and cancel all conditional denominators to identify the junction law with the graph weight and separator clique weights. | Very hard | ✅ |
| Normalized graph/separator Gibbs densities | Define the normalized graph law and separator tilts, prove measurability, positivity, and total mass one. | Very hard | ✅ |
| Cross-multiplied clique-tree gluing | Prove $t(H,W)\prod_{i\ne\rho}t_{s_i}\ge t_r^m$, including vanishing densities. | Extreme | ✅ |
| Positive-kernel entropy gluing | Prove the gluing inequality first for strictly positive regularised graphons using the Gibbs lemma. | Extreme | ✅ |
| Remove regularisation | Pass $\varepsilon\downarrow0$ using the proved explicit hom-density continuity estimate. | Hard | ✅ |
| Certificate-form polynomial bound | Combine gluing, clique ratios, separator bounds, and vertex count to prove the clique-tree expression lower bound. | Very hard | ✅ |
| Chordal graph structural wrapper | Formalize chordality by its standard maximal-clique-tree characterization and convert uniform maximal-clique size into the analytic certificate. | Extreme | ✅ |
| One-bag colouring extension bijection | A prefix colouring extends uniquely by injecting the new bag vertices into the colours unused on its separator. | Very hard | ✅ |
| Prefix-colouring recurrence | Prove the next-bag count is multiplied by $(q-s_i)_{r-s_i}$ and iterate it over the rooted clique tree. | Very hard | ✅ |
| Chromatic-polynomial factorisation | Construct the factored `Polynomial ℝ`, and prove $\chi_H(q)=\prod_i(q-s_i)_{r-s_i}$ by its proper-colouring count at every natural $q$. | Extreme | ✅ |
| Certificate/chromatic identity | Prove the analytic certificate equals $(1-p)^{\|V(H)\|}\chi_H(1/(1-p))$ for $p\ne1$. | Very hard | ✅ |
| Final stated theorem | Prove both the denominator-free bound and its chromatic-polynomial form for connected chordal graphs with all maximal cliques of size $r$. | Extreme | ✅ |
| Diamond certificate and bound | Certify $K_4$ minus one edge as two triangles glued along an edge and specialize the polynomial bound. | Hard | ✅ |
| Goldner–Harary certificate and bound | Certify the standard 11-vertex graph by its eight maximal tetrahedra and prove $t(GH,W)\ge p(2p-1)(3p-2)^8$. | Very hard | ✅ |
| Balanced multipartite extremizer | At $p=1-1/k$, compute the balanced complete $k$-partite graphon density, prove exact attainment, and prove minimality among graphons of that edge density when $r\le k$. | Very hard | ✅ |
| Leaf API layout | Keep both final theorems (`pureChordal_chromaticPolynomial_lower_bound`, `pureChordal_balancedMultipartite_minimal`) in `Main.lean`, the two graph corollaries in `Example.lean`, and make `Example.lean` the only direct importer of `Main.lean`. | Medium | ✅ |
| Soundness audit | Full root build; no `sorry`, `admit`, declared axioms, or `native_decide`; key theorems use only standard Lean axioms; no tracked `complete_lean` diff. | Medium | ✅ |
