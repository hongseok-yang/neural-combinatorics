# General $C_{2k+1}$ odd-cycle graphon lower bound: progress and obstructions

> **STATUS UPDATE (2026-05-31, after the $C_{13}$ frontier split).** This
> report began as the output of a multi-agent *exploration* run before the
> collaborator's general results were available. Several "approaches explored"
> below are now **proven theorems**, verified and incorporated into `paper.tex`
> §9:
> - The hub-coupling positivity lemma and the universal bound
>   $t(C_m,W)\ge p^m-\Tr(A^m)$, hence the **norm-safe** criterion $\|A\|\le q$
>   (subsumes regular graphons).
> - The **rank-one complement** and **equal disjoint clique complement** all-$k$
>   theorems.
> - The exact path-cycle identity and the corrected spectral bottleneck
>   $\Psi_m\ge\Tr(A^m)-pq^{m-1}$ (with a counterexample to the naive modewise
>   target).
> The old $C_{13}$ partial result is now superseded: `paper.tex` §8 closes
> $C_{13}$ by combining the path-certificate range, the triangle-spectral range,
> and the positive-spectrum/frontier split. What survives below as genuinely
> *open* is the asymptotic obstruction analysis (§4–§5 here): the
> $\delta_m\sim9/(4m^2)$ ceiling, the unequal-clique target, and the
> near-bipartite/$C_5$ route. Read those sections; treat §2–§3 as historical
> except where explicitly refreshed below.
>
> **New general-case attack log (2026-05-31).** The exploratory checker
> `general_odd_cycle_attack.py` starts the general case directly rather than
> moving cycle-by-cycle to $C_{15}$. It carries out the two most promising
> extensions of the $C_{13}$ work:
>
> 1. **Uniform frontier split.** In the true triangle-spectral gap, the
> no-frontier case $\lambda_{\max}(A)\le q$ is already closed by the
> positive-spectrum-safe criterion. In the one-frontier case
> $\alpha=\lambda_{\max}(A)>q$, the trace-square budget gives at most one
> frontier eigenvalue and bounds every other positive mode by
> $\tau(q)=\sqrt{q(1-2q)}$. A restricted-domain scan of the general path
> certificate finds the linear polynomial $P_q^{(m)}$ positive for
> $m=13,15,\dots,23$, but the quadratic kernel $K_2$ turns negative at the
> frontier-safe boundary from $m=21$ onward. The first negative samples are
> $m=21$ with $q=0.4941793298$, $\alpha=q+10^{-6}$,
> $\beta=\tau(q)=0.0758479383$, where $K_2\approx-2.85\cdot10^{-4}$, and
> $m=23$ with $q=0.4951827227$, $\alpha=q+10^{-6}$,
> $\beta=0.0690714482$, where $K_2\approx-2.19\cdot10^{-4}$. Thus the
> $C_{13}$ split does **not** iterate verbatim; the next version must retain
> the deletion gap $x_{m-1}-c_m$, add coupling restrictions beyond marginal
> spectral boxes, or use a different structural input.
>
> 2. **Near-bipartite/$C_5$ input.** Replacing triangle density by a hypothetical
> sharp lower bound for $t(C_5,W)$ at fixed edge density is still the strongest
> external-input route, but the earlier "uniform $\delta_m\gtrsim0.12$" optimism
> was too strong for the spectral-closure argument alone. For the equal-halves
> near-bipartite two-block graphon with cross density $1$, one internal fill
> $4\eps$, and $p=1/2+\eps$,
> \[
>     B_5(\eps)=\frac58\eps+10\eps^3+32\eps^5,\qquad
>     B_5(\eps)-\big((1/2+\eps)^5-(1/2-\eps)^5\big)
>       =5\eps^3(1+6\eps^2).
> \]
> The conditional $C_5$ spectral window covers all of $[1/2,2/3]$ in the tested
> range through $m=501$, but for large $m$ the first near-zero window shrinks:
> high-precision roots give $\delta_{1001}=0.01347037$,
> $\delta_{2001}=0.00646091$, and $\delta_{20001}=0.00111765$, with
> $m^{2/3}\delta_m$ trending toward the leading balance
> $(5/8)^{2/3}$. The $C_5$ route is therefore not a black-box uniform spectral
> closure; its real promise is structural, namely proving a near-bipartite
> reduction/minimiser theorem and then checking the resulting two-block (or
> few-block) inequality directly.
>
> **Deletion-retaining one-frontier execution (2026-05-31).** The next script
> `general_frontier_deletion_retaining.py` keeps the exact deletion gap in the
> simplest spectral model with one frontier mode and one safe positive mode,
> \[
>       T_U=\begin{pmatrix}
>       q&b_1&b_2\\ b_1&\alpha&0\\ b_2&0&\beta
>       \end{pmatrix},
>       \qquad
>       \alpha>q,\qquad
>       \alpha^2+\beta^2+2(b_1^2+b_2^2)\le pq .
> \]
> The first check is important: the negative $K_2$ obstruction is not just an
> artefact of the older rectangular box. Even on the sharp boundary
> $\beta^2=pq-\alpha^2$, $K_2$ remains negative; for example at $m=21$,
> $q=0.4941793299$, $\alpha=q+10^{-3}$,
> $\beta=0.0690184836$, one gets $K_2=-2.41\cdot10^{-4}$.
>
> The retained-deletion scan then shows the next missing constraint. If we only
> impose spectral and $C_2$ budgets, the abstract arrowhead model can have
> $x_{m-1}-c_m<0$, hence is outside the graphon world (actual nonnegative
> graphons satisfy the deletion inequality). After imposing the necessary
> graphon-like constraint $x_{m-1}-c_m\ge0$, the coarse two-mode scans found no
> violation. The smallest retained defects found were positive:
> $1.88\cdot10^{-9}$ for $m=21$ and $4.64\cdot10^{-10}$ for $m=23$. Even among
> samples with genuinely active negative $K_2$ (both $b_1^2,b_2^2>0$), the worst
> retained defects were positive: $3.59\cdot10^{-9}$ for $m=21$ and
> $6.49\cdot10^{-10}$ for $m=23$.
>
> Thus the next concrete theorem to try is no longer "restricted $K_2\ge0$."
> It is the finite-dimensional implication
> \[
>   \alpha>q,\quad 0\le\beta^2\le pq-\alpha^2-2(u+v),\quad
>   x_{m-1}-c_m\ge0
>   \quad\Longrightarrow\quad
>   \Phi_m+(x_{m-1}-c_m)\ge0
> \]
> in the two-mode variables $(q,\alpha,\beta,u,v)=(q,\alpha,\beta,b_1^2,b_2^2)$,
> followed by an extension from one safe atom $\beta$ to the full safe spectral
> measure. This looks like the best current laboratory for the general case:
> it is false without the deletion constraint, true in the first coarse scans,
> and close enough to the actual obstruction to teach us what extra information
> the path certificate was missing.
>
> **Finite-dimensional target search (2026-05-31).** The follow-up script
> `general_frontier_finite_dimensional_search.py` normalises the two-mode
> feasible set to a five-dimensional box and runs biased random search plus
> coordinate refinement. It again found no counterexample for
> $m=21,23,25,31$ (and an ad hoc pass at $m=41$ behaved the same way). The tight
> feasible minima collapse to the zero-coupling edge $u=v=0$, where
> \[
>       \Phi_m=0,\qquad
>       x_{m-1}-c_m
>       =t(C_m,1-U)-\bigl(p^m-pq^{m-1}\bigr)
>       =pq^{m-1}-\alpha^m-\beta^m.
> \]
> Thus the deletion-gap condition itself gives the desired inequality at the
> apparent minimum. Active coupled points stayed positive; representative
> refined active minima for the retained defect were
> $3.19\cdot10^{-11}$ at $m=21$, $1.17\cdot10^{-12}$ at $m=23$,
> $1.64\cdot10^{-12}$ at $m=25$, $4.09\cdot10^{-14}$ at $m=31$, and
> $1.01\cdot10^{-17}$ in the ad hoc $m=41$ pass. This suggests a sharper
> subtarget: in the two-mode model, prove that under the square-budget and
> deletion-gap constraints the minimum of the retained defect occurs on the
> zero-coupling boundary.
>
> **Sharpened retained-defect reduction (2026-05-31).** The tempting stronger
> assertion $\Phi_m\ge0$ is false in the long-cycle regime, so the deletion term
> is not cosmetic. The script `general_frontier_retained_boundary.py` records
> high-precision two-mode witnesses satisfying the square budget with
> $\Phi_m<0$ but positive deletion gap and positive retained defect:
> \[
> \begin{array}{c|c|c|c}
> m&\Phi_m&x_{m-1}-c_m&
> t(C_m,1-U)-\bigl(p^m-pq^{m-1}\bigr)\\ \hline
> 301&-4.01\cdot10^{-88}&5.22\cdot10^{-88}&1.21\cdot10^{-88}\\
> 501&-1.76\cdot10^{-141}&1.76\cdot10^{-141}&4.08\cdot10^{-145}
> \end{array}
> \]
> Thus the right sharpened theorem is boundary, not global, positivity.
>
> What we can prove exactly is the monotonicity that forces this boundary
> reduction. Let
> \[
>       D_m(u,v)=t(C_m,1-U)-\bigl(p^m-pq^{m-1}\bigr)
> \]
> in the two-mode arrowhead model, and conjugate the complement matrix by the
> sign flip on the leaves:
> \[
>       N=\begin{pmatrix}p&b_1&b_2\\ b_1&-\alpha&0\\ b_2&0&-\beta\end{pmatrix}.
> \]
> Since $p\ge1/2\ge\alpha,\beta$, the matrix $N^2$ is entrywise nonnegative:
> its hub--leaf entries are $b_i(p-\lambda_i)\ge0$, and the other entries are
> immediate. For odd $m$, $m-1$ is even, hence
> \[
>       (N^{m-1})_{0i}=((N^2)^{(m-1)/2})_{0i}\ge0.
> \]
> Differentiating the trace with respect to $u_i=b_i^2$ gives
> \[
>       \frac{\partial D_m}{\partial u_i}
>       =\frac{m}{b_i}(N^{m-1})_{0i}\ge0
>       \qquad (b_i>0),
> \]
> with the boundary case obtained by continuity. Therefore the retained defect
> is coordinatewise nondecreasing in the coupling weights. Consequently a
> negative minimum subject to the square budget and deletion condition
> $x_{m-1}-c_m\ge0$ cannot occur at an interior point with
> $x_{m-1}-c_m>0$: decreasing a positive coupling preserves feasibility for a
> short time and cannot increase $D_m$. Such a minimum must be either at
> $u=v=0$ or on the deletion frontier $x_{m-1}=c_m$. The zero-coupling case is
> harmless, because there $D_m=x_{m-1}-c_m=pq^{m-1}-\alpha^m-\beta^m$.
>
> The remaining finite-dimensional target is therefore the exact boundary
> statement
> \[
>   \alpha>q,\quad \alpha^2+\beta^2+2(u+v)\le pq,\quad x_{m-1}=c_m
>   \quad\Longrightarrow\quad
>   \Phi_m=D_m\ge0.
> \]
> Boundary scans in `general_frontier_retained_boundary.py` found no violation
> at $m=21,101,301$; the smallest sampled boundary values of $\Phi_m$ were
> $1.86\cdot10^{-10}$, $1.39\cdot10^{-34}$, and $1.01\cdot10^{-93}$,
> respectively. This is now the precise algebraic target.

## 1. The open problem

**Conjecture.** For every odd integer $m = 2k+1 \geq 3$ and every graphon $W$ with edge density $p = t(K_2, W)$,
$$t(C_m, W) \;\geq\; p^m - p(1-p)^{m-1}.$$
The bound is tight at $p = 1 - 1/j$ for integers $j \geq 2$, attained by the balanced complete $j$-partite graphon. The cases $m = 3$ (Goodman, 1959), $m = 5$ (folklore for $p \leq 1/2$; Bennett–Dudek–Lidický–Pikhurko 2020 at the discrete densities $p = 1 - 1/k$), and now $m = 7, 9, 11, 13$ (current paper) are proved for all $p \in (0,1)$. The conjecture is **open for every odd $m \geq 15$**.

The $C_9$ and $C_{11}$ proofs are hybrids of (i) a complement path-certificate covering $p \geq \rho_m$, and (ii) a spectral closure using triangle density covering $1/2 < p \leq \rho_m$. This report assesses whether the hybrid scales to $m \geq 13$.

## 2. Approaches explored

**Generalize the spectral closure.** The reduction-to-$\ell = p$ step of §6.2 (monotonicity of $G(\ell)$) extends verbatim and rigorously to every odd $m \geq 5$: implicit differentiation gives $\alpha' = \ell^{m-1}/\alpha^{m-1}$, and $G'(\ell) \geq 3\ell^2((\ell/\alpha)^{m-3} - 1) > 0$ uniformly. However, Taylor analysis at $p = 1/2 + \varepsilon$ shows the spectral closure window $\delta_m$ shrinks as $\delta_m \sim 9/(4m^2)$, with hard ceiling $\delta_m \leq 9m/(4(m-2)^3)$. Bisection gives $\delta_{13} \approx 0.01559$, $\delta_{15} \approx 0.01166$, etc.

**Generalize the path-certificate.** The path-certificate machinery generalizes cleanly to $C_{13}$, yielding $\rho_{13} = 519/1000$ certified by exact Bernstein subdivision. A **closed-form formula** was discovered for the linear polynomial $P_q^{(m)}(\lambda)$: coefficient of $\lambda^j$ is $a_j(q) = (-1)^j m(1-q)^{m-2-j} + mq^{m-2-j} - (m-2-j)q^{m-3-j}$. Numerical thresholds $q_m^*$ for $m \leq 23$ show non-monotone behavior, stabilizing around $0.479$ — the path-certificate gap $1/2 - q_m^*$ does **not** shrink to zero.

**Reduce to the regular case.** Numerical evidence on step-graphons up to size 8 supports $\inf_W t(C_m, W) = \inf_{W\ p\text{-regular}} t(C_m, W)$, but no reduction technique tested (constant-averaging, convexity, rearrangement) gives a rigorous proof. The functional $W \mapsto t(C_5, W)$ is **not convex** on the edge-density slice. The reduction appears as hard as the original conjecture.

**Alternative inputs.** Spectral moments are cycle densities $\mathrm{Tr}(T^r) = t(C_r, W)$, so higher-clique density theorems (Reiher's $K_r$ result) **cannot** be plugged in. A sharp $t(C_5, W) \geq t(C_5, T(2;c))$ Turán-type bound, if proved, would dramatically widen the near-bipartite spectral window for each fixed moderate $m$, but the 2026-05-31 high-precision check shows that the window still shrinks like $m^{-2/3}$ asymptotically under the same spectral-closure mechanism. Inductive bootstrap on the conjecture fails: the linear-$\varepsilon$ coefficient $(r-1)/2^{r-2}$ of the conjectured input is strictly less than the required $r(m-1)/(m \cdot 2^{r-2})$ for $r < m$.

**Inductive structure.** The closed form for $a_j(q)$ admits a rational expression $P_q^{(m)}(\lambda) = m(1-q)[\psi_{m-2}(p,\lambda) - \phi_{m-2}(q,\lambda)] + g_m(q,\lambda)$. No clean polynomial recurrence $P_q^{(m+2)} = (\text{simple})\cdot P_q^{(m)} + (\text{sign-definite})$ exists. The inductive content lives in the coefficient formula, not in a multiplicative recurrence.

**Literature scan.** BDLP (CPC 2020) handles $C_5$ at discrete $p = 1 - 1/k$ via flag algebras. Reiher (JCTB 2016) handles all odd cycles **under the stronger local density hypothesis**. Kim–Lee (JCTB 2024) prove the symmetric commonality version $t_H(W) + t_H(1-W) \geq \ldots$. No published result handles $C_{2k+1}$ at continuous $p \in (0,1)$ for $k \geq 3$, so the paper's $C_7, C_9, C_{11}$ results are new beyond the state of the art.

## 3. Verified concrete progress

The following claims **survived adversarial verification** (numerical, symbolic, and source cross-check):

- **$G'(\ell) > 0$ uniformly for $m \geq 5$.** The spectral closure's monotonicity step generalizes rigorously to every odd $m \geq 5$, with strict inequality $G'(\ell) > 3\ell^2((\ell/\alpha)^{m-3} - 1) > 0$ on the subset where $\Delta \geq 0$. This is unconditional and ready to use.

- **Leading Taylor coefficients (modulo a sign correction).** $\Theta(p) - (p^3 - \alpha_0^3) = (3/(2m))\varepsilon + O(\varepsilon^2)$ and $\Delta_0 = ((m-2)/m)\varepsilon + O(\varepsilon^2)$. (Adversarial check flagged a $-3/4 \cdot \varepsilon^2$ coefficient that was omitted from the proof sketch but does not affect leading-order conclusions.)

- **Leading-order critical $\delta$.** $\delta_{\text{lead}}(m) = 9m/(4(m-2)^3)$, with $m^2 \delta_m \to 9/4$. This is the **hard asymptotic ceiling** of the present spectral closure.

- **Exact bisection values.** $\delta_{13} = 0.01559293506$, $\delta_{15} = 0.01166307611$, $\delta_{17} = 0.009018528186$, $\delta_{19} = 0.007164963662$ (verified independently to 80-digit precision).

- **Gap-width comparison.** $G_9 = 3/2000$, $G_{11} = 3/200$, a $10\times$ jump in one step, against spectral closure shrinking by $\delta_{11}/\delta_9 \approx 0.68$.

- **$\rho_{13} = 519/1000$ certified.** Exact rational Bernstein subdivision certifies the $C_{13}$ path-certificate range $q \in [0, 481/1000]$ in $\approx 60$s. This is **a fully rigorous new result** ready to be packaged.

- **Closed-form $P_q^{(m)}$ for all odd $m$.** Verified symbolically against $m = 5, 7, 9, 11$. Provides a uniform formula previously unavailable.

- **The old $C_{13}$ hybrid gap was real, but is now closed by a third ingredient.** The triangle-spectral side gives only $\delta_{13}=0.01559\ldots$, while the path-certificate side begins at $p=519/1000$. The missing band was not closed by those two techniques alone; it is closed in `paper.tex` §8 by the positive-spectrum/frontier split.

- **BDLP/$C_5$ equivalence.** $(p^5 - p(1-p)^4)/10$ matches BDLP's explicit polynomial at $p = 1 - 1/k$ for all $k \geq 3$; the present results strictly extend BDLP from discrete to continuous $p$.

**No proof of the general conjecture was obtained.** The $C_{13}$ case is now closed, but the classical two-part hybrid still has the same asymptotic obstruction for longer cycles.

## 4. Structural obstructions

The general case is hard for **three interlocking reasons**:

**(O1) Quadratic decay of the spectral window.** The slack $\Theta(p) - (p^3 - \alpha_0^3)$ opens linearly in $\varepsilon$ with coefficient $3/(2m) \to 0$, while the deficit $\Delta_0^{3/2}$ opens like $\varepsilon^{3/2}$ with $\Theta(1)$ coefficient $((m-2)/m)^{3/2} \to 1$. Solving the leading balance forces $\delta_m \sim 9/(4m^2)$. This is **intrinsic** to using triangle density + $L^2$-to-$L^3$ comparison: no manipulation within these inputs can change the $1/m^2$ scaling.

**(O2) Path-certificate gap does NOT shrink.** Numerical thresholds $q_m^*$ for the path-certificate stabilize around $0.479$ for $m \geq 17$, giving a gap $1/2 - q_m^* \approx 0.021$ uniformly. So the spectral side must close an interval of essentially **constant width** $\geq 0.02$ at every $m$, but the spectral side itself shrinks like $1/m^2$. The two sides diverge: the **crossover already occurs at $m = 13$** ($G_{13} \geq 0.019$ vs $\delta_{13} = 0.0156$).

**(O3) No usable stronger input from cliques.** Spectral moments are $\sum \lambda_i^r = t(C_r, W)$, **not** $t(K_r, W)$. Reiher's clique density theorem cannot be plugged in; the only meaningful upgrade is a sharp $t(C_r, W) \geq t(C_r, T(2;c))$ bound for odd $r \geq 5$, which is itself open.

A subtler obstruction: at $m \geq 17$ the quadratic kernel $K_2$ in the path-certificate decomposition becomes the **binding** Bernstein constraint on the full $[0, 1/2]$ box, requiring the certificate to be restated on the truncated box $[0, 1 - \rho_m]$.

## 5. Current most promising next directions

Ranked by feasibility after the 2026-05-31 general scan:

1. **Deletion-retaining one-frontier certificate.** The $C_{13}$ frontier split remains the most concrete general mechanism, but the deletion-free restricted path certificate fails by $m=21$. The right next algebraic target is therefore not "prove the same $K_2\ge0$ on a smaller box"; it is to keep the deletion gap $x_{m-1}-c_m$ (or an equivalent coupling term) while imposing the one-frontier spectral support restriction. This is the most feasible continuation because all variables are already identified: one frontier atom $\alpha>q$, all other positive modes at most $\tau(q)=\sqrt{q(1-2q)}$, and the defect is concentrated in the discarded deletion term.

2. **Near-bipartite structural reduction.** The numerical minimiser near $p=1/2$ is near-bipartite, and the two-block near-bipartite family itself satisfies the Goodman target in every tested odd length. A sharp $C_5$ Turán-type input would be a strong fixed-$m$ spectral tool, but not a uniform all-$m$ black box; the more promising version is structural: prove that a minimiser with $p=1/2+\eps$ and small $\eps$ is close to the equal-halves near-bipartite model, then solve the resulting low-dimensional inequality directly.

3. **Unequal multipartite reduction away from $1/2$.** The rank-one, equal-clique, and two-value multipartite cases are settled. The remaining high-density finite-dimensional target is the simplex-to-two-value reduction for unequal disjoint clique complements. This would not handle the near-bipartite minimiser, but it would remove one large class of possible obstructions and isolate the problem near $p=1/2$.

## 6. Current concrete next steps

- **Build the deletion-retaining frontier polynomial.** Modify the path-cycle checker so that, after splitting off a single frontier atom, it keeps the exact deletion surplus instead of dropping it. The first diagnostic target is $m=21$, where the deletion-free $K_2$ value is already negative by about $2.85\cdot10^{-4}$.

- **Turn the near-bipartite model into a lemma.** For the equal-halves graphon with cross density $1$ and one internal fill $4\eps$, write
  \[
      t(C_m)=\bigl(\eps+\sqrt{\eps^2+1/4}\bigr)^m
             +\bigl(\eps-\sqrt{\eps^2+1/4}\bigr)^m
  \]
  for odd $m$, then prove this is at least $p^m-p(1-p)^{m-1}$ on
  $0\le\eps\le1/6$. A coefficient/Sturm certificate after clearing
  denominators looks realistic.

- **Stress-test the structural reduction.** Numerically optimise step graphons
  near $p=1/2$ for several larger odd $m$ and record whether all minimisers
  collapse to the near-bipartite two-block form. The key analytic hint to
  exploit is $\lambda_{\min}(T_W)\ge-1/2$ with near-equality forcing
  near-bipartiteness.

**Current bottom line.** No proof of the general conjecture was found, but the
first general pass clarified the fork. A verbatim $C_{13}$ frontier certificate
breaks at the quadratic kernel by $m=21$, so the spectral route must retain
deletion information or extra coupling constraints. The near-bipartite route is
still the best structural bet, but a sharp $C_5$ input alone does not give a
uniform constant-width all-$m$ spectral closure.

## 7. Historical 2026-05-30 directions (superseded)

Ranked by feasibility:

1. **Compute $C_{13}$ rigorously, accepting a marginal gap.** The closed-form $P_q^{(13)}$, the certified $\rho_{13} = 519/1000$, and the spectral $\delta_{13} = 0.01559$ leave a residual interval $q \in (481/1000, 485/1000)$ of width $\approx 0.004$ uncovered. Try to close it via (a) sharpening the path-certificate by truncating $K_2$ to the smaller box (likely cheap, $\sim$1 day), or (b) refining the spectral closure by tracking $O(\varepsilon^2)$ corrections currently dropped. **Most feasible**: the hard work (Bernstein + bisection) is already done, only one of the two sides needs a $\sim 25\%$ improvement.

2. **Prove a sharp $t(C_5, W) \geq t(C_5, T(2;c))$ Turán bound on $p \in [1/2, 2/3]$.** This would replace the triangle input and yield $\delta_m \geq 0.122$ **uniformly in $m$**, closing the gap for every odd $m$ at once given any path-cert with $\rho_m \leq 0.62$. **Highest payoff but technically hardest**: requires an odd-cycle analog of Razborov–Reiher. Flag algebras may give a discrete-$p$ version first.

3. **Prove the regularity reduction directly.** Numerical evidence strongly suggests $\inf_W t(C_m, W) = \inf_{p\text{-regular}} t(C_m, W)$, and the regular case is already handled in §3.2. A Lagrange/Euler–Lagrange analysis of stationary $W$ on the edge-density slice may force step-structure. **Medium feasibility**: an honest attempt has not yet been made; if it works, it unlocks the whole conjecture.

## 8. Historical concrete next steps (superseded)

- **Commit the $C_{13}$ infrastructure.** Save `/tmp/c13_paper_style.py` as `discussions/goodman-style-bound/odd_cycle_c13_checker.py` and write a working note `odd_cycle_c13_working_note.tex` documenting $\Phi_{13}$, $\rho_{13} = 519/1000$, and the closed-form $P_q^{(m)}$.

- **Close the residual $C_{13}$ window.** Adapt the section-7.1 scalar inequalities (the $C_{11}$ constants $139/100$ and $9/11$) to $m = 13$ with $\alpha_0 = (pq^{12})^{1/13}$, and check whether the analog of the $C_{11}$ Sturm-certified margin survives at $\varepsilon = 19/1000$.

- **Cite the literature properly.** Add citations to BDLP (arXiv:1803.00165, CPC 2020), Reiher (arXiv:1604.06833, JCTB 2016), Kim–Lee (arXiv:2210.00977, JCTB 2024), Razborov triangle (Annals 2008), and Reiher clique density (Annals 2016). Frame the paper's $C_7, C_9, C_{11}$ continuous-$p$ results as the new state of the art.

- **Stress-test the regularity reduction.** Numerically refine the $n = 4..8$ step-graphon experiments to $n = 10, 12$ at high precision and check whether $\inf$ is still attained at a $p$-regular two-block.

- **Investigate the sharp $C_5$ Turán bound.** Even a partial result (e.g., for $p$ in a sub-interval, or with a controlled lower-order loss) would dramatically widen $\delta_m$ uniformly. This is the highest-leverage open subproblem identified by this investigation.

- **Update `SESSION_STATE.md`** with the verified status: $C_{13}$ unproved as of this report, residual gap $\approx 0.004$ in $q$, closed-form $P_q^{(m)}$ in hand, and the structural ceiling $\delta_m \leq 9m/(4(m-2)^3)$ documented.

**Bottom line.** No proof of the general conjecture was found. The hybrid strategy that proved $C_7, C_9, C_{11}$ has a hard structural ceiling: spectral closure window $\sim 1/m^2$, path-certificate gap $\sim$ constant, and the two cross at exactly $m = 13$. Either a sharper external input ($C_5$ Turán bound) or a structural shortcut (regularity reduction) appears necessary to push beyond $m = 11$.
