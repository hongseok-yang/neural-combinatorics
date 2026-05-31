# General $C_{2k+1}$ odd-cycle graphon lower bound: progress and obstructions

> **STATUS UPDATE (2026-05-30, post-incorporation).** This report was the output
> of a multi-agent *exploration* run before the collaborator's general results
> were available. Several "approaches explored" below are now **proven theorems**,
> verified and incorporated into `paper.tex` §9:
> - The hub-coupling positivity lemma and the universal bound
>   $t(C_m,W)\ge p^m-\Tr(A^m)$, hence the **norm-safe** criterion $\|A\|\le q$
>   (subsumes regular graphons).
> - The **rank-one complement** and **equal disjoint clique complement** all-$k$
>   theorems.
> - The exact path-cycle identity and the corrected spectral bottleneck
>   $\Psi_m\ge\Tr(A^m)-pq^{m-1}$ (with a counterexample to the naive modewise
>   target).
> The C_13 partial result (path-certificate $p\ge519/1000$, closed-form
> $P_q^{(m)}$, residual gap $\approx0.0034$) is now `paper.tex` §8. What survives
> below as genuinely *open* is the asymptotic obstruction analysis (§4–§5 here):
> the $\delta_m\sim9/(4m^2)$ ceiling, the unequal-clique target, and the
> sharp-$C_5$-Turán route. Read those sections; treat §2–§3 as historical.
>
> One self-correction: the line "$m=7,9,11$ ... proved ... and **open for every
> $m\ge13$**" is now superseded — $C_{13}$ is *partially* closed ($p\ge519/1000$).

## 1. The open problem

**Conjecture.** For every odd integer $m = 2k+1 \geq 3$ and every graphon $W$ with edge density $p = t(K_2, W)$,
$$t(C_m, W) \;\geq\; p^m - p(1-p)^{m-1}.$$
The bound is tight at $p = 1 - 1/j$ for integers $j \geq 2$, attained by the balanced complete $j$-partite graphon. The cases $m = 3$ (Goodman, 1959), $m = 5$ (folklore for $p \leq 1/2$; Bennett–Dudek–Lidický–Pikhurko 2020 at the discrete densities $p = 1 - 1/k$), and now $m = 7, 9, 11$ (current paper) are proved for all $p \in (0,1)$. The conjecture is **open for every $m \geq 13$**.

The $C_9$ and $C_{11}$ proofs are hybrids of (i) a complement path-certificate covering $p \geq \rho_m$, and (ii) a spectral closure using triangle density covering $1/2 < p \leq \rho_m$. This report assesses whether the hybrid scales to $m \geq 13$.

## 2. Approaches explored

**Generalize the spectral closure.** The reduction-to-$\ell = p$ step of §6.2 (monotonicity of $G(\ell)$) extends verbatim and rigorously to every odd $m \geq 5$: implicit differentiation gives $\alpha' = \ell^{m-1}/\alpha^{m-1}$, and $G'(\ell) \geq 3\ell^2((\ell/\alpha)^{m-3} - 1) > 0$ uniformly. However, Taylor analysis at $p = 1/2 + \varepsilon$ shows the spectral closure window $\delta_m$ shrinks as $\delta_m \sim 9/(4m^2)$, with hard ceiling $\delta_m \leq 9m/(4(m-2)^3)$. Bisection gives $\delta_{13} \approx 0.01559$, $\delta_{15} \approx 0.01166$, etc.

**Generalize the path-certificate.** The path-certificate machinery generalizes cleanly to $C_{13}$, yielding $\rho_{13} = 519/1000$ certified by exact Bernstein subdivision. A **closed-form formula** was discovered for the linear polynomial $P_q^{(m)}(\lambda)$: coefficient of $\lambda^j$ is $a_j(q) = (-1)^j m(1-q)^{m-2-j} + mq^{m-2-j} - (m-2-j)q^{m-3-j}$. Numerical thresholds $q_m^*$ for $m \leq 23$ show non-monotone behavior, stabilizing around $0.479$ — the path-certificate gap $1/2 - q_m^*$ does **not** shrink to zero.

**Reduce to the regular case.** Numerical evidence on step-graphons up to size 8 supports $\inf_W t(C_m, W) = \inf_{W\ p\text{-regular}} t(C_m, W)$, but no reduction technique tested (constant-averaging, convexity, rearrangement) gives a rigorous proof. The functional $W \mapsto t(C_5, W)$ is **not convex** on the edge-density slice. The reduction appears as hard as the original conjecture.

**Alternative inputs.** Spectral moments are cycle densities $\mathrm{Tr}(T^r) = t(C_r, W)$, so higher-clique density theorems (Reiher's $K_r$ result) **cannot** be plugged in. A sharp $t(C_5, W) \geq t(C_5, T(2;c))$ Turán-type bound, if proved, would give $\delta_m$ bounded below by $\approx 0.123$ uniformly in $m$ — but this is itself open. Inductive bootstrap on the conjecture fails: the linear-$\varepsilon$ coefficient $(r-1)/2^{r-2}$ of the conjectured input is strictly less than the required $r(m-1)/(m \cdot 2^{r-2})$ for $r < m$.

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

- **C_{13} margin is barely positive.** $\delta_{13} - 3/200 = 0.00059 > 0$, so **if** the $C_{13}$ path-certificate at the C_{11} q-cutoff $97/200$ were sufficient, the hybrid would close $C_{13}$ — but with razor-thin overlap. The actual $C_{13}$ cutoff $q = 481/1000 < 97/200$ does **not** match the spectral side: there is a residual gap on $q \in (481/1000, 485/1000)$ of width $\approx 0.004$ that is **not covered** by the hybrid as stated. So **the $C_{13}$ case is not closed by these two techniques alone**.

- **BDLP/$C_5$ equivalence.** $(p^5 - p(1-p)^4)/10$ matches BDLP's explicit polynomial at $p = 1 - 1/k$ for all $k \geq 3$; the present results strictly extend BDLP from discrete to continuous $p$.

**No proof of the general conjecture was obtained**, and **the hybrid strategy as currently formulated does not close $C_{13}$** — the spectral side gives only $\delta_{13} = 0.01559$, while the certified path-cert side requires $\delta_{13} \geq 19/1000 = 0.019$.

## 4. Structural obstructions

The general case is hard for **three interlocking reasons**:

**(O1) Quadratic decay of the spectral window.** The slack $\Theta(p) - (p^3 - \alpha_0^3)$ opens linearly in $\varepsilon$ with coefficient $3/(2m) \to 0$, while the deficit $\Delta_0^{3/2}$ opens like $\varepsilon^{3/2}$ with $\Theta(1)$ coefficient $((m-2)/m)^{3/2} \to 1$. Solving the leading balance forces $\delta_m \sim 9/(4m^2)$. This is **intrinsic** to using triangle density + $L^2$-to-$L^3$ comparison: no manipulation within these inputs can change the $1/m^2$ scaling.

**(O2) Path-certificate gap does NOT shrink.** Numerical thresholds $q_m^*$ for the path-certificate stabilize around $0.479$ for $m \geq 17$, giving a gap $1/2 - q_m^* \approx 0.021$ uniformly. So the spectral side must close an interval of essentially **constant width** $\geq 0.02$ at every $m$, but the spectral side itself shrinks like $1/m^2$. The two sides diverge: the **crossover already occurs at $m = 13$** ($G_{13} \geq 0.019$ vs $\delta_{13} = 0.0156$).

**(O3) No usable stronger input from cliques.** Spectral moments are $\sum \lambda_i^r = t(C_r, W)$, **not** $t(K_r, W)$. Reiher's clique density theorem cannot be plugged in; the only meaningful upgrade is a sharp $t(C_r, W) \geq t(C_r, T(2;c))$ bound for odd $r \geq 5$, which is itself open.

A subtler obstruction: at $m \geq 17$ the quadratic kernel $K_2$ in the path-certificate decomposition becomes the **binding** Bernstein constraint on the full $[0, 1/2]$ box, requiring the certificate to be restated on the truncated box $[0, 1 - \rho_m]$.

## 5. Most promising next directions

Ranked by feasibility:

1. **Compute $C_{13}$ rigorously, accepting a marginal gap.** The closed-form $P_q^{(13)}$, the certified $\rho_{13} = 519/1000$, and the spectral $\delta_{13} = 0.01559$ leave a residual interval $q \in (481/1000, 485/1000)$ of width $\approx 0.004$ uncovered. Try to close it via (a) sharpening the path-certificate by truncating $K_2$ to the smaller box (likely cheap, $\sim$1 day), or (b) refining the spectral closure by tracking $O(\varepsilon^2)$ corrections currently dropped. **Most feasible**: the hard work (Bernstein + bisection) is already done, only one of the two sides needs a $\sim 25\%$ improvement.

2. **Prove a sharp $t(C_5, W) \geq t(C_5, T(2;c))$ Turán bound on $p \in [1/2, 2/3]$.** This would replace the triangle input and yield $\delta_m \geq 0.122$ **uniformly in $m$**, closing the gap for every odd $m$ at once given any path-cert with $\rho_m \leq 0.62$. **Highest payoff but technically hardest**: requires an odd-cycle analog of Razborov–Reiher. Flag algebras may give a discrete-$p$ version first.

3. **Prove the regularity reduction directly.** Numerical evidence strongly suggests $\inf_W t(C_m, W) = \inf_{p\text{-regular}} t(C_m, W)$, and the regular case is already handled in §3.2. A Lagrange/Euler–Lagrange analysis of stationary $W$ on the edge-density slice may force step-structure. **Medium feasibility**: an honest attempt has not yet been made; if it works, it unlocks the whole conjecture.

## 6. Concrete next steps for the user

- **Commit the $C_{13}$ infrastructure.** Save `/tmp/c13_paper_style.py` as `discussions/goodman-style-bound/odd_cycle_c13_checker.py` and write a working note `odd_cycle_c13_working_note.tex` documenting $\Phi_{13}$, $\rho_{13} = 519/1000$, and the closed-form $P_q^{(m)}$.

- **Close the residual $C_{13}$ window.** Adapt the section-7.1 scalar inequalities (the $C_{11}$ constants $139/100$ and $9/11$) to $m = 13$ with $\alpha_0 = (pq^{12})^{1/13}$, and check whether the analog of the $C_{11}$ Sturm-certified margin survives at $\varepsilon = 19/1000$.

- **Cite the literature properly.** Add citations to BDLP (arXiv:1803.00165, CPC 2020), Reiher (arXiv:1604.06833, JCTB 2016), Kim–Lee (arXiv:2210.00977, JCTB 2024), Razborov triangle (Annals 2008), and Reiher clique density (Annals 2016). Frame the paper's $C_7, C_9, C_{11}$ continuous-$p$ results as the new state of the art.

- **Stress-test the regularity reduction.** Numerically refine the $n = 4..8$ step-graphon experiments to $n = 10, 12$ at high precision and check whether $\inf$ is still attained at a $p$-regular two-block.

- **Investigate the sharp $C_5$ Turán bound.** Even a partial result (e.g., for $p$ in a sub-interval, or with a controlled lower-order loss) would dramatically widen $\delta_m$ uniformly. This is the highest-leverage open subproblem identified by this investigation.

- **Update `SESSION_STATE.md`** with the verified status: $C_{13}$ unproved as of this report, residual gap $\approx 0.004$ in $q$, closed-form $P_q^{(m)}$ in hand, and the structural ceiling $\delta_m \leq 9m/(4(m-2)^3)$ documented.

**Bottom line.** No proof of the general conjecture was found. The hybrid strategy that proved $C_7, C_9, C_{11}$ has a hard structural ceiling: spectral closure window $\sim 1/m^2$, path-certificate gap $\sim$ constant, and the two cross at exactly $m = 13$. Either a sharper external input ($C_5$ Turán bound) or a structural shortcut (regularity reduction) appears necessary to push beyond $m = 11$.