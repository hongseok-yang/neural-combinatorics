# Addendum Appendix E — ChatGPT Pro conversations (from the account export)

The author's ChatGPT account export (zip of 2026-09-23, placed in the project root on 2026-09-27) contains 1,068 conversations back to May 2024. The conversations below are the ones relevant to `exhaustive_research/` in the 2026-08-18…26 window ("campaign" and "satellite"), followed by the earlier conversations behind the campaign's input documents ("prehistory"). Times are KST. Model names are the export's `model_slug` values, verbatim (`gpt-5-6-pro`, `gpt-5-6-thinking`, `gpt-5.6-sol-wm`). User prompts are reproduced byte-for-byte. Assistant progress/thought entries are counted but not reproduced; files the assistant delivered as sandbox downloads are listed by link line. The full raw record is in the export zip (kept in the raw-data backup).


## Conversation `6a83c384` — “Entropy proof in LaTeX” (campaign)

- 2026-08-18 11:29:56 → 2026-08-18 11:32:33; models: gpt-5-6-thinking×6; 7 messages on the final path
- Blekherman–Raymond entropy proof of t(P5)^3 >= t(P3)^5 written out in LaTeX (Atlas 102 reference)

### E.1 — 2026-08-18 11:29:54 · `6a83c384`

```text
Would you please provide me the proof of 
t(P_5)^3 >= t(P_3)^5
by Blekherman-Raymond, using the entropy method in LaTeX?
```

## Conversation `6a8420b0` — “Proof region splitting question” (satellite)

- 2026-08-18 18:06:57 → 2026-08-18 19:28:22; models: gpt-5-6-pro×21; 26 messages on the final path
- odd-cycle paper: proof region-splitting question (related work)

### E.2 — 2026-08-18 18:13:25 · `6a8420b0` · attachments: paper_new_region2_v2(4).pdf

```text
I have question regarding the proof of this article. So here, we split the region into two, p >= 2/3 and the other. I'd like to understand why we should so. Though we now have the argument that clarifies where the hypothesis is consumed, but it is very low level and is less related to the main proof. So here is my idea. I think the dense region proof is mostly eigenvalue analysis. Most of the analysis focuses on the eigenvalue, and our only condition is that eigenvalues are supported on [-1/2, 1/2]. Then, we might consider relaxed graphon, as an operator which block decomposes, and the 'A' matrix has eigenvalue supported on [-1/2, 1/2]. Then see when this operator satisfies Tr(W^2m+1) >= ..., and find out the failing region converges to (1/2, 2/3). Can you try to prove this kind of claim?
```

### E.3 — 2026-08-18 18:25:18 · `6a8420b0`

```text
I didn't request you to summarise the proof. I want you to give completely different picture, what dense region 'forget', and why such forgetting makes the inequality invalid in the imtermediate region. I have read the paper, so just saying reduce reduce reduce and here is hypothesis used, does not help.
```

## Conversation `6a856564` — “Extend Graphon Lower Bounds” (campaign)

- 2026-08-19 17:12:21 → 2026-08-19 22:36:54; models: gpt-5-6-pro×19; 23 messages on the final path
- PRODUCED notes/chordal_entropy_extension.tex (monotone-exponent + PAVA entropy theorem)
- Delivered file: `[Download the complete LaTeX source](sandbox:/mnt/data/chordal_entropy_extension.tex)`
- Delivered file: `[Download the compiled PDF](sandbox:/mnt/data/chordal_entropy_extension.pdf)`

### E.4 — 2026-08-19 17:12:19 · `6a856564` · attachments: pure_chordal(2).pdf

```text
This article proves some lower bound on the graphon, using the entropy method.
I know that this does not naively relax to the arbitrary chordal graph. But I want to at least somehow extend it. Current condition is a bit restrictive. 
Do you have any idea to extend and relax the condition a bit?
```

### E.5 — 2026-08-19 19:01:48 · `6a856564`

```text
Interesting. Would you please write this proof as a LaTeX, complete, flawless, detailed?
```

## Conversation `6a85a514` — “Resolve Chromatic Bound” (campaign)

- 2026-08-19 21:44:05 → 2026-08-20 01:44:16; models: gpt-5-6-pro×16; 18 messages on the final path
- 21-instance research brief (in the form of an agent-drafted prompt); no resolution

### E.6 — 2026-08-19 21:44:03 · `6a85a514`

```text
**# Prompt for ChatGPT Pro: resolve one open case of the chromatic-polynomial lower bound**

You are a research mathematician specializing in extremal graph theory and graph limits. Below is a fully precise open problem with 21 concrete instances. Your task: **\*\*completely resolve at least one instance\*\*** — either by a rigorous proof or by an explicit, exactly verifiable counterexample. You choose which instance and which direction; both outcomes are equally valuable. Partial progress is welcome as a secondary output, but the goal is one full resolution.

**## 1. Definitions (all standard, stated to fix conventions)**

A **\*\*graphon\*\*** is a symmetric Lebesgue-measurable function $W:[0,1]^2\to[0,1]$. For a finite simple graph $H$ with vertex set $V(H)$ and edge set $E(H)$, the **\*\*homomorphism density\*\*** is

$$

 t(H,W) \\;=\\; \int\_{[0,1]^{V(H)}} \prod\_{uv\in E(H)} W(x\_u,x\_v)\\; \prod\_{u\in V(H)} dx\_u .

$$

(Maps are not required to be injective.) The **\*\*edge density\*\*** of $W$ is $p := t(K\_2,W) = \iint W$.

For a graph $H$ with chromatic polynomial $\chi\_H$ and $v = v(H)$ vertices, define for $0\le p<1$

$$

 \Phi\_H(p) \\;:=\\; (1-p)^{v}\\,\chi\_H\\!\left(\frac{1}{1-p}\right),

 \qquad \Phi\_H(1):=1 \ \text{(continuous extension)}.

$$

This is a polynomial in $p$ with integer coefficients (expanded forms are given below for each instance).

**\*\*Conjectured inequality for a given $H$\*\*** (this is the object to prove or disprove):

\> For every graphon $W$ with edge density $p = t(K\_2,W) \ge 1 - \dfrac{1}{\chi(H)-1}$, it holds that $t(H,W)\ \ge\ \Phi\_H(p)$.

Here $\chi(H)$ is the chromatic number. The density restriction is essential: below the threshold the inequality is generally false and is not conjectured.

Equivalent finite form: since finite graphs are dense in the graphon space and both sides are continuous in the relevant densities, the statement for $H$ is equivalent to: for every finite simple graph $G$ (with $t(F,G) := \hom(F,G)/n^{v(F)}$, so $t(K\_2,G)=2e(G)/n^2$), $t(K\_2,G)\ge$ threshold implies $t(H,G)\ge\Phi\_H(t(K\_2,G))$. You may work in either setting. For a **\*\*counterexample\*\*** you may restrict to step graphons without loss of generality: if $W$ is a step function with $k$ parts of measures $\alpha\_1,\dots,\alpha\_k$ ($\sum\alpha\_i=1$) and symmetric value matrix $M\in[0,1]^{k\times k}$, then

$$

 t(H,W) = \sum\_{\varphi\:V(H)\to[k]}\ \prod\_{uv\in E(H)} M\_{\varphi(u)\varphi(v)}\ \prod\_{u\in V(H)}\alpha\_{\varphi(u)} .

$$

**## 2. Hard constraints any answer must respect**

**\*\*(a) Infinitely many equality cases.\*\*** Let $T\_k$ denote the balanced Turán graphon ($k$ equal parts, $W=0$ on the $k$ diagonal blocks, $W=1$ off-diagonal), with $p = 1-1/k$. Then $t(H,T\_k)=\chi\_H(k)/k^{v(H)}$ and $\Phi\_H(1-1/k)=\chi\_H(k)/k^{v(H)}$ — **\*\*equality holds at $T\_k$ for every $k \ge \chi(H)-1$\*\***, and also at $W\equiv 1$. A proof cannot afford any loss at these points; a counterexample must do strictly better than all of them.

**\*\*(b) The inequality is false for some $H$.\*\*** Among all 117 non-bipartite graphs on $\le 6$ vertices (no isolated vertices, no isolated-edge components), 23 have exact counterexamples and 73 have accepted proofs; the 21 below are exactly the unresolved ones. Known counterexamples come in two shapes: (i) tensor products $W = T\_{k\_1}\otimes\cdots\otimes T\_{k\_s}$ (for which $p=\prod\_i(1-1/k\_i)$ and $t(H,W)=\prod\_i \chi\_H(k\_i)/k\_i^{v(H)}$), and (ii) local perturbations of $T\_2$ or $T\_3$, including one genuinely 5-step "fractional-fibre" perturbation of $T\_2$ at $p\approx 1/2$. So no general theorem is possible; the structure of the specific $H$ must be used.

**\*\*(c) What has already been ruled out for all 21 instances below.\*\*** Do not spend effort re-deriving these:

\- **\*\*Tensor counterexamples are exhausted\*\***: all $T\_{k\_1}\otimes T\_{k\_2}$ with $k\_i\le 500$, repeated and consecutive products with endpoints $\le 1000$, and $2\times10^6$ random products of lengths 2–24 with factors $\le 5000$ were checked in exact arithmetic. None violates the inequality for these 21 graphs.

\- **\*\*Local stability holds\*\***: for each of the 21 graphs there is a proven explicit $L^\infty$-radius around every interior Turán graphon $T\_k$, $k\ge\chi(H)$, and around the critical threshold Turán graphon, inside which the inequality holds. So a counterexample cannot be an $L^\infty$-small perturbation of any balanced Turán graphon. (Perturbations of small measure but order-one amplitude are *\*not\** excluded in general — that is how the one known non-tensor 6-vertex counterexample works.)

\- **\*\*The high-density endpoint is closed\*\***: for each of the 21 graphs there is a proven explicit $\varepsilon\_H>0$ such that the inequality holds for **\*\*every\*\*** graphon with $1-p\le\varepsilon\_H$. (The proven radii are small, e.g. of order $10^{-6}$ to $10^{-12}$.) So a counterexample must live at "middle" densities; a proof, however, should ideally cover the whole range on its own.

\- **\*\*The constant graphon is safe\*\***: $W\equiv p$ satisfies the inequality strictly in the open range for all 21 graphs.

**\*\*(d) Rigor standard.\*\*** A proof must be complete and self-contained modulo the citable literature (e.g. Goodman's bound, Moon–Moser clique-density inequalities $t\_{j}\ge t\_{j-1}\bigl(1-(j-1)(1-p)\bigr)$, Kruskal–Katona, Reiher's clique density theorem, standard entropy/Cauchy–Schwarz/Hölder arguments, Lovász's graph-limits book). Numerical SDP/flag-algebra output is acceptable **\*\*only\*\*** if rounded to an exact rational certificate that can be verified by hand or exact arithmetic. A counterexample must be an explicit step graphon with rational part sizes and rational values, an explicit rational $p$ in the admissible range, and an exact rational evaluation of both $t(H,W)$ and $\Phi\_H(p)$ exhibiting $t(H,W)<\Phi\_H(p)$.

**## 3. The 21 open instances**

Vertices are labeled $0,\dots,v-1$. "Threshold" is $1-1/(\chi(H)-1)$; the inequality is claimed exactly on $p\in[\text{threshold},1]$. The graph6 string is authoritative machine-readable identification; the edge list is the same graph spelled out. ($\bar H$ = complement, listed since several methods work in the complement at high density.)

**### Five-vertex instance**

**\*\*Atlas 43\*\*** — graph6 \`Dlc\`, $v=5$, $e=6$, $\chi=3$, threshold $p\ge 1/2$. The "house": 5-cycle $0\\!-\\!1\\!-\\!2\\!-\\!3\\!-\\!4\\!-\\!0$ plus chord $\\{0,3\\}$.

Edges: $\\{0,1\\},\\{0,3\\},\\{0,4\\},\\{1,2\\},\\{2,3\\},\\{3,4\\}$.

$\chi\_H(x)=x(x-1)(x-2)(x^2-3x+3)$; target $\Phi\_H(p)=p(2p-1)(3p^2-3p+1)=6p^4-9p^3+5p^2-p$.

$\bar H$ edges: $\\{0,2\\},\\{1,3\\},\\{1,4\\},\\{2,4\\}$.

**### Six-vertex instances, $\chi=3$ (threshold $p\ge 1/2$)**

**\*\*Atlas 118\*\*** — graph6 \`Eht?\`, $e=7$.

Edges: $\\{0,1\\},\\{0,4\\},\\{1,2\\},\\{1,4\\},\\{1,5\\},\\{2,3\\},\\{3,4\\}$.

$\chi\_H(x)=x(x-1)^2(x-2)(x^2-3x+3)$; $\Phi\_H(p)=p^2(2p-1)(3p^2-3p+1)$.

$\bar H$: $\\{0,2\\},\\{0,3\\},\\{0,5\\},\\{1,3\\},\\{2,4\\},\\{2,5\\},\\{3,5\\},\\{4,5\\}$.

**\*\*Atlas 122\*\*** — graph6 \`Eld?\`, $e=7$.

Edges: $\\{0,1\\},\\{0,3\\},\\{0,4\\},\\{1,2\\},\\{1,5\\},\\{2,3\\},\\{3,4\\}$.

$\chi\_H(x)=x(x-1)^2(x-2)(x^2-3x+3)$; $\Phi\_H(p)=p^2(2p-1)(3p^2-3p+1)$.

$\bar H$: $\\{0,2\\},\\{0,5\\},\\{1,3\\},\\{1,4\\},\\{2,4\\},\\{2,5\\},\\{3,5\\},\\{4,5\\}$.

**\*\*Atlas 124\*\*** — graph6 \`Exd?\`, $e=7$.

Edges: $\\{0,1\\},\\{0,2\\},\\{0,4\\},\\{1,2\\},\\{1,5\\},\\{2,3\\},\\{3,4\\}$.

$\chi\_H(x)=x(x-1)^2(x-2)(x^2-3x+3)$; $\Phi\_H(p)=p^2(2p-1)(3p^2-3p+1)$.

$\bar H$: $\\{0,3\\},\\{0,5\\},\\{1,3\\},\\{1,4\\},\\{2,4\\},\\{2,5\\},\\{3,5\\},\\{4,5\\}$.

**\*\*Atlas 127\*\*** — graph6 \`EZEG\`, $e=7$. A 6-cycle $0\\!-\\!2\\!-\\!1\\!-\\!3\\!-\\!4\\!-\\!5\\!-\\!0$ plus chord $\\{2,3\\}$.

Edges: $\\{0,2\\},\\{0,5\\},\\{1,2\\},\\{1,3\\},\\{2,3\\},\\{3,4\\},\\{4,5\\}$.

$\chi\_H(x)=x(x-1)(x-2)^2(x^2-2x+2)$; $\Phi\_H(p)=p(2p-1)^2(2p^2-2p+1)$.

$\bar H$: $\\{0,1\\},\\{0,3\\},\\{0,4\\},\\{1,4\\},\\{1,5\\},\\{2,4\\},\\{2,5\\},\\{3,5\\}$.

**\*\*Atlas 130\*\*** — graph6 \`E{CW\`, $e=7$. **\*\*Chordal.\*\*** Two vertex-disjoint triangles $\\{0,1,2\\}$ and $\\{3,4,5\\}$ joined by the single bridge $\\{0,3\\}$.

Edges: $\\{0,1\\},\\{0,2\\},\\{0,3\\},\\{1,2\\},\\{3,4\\},\\{3,5\\},\\{4,5\\}$.

$\chi\_H(x)=x(x-1)^3(x-2)^2$; $\Phi\_H(p)=p^3(2p-1)^2$.

Useful bilinear form: $t(H,W)=\iint W(x,y)\\,\tau(x)\\,\tau(y)\\,dx\\,dy$ where $\tau(x):=\iint W(x,a)W(x,b)W(a,b)\\,da\\,db$ is the rooted-triangle density.

$\bar H$: $\\{0,4\\},\\{0,5\\},\\{1,3\\},\\{1,4\\},\\{1,5\\},\\{2,3\\},\\{2,4\\},\\{2,5\\}$.

**\*\*Atlas 147\*\*** — graph6 \`EhMg\`, $e=8$.

Edges: $\\{0,1\\},\\{0,5\\},\\{1,2\\},\\{2,3\\},\\{2,4\\},\\{2,5\\},\\{3,4\\},\\{4,5\\}$.

$\chi\_H(x)=x(x-1)(x-2)^2(x^2-3x+3)$; $\Phi\_H(p)=p(2p-1)^2(3p^2-3p+1)$.

$\bar H$: $\\{0,2\\},\\{0,3\\},\\{0,4\\},\\{1,3\\},\\{1,4\\},\\{1,5\\},\\{3,5\\}$.

**\*\*Atlas 151\*\*** — graph6 \`EhdW\`, $e=8$.

Edges: $\\{0,1\\},\\{0,4\\},\\{1,2\\},\\{1,5\\},\\{2,3\\},\\{3,4\\},\\{3,5\\},\\{4,5\\}$.

$\chi\_H(x)=x(x-1)(x-2)^2(x^2-3x+4)$; $\Phi\_H(p)=p(2p-1)^2(4p^2-5p+2)$.

$\bar H$: $\\{0,2\\},\\{0,3\\},\\{0,5\\},\\{1,3\\},\\{1,4\\},\\{2,4\\},\\{2,5\\}$.

**\*\*Atlas 153\*\*** — graph6 \`Ehf\_\`, $e=8$. *\*Density-neutral: $\Phi\_H(p)\le 0$ for $1/2\le p\le 7/12$, so only $p>7/12$ is at issue.\**

Edges: $\\{0,1\\},\\{0,4\\},\\{0,5\\},\\{1,2\\},\\{1,5\\},\\{2,3\\},\\{2,5\\},\\{3,4\\}$.

$\chi\_H(x)=x(x-1)(x-2)(x^3-5x^2+9x-7)$; $\Phi\_H(p)=p(2p-1)(7p^3-12p^2+8p-2)$.

$\bar H$: $\\{0,2\\},\\{0,3\\},\\{1,3\\},\\{1,4\\},\\{2,4\\},\\{3,5\\},\\{4,5\\}$.

**\*\*Atlas 168\*\*** — graph6 \`E^MG\`, $e=9$.

Edges: $\\{0,2\\},\\{0,3\\},\\{0,5\\},\\{1,2\\},\\{1,3\\},\\{2,3\\},\\{2,4\\},\\{3,4\\},\\{4,5\\}$.

$\chi\_H(x)=x(x-1)(x-2)^2(x^2-4x+5)$; $\Phi\_H(p)=p(2p-1)^2(5p^2-6p+2)$.

$\bar H$: $\\{0,1\\},\\{0,4\\},\\{1,4\\},\\{1,5\\},\\{2,5\\},\\{3,5\\}$.

**\*\*Atlas 171\*\*** — graph6 \`Ehew\`, $e=9$. *\*Density-neutral: only $p>7/12$ is at issue.\**

Edges: $\\{0,1\\},\\{0,4\\},\\{0,5\\},\\{1,2\\},\\{2,3\\},\\{2,5\\},\\{3,4\\},\\{3,5\\},\\{4,5\\}$.

$\chi\_H(x)=x(x-1)(x-2)(x^3-6x^2+13x-11)$; $\Phi\_H(p)=p(2p-1)(11p^3-20p^2+13p-3)$.

$\bar H$: $\\{0,2\\},\\{0,3\\},\\{1,3\\},\\{1,4\\},\\{1,5\\},\\{2,4\\}$.

**\*\*Atlas 174\*\*** — graph6 \`EtTg\`, $e=9$. The **\*\*triangular prism\*\*** $K\_3\\,\square\\,K\_2$: triangles $\\{0,2,3\\}$, $\\{1,4,5\\}$, matching $\\{0,1\\},\\{2,5\\},\\{3,4\\}$. 3-regular. *\*Density-neutral: only $p>7/12$ is at issue.\**

Edges: $\\{0,1\\},\\{0,2\\},\\{0,3\\},\\{1,4\\},\\{1,5\\},\\{2,3\\},\\{2,5\\},\\{3,4\\},\\{4,5\\}$.

$\chi\_H(x)=x(x-1)(x-2)(x^3-6x^2+14x-13)$; $\Phi\_H(p)=p(2p-1)(13p^3-25p^2+17p-4)$.

$\bar H$: $\\{0,4\\},\\{0,5\\},\\{1,2\\},\\{1,3\\},\\{2,4\\},\\{3,5\\}$ — the complement is the 6-cycle $4\\!-\\!0\\!-\\!5\\!-\\!3\\!-\\!1\\!-\\!2\\!-\\!4$ (the prism is $\bar{C\_6}$).

Integer values: $\chi\_H(3)=12$, $\chi\_H(4)=264$.

**\*\*Atlas 188\*\*** — graph6 \`EzNG\`, $e=10$. *\*Density-neutral: only $p>7/12$ is at issue.\**

Edges: $\\{0,1\\},\\{0,2\\},\\{0,5\\},\\{1,2\\},\\{1,3\\},\\{1,5\\},\\{2,3\\},\\{2,4\\},\\{3,4\\},\\{4,5\\}$.

$\chi\_H(x)=x(x-1)(x-2)(x^3-7x^2+18x-17)$; $\Phi\_H(p)=p(2p-1)(17p^3-33p^2+22p-5)$.

$\bar H$: $\\{0,3\\},\\{0,4\\},\\{1,4\\},\\{2,5\\},\\{3,5\\}$.

**### Six-vertex instances, $\chi=4$ (threshold $p\ge 2/3$)**

**\*\*Atlas 157\*\*** — graph6 \`\`E\~\`\_\`\`, $e=9$. **\*\*Chordal.\*\*** $K\_4$ on $\\{0,1,2,3\\}$, a triangle $\\{1,2,5\\}$ glued along edge $\\{1,2\\}$, and a pendant vertex $4$ attached to $0$.

Edges: $\\{0,1\\},\\{0,2\\},\\{0,3\\},\\{0,4\\},\\{1,2\\},\\{1,3\\},\\{1,5\\},\\{2,3\\},\\{2,5\\}$.

$\chi\_H(x)=x(x-1)^2(x-2)^2(x-3)$; $\Phi\_H(p)=p^2(2p-1)^2(3p-2)$.

$\bar H$: $\\{0,5\\},\\{1,4\\},\\{2,4\\},\\{3,4\\},\\{3,5\\},\\{4,5\\}$.

**\*\*Atlas 169\*\*** — graph6 \`Exf\_\`, $e=9$.

Edges: $\\{0,1\\},\\{0,2\\},\\{0,4\\},\\{0,5\\},\\{1,2\\},\\{1,5\\},\\{2,3\\},\\{2,5\\},\\{3,4\\}$.

$\chi\_H(x)=x(x-1)(x-2)(x-3)(x^2-3x+3)$; $\Phi\_H(p)=p(2p-1)(3p-2)(3p^2-3p+1)$.

$\bar H$: $\\{0,3\\},\\{1,3\\},\\{1,4\\},\\{2,4\\},\\{3,5\\},\\{4,5\\}$.

**\*\*Atlas 181\*\*** — graph6 \`E^mG\`, $e=10$. **\*\*Chordal.\*\*** $K\_4$ on $\\{0,2,3,4\\}$, a triangle $\\{0,4,5\\}$ glued along edge $\\{0,4\\}$, and a triangle $\\{1,2,3\\}$ glued along edge $\\{2,3\\}$.

Edges: $\\{0,2\\},\\{0,3\\},\\{0,4\\},\\{0,5\\},\\{1,2\\},\\{1,3\\},\\{2,3\\},\\{2,4\\},\\{3,4\\},\\{4,5\\}$.

$\chi\_H(x)=x(x-1)(x-2)^3(x-3)$; $\Phi\_H(p)=p(2p-1)^3(3p-2)$.

$\bar H$: $\\{0,1\\},\\{1,4\\},\\{1,5\\},\\{2,5\\},\\{3,5\\}$.

**\*\*Atlas 185\*\*** — graph6 \`Exv\_\`, $e=10$.

Edges: $\\{0,1\\},\\{0,2\\},\\{0,4\\},\\{0,5\\},\\{1,2\\},\\{1,4\\},\\{1,5\\},\\{2,3\\},\\{2,5\\},\\{3,4\\}$.

$\chi\_H(x)=x(x-1)(x-2)(x-3)(x^2-4x+5)$; $\Phi\_H(p)=p(2p-1)(3p-2)(5p^2-6p+2)$.

$\bar H$: $\\{0,3\\},\\{1,3\\},\\{2,4\\},\\{3,5\\},\\{4,5\\}$.

**\*\*Atlas 194\*\*** — graph6 \`E\~wW\`, $e=11$. $K\_5$ minus an edge on $\\{0,1,2,3,4\\}$ (missing $\\{3,4\\}$), plus vertex $5$ adjacent to $3,4$.

Edges: $\\{0,1\\},\\{0,2\\},\\{0,3\\},\\{0,4\\},\\{1,2\\},\\{1,3\\},\\{1,4\\},\\{2,3\\},\\{2,4\\},\\{3,5\\},\\{4,5\\}$.

$\chi\_H(x)=x(x-1)(x-2)(x-3)(x^2-5x+7)$; $\Phi\_H(p)=p(2p-1)(3p-2)(7p^2-9p+3)$.

$\bar H$: $\\{0,5\\},\\{1,5\\},\\{2,5\\},\\{3,4\\}$.

**\*\*Atlas 196\*\*** — graph6 \`ER\~g\`, $e=11$.

Edges: $\\{0,2\\},\\{0,4\\},\\{0,5\\},\\{1,3\\},\\{1,4\\},\\{1,5\\},\\{2,3\\},\\{2,4\\},\\{2,5\\},\\{3,4\\},\\{4,5\\}$.

$\chi\_H(x)=x(x-1)(x-2)(x-3)(x^2-5x+7)$; $\Phi\_H(p)=p(2p-1)(3p-2)(7p^2-9p+3)$.

$\bar H$: $\\{0,1\\},\\{0,3\\},\\{1,2\\},\\{3,5\\}$.

**\*\*Atlas 199\*\*** — graph6 \`El^g\`, $e=11$.

Edges: $\\{0,1\\},\\{0,3\\},\\{0,5\\},\\{1,2\\},\\{1,4\\},\\{1,5\\},\\{2,3\\},\\{2,4\\},\\{2,5\\},\\{3,4\\},\\{4,5\\}$.

$\chi\_H(x)=x(x-1)(x-2)(x-3)(x^2-5x+8)$; $\Phi\_H(p)=p(2p-1)(3p-2)(8p^2-11p+4)$.

$\bar H$: $\\{0,2\\},\\{0,4\\},\\{1,3\\},\\{3,5\\}$.

**\*\*Atlas 203\*\*** — graph6 \`E\~^G\`, $e=12$.

Edges: $\\{0,1\\},\\{0,2\\},\\{0,3\\},\\{0,5\\},\\{1,2\\},\\{1,3\\},\\{1,4\\},\\{1,5\\},\\{2,3\\},\\{2,4\\},\\{3,4\\},\\{4,5\\}$.

$\chi\_H(x)=x(x-1)(x-2)(x-3)(x^2-6x+10)$; $\Phi\_H(p)=p(2p-1)(3p-2)(10p^2-14p+5)$.

$\bar H$: $\\{0,4\\},\\{2,5\\},\\{3,5\\}$.

**## 4. Known partial lower bounds on the three chordal instances**

For connected chordal $H$ with maximal clique sizes $r\_i$ and clique-tree separator sizes $s\_e$, write $b\_j := \\#\\{i: r\_i\ge j\\} - \\#\\{e: s\_e \ge j\\}$ (so $\chi\_H(x)=\prod\_j (x-j+1)^{b\_j}$), and $c\_j(p) := 1-(j-1)(1-p)$. An entropy argument (uniform $K\_r$-homomorphism law, junction-tree gluing, Moon–Moser suffix bounds) proves $t(H,W)\ge \prod\_j c\_j(p)^{b\_j}=\Phi\_H(p)$ whenever $b\_1\le\cdots\le b\_r$ — but all three chordal instances above **\*\*violate\*\*** that monotonicity, and the same method then only yields the strictly weaker "pooled" bound $\prod\_j c\_j(p)^{\bar b\_j}$ with $\bar b$ the isotonic (pool-adjacent-violators) regression of $b$:

\- **\*\*Atlas 130\*\***: $b=(1,3,2)$, proven bound $t \ge \bigl[p(2p-1)\bigr]^{5/2}$, target $p^3(2p-1)^2$.

\- **\*\*Atlas 157\*\***: $b=(1,2,2,1)$, $\bar b=(1,\tfrac53,\tfrac53,\tfrac53)$, proven bound $t \ge \bigl[p(2p-1)(3p-2)\bigr]^{5/3}$; target $p^2(2p-1)^2(3p-2)$.

\- **\*\*Atlas 181\*\***: $b=(1,1,3,1)$, $\bar b=(1,1,2,2)$, proven bound $t \ge p\\,(2p-1)^2(3p-2)^2$; target $p(2p-1)^3(3p-2)$. **\*\*The gap is a single factor $(3p-2)$ vs $(2p-1)$.\*\*** Closing this one factor resolves the instance.

**## 5. Suggested entry points (you are free to ignore these)**

1\. **\*\*Atlas 130\*\*** (two triangles joined by a bridge). The cleanest statement in the list: prove or disprove $\iint W(x,y)\tau(x)\tau(y) \ge p^3(2p-1)^2$ for $p\ge 1/2$, where $\tau$ is the rooted-triangle density and $\int\tau = t(K\_3,W) \ge p(2p-1)$ by Goodman's bound. The difficulty is the correlation between $W(x,y)$ and the product $\tau(x)\tau(y)$; naive Cauchy–Schwarz decouplings lose at $T\_k$.

2\. **\*\*Atlas 181\*\***: upgrade the pooled entropy bound by one factor (see §4).

3\. **\*\*Atlas 43\*\*** (the house): the only 5-vertex instance; $t \ge p(2p-1)(3p^2-3p+1)$ for $p\ge 1/2$. Structurally the house is a triangle $\\{0,3,4\\}$ and a 4-cycle $0\\!-\\!1\\!-\\!2\\!-\\!3\\!-\\!0$ glued along the edge $\\{0,3\\}$, and correspondingly $p\cdot\Phi\_H(p) = \Phi\_{K\_3}(p)\cdot\Phi\_{C\_4}(p)$ with $\Phi\_{K\_3}(p)=p(2p-1)$ and $\Phi\_{C\_4}(p)=p(3p^2-3p+1)$ — suggesting an edge-rooted decoupling ansatz.

4\. **\*\*Density-neutral rows 153, 171, 174, 188\*\***: the inequality is vacuous on $[1/2, 7/12]$; among them **\*\*Atlas 174 is the triangular prism\*\***, a highly symmetric graph where exact spectral/moment computations are feasible.

5\. If you instead hunt for a counterexample: the known non-tensor counterexample for a similar graph is a 5-step graphon obtained from $T\_2$ by carving out a set of measure $\varepsilon=1/3000$ and using order-one but carefully chosen values on the new cells, verified in exact rational arithmetic at $p$ slightly above $1/2$. Small-measure/large-amplitude constructions near the threshold, or constructions near $p\approx 0.55$–$0.65$ (for $\chi=3$) respectively $p\approx 0.7$–$0.8$ (for $\chi=4$), are the unexplored regimes.

**## 6. Required output format**

1\. State clearly **\*\*which Atlas ID(s)\*\*** you resolve and in **\*\*which direction\*\*** (proof of the inequality on the full range $[1-\tfrac1{\chi-1},\\,1]$, or counterexample).

2\. For a proof: a complete argument, every inequality justified, with the equality cases at each $T\_k$ traced through the proof (a correct proof must be tight there). Cite standard results precisely.

3\. For a counterexample: the step graphon (part sizes $\alpha\_i$, matrix $M$, all rational), the value of $p$ as an exact rational, exact rational values of $t(H,W)$ and $\Phi\_H(p)$, and the strict inequality $t < \Phi\_H(p)$. Include enough intermediate structure (e.g. the polynomial in the perturbation parameter) that the computation can be independently re-verified by exact arithmetic.

4\. If after serious effort you cannot fully resolve any instance, report the most advanced partial result in a precisely stated form (e.g. a proof on a subinterval of densities strictly larger than what is stated as known above, or a reduction of one instance to a finite list of explicitly stated polynomial inequalities), and clearly separate proven claims from heuristics.
```

*Note:* A brief in the form of an agent-drafted prompt ("# Prompt for ChatGPT Pro: resolve one open case…", 21 instances, 18,497 characters). Its content — the exhausted tensor searches, the L-infinity stability radii, the 10^-6..10^-12 high-density radii — is the campaign state as of 19 Aug. The session that drafted it is in neither machine's surviving logs: this device has no session at that time, and the workstation Codex logs never mention ChatGPT (the deleted Claude Code sessions remain possible). Pasted by the user.

## Conversation `6a8628e3` — “Resolve Homomorphism Inequalities” (campaign)

- 2026-08-20 07:06:28 → 2026-08-20 15:11:04; models: gpt-5-6-pro×24; 26 messages on the final path
- three-instance brief (Atlas 130 bridge-triangles, K4 pages, house); run ended without a final answer

### E.7 — 2026-08-20 07:06:27 · `6a8628e3`

```text
**# Three open homomorphism-density inequalities**

You are a research mathematician in extremal graph theory. Below are three concrete open problems. **\*\*Completely resolve at least one\*\*** — by rigorous proof or by an explicit, exactly verifiable counterexample. Both directions are valuable; pick the instance you judge most tractable.

**## Setup**

A graphon is a symmetric measurable $W:[0,1]^2\to[0,1]$; for a finite simple graph $H$,

$$

 t(H,W)=\int\_{[0,1]^{V(H)}}\prod\_{uv\in E(H)}W(x\_u,x\_v)\prod\_u dx\_u,

 \qquad p:=t(K\_2,W).

$$

For each $H$ below, the question is whether every graphon with $p\ge 1-\frac{1}{\chi(H)-1}$ satisfies

$$

 t(H,W)\ \ge\ \Phi\_H(p):=(1-p)^{v(H)}\\,\chi\_H\\!\left(\tfrac{1}{1-p}\right),

$$

where $\chi\_H$ is the chromatic polynomial. Prove it on the full stated range, or give a counterexample.

**## The three instances**

**\*\*Problem A (main target).\*\*** $H$ = two vertex-disjoint triangles joined by one edge (a bridge): vertices $0..5$, edges $\\{01,02,12,\\;34,35,45,\\;03\\}$. Here $\chi\_H(x)=x(x-1)^3(x-2)^2$, and the claim reads

$$

 t(H,W)\ \ge\ p^3(2p-1)^2 \qquad\text{for } p\ge \tfrac12 .

$$

Equivalently, with the rooted-triangle density $\tau(x):=\iint W(x,a)W(x,b)W(a,b)\\,da\\,db$:

$$

 \iint W(x,y)\\,\tau(x)\\,\tau(y)\\,dx\\,dy\ \ge\ p^3(2p-1)^2 .

$$

Known: $\int\tau = t(K\_3,W)\ge p(2p-1)$ (Goodman), and an entropy argument gives $t(H,W)\ge[p(2p-1)]^{5/2}$, which is weaker. Naive Cauchy–Schwarz decouplings fail because they are not tight at the equality cases below.

**\*\*Problem B (smallest gap).\*\*** $H$ = $K\_4$ on $\\{0,2,3,4\\}$ with two triangles glued on edges: triangle $\\{0,4,5\\}$ on edge $\\{0,4\\}$ and triangle $\\{1,2,3\\}$ on edge $\\{2,3\\}$. Edges: $\\{02,03,04,05,12,13,23,24,34,45\\}$; $\chi\_H(x)=x(x-1)(x-2)^3(x-3)$. Claim:

$$

 t(H,W)\ \ge\ p(2p-1)^3(3p-2) \qquad\text{for } p\ge \tfrac23 .

$$

Known (entropy): $t(H,W)\ \ge\ p(2p-1)^2(3p-2)^2$. Since $3p-2\le 2p-1$ on the range, the entire gap is upgrading one factor $(3p-2)$ to $(2p-1)$.

**\*\*Problem C (smallest graph).\*\*** $H$ = the house: 5-cycle $0\\!-\\!1\\!-\\!2\\!-\\!3\\!-\\!4\\!-\\!0$ plus chord $\\{0,3\\}$ (a triangle and a 4-cycle glued along an edge). $\chi\_H(x)=x(x-1)(x-2)(x^2-3x+3)$. Claim:

$$

 t(H,W)\ \ge\ p(2p-1)(3p^2-3p+1) \qquad\text{for } p\ge \tfrac12 .

$$

**## Facts any answer must respect**

1\. **\*\*Equality cases.\*\*** For the balanced Turán graphon $T\_k$ ($k$ equal parts, $0$ on diagonal blocks, $1$ off-diagonal; $p=1-1/k$): $t(H,T\_k)=\chi\_H(k)/k^{v(H)}=\Phi\_H(1-1/k)$. So **\*\*equality holds at every $T\_k$ with $k\ge\chi(H)-1$\*\***, and at $W\equiv1$. A proof must be tight at all of them; a counterexample must beat all of them.

2\. **\*\*The inequality is false for some graphs\*\*** of the same size (exact counterexamples exist for 23 sibling graphs, via tensor products $T\_{k\_1}\otimes\cdots\otimes T\_{k\_s}$, where $t$ is multiplicative and $p=\prod(1-1/k\_i)$, or via local perturbations of $T\_2$/$T\_3$). So the specific structure of $H$ must be used.

3\. **\*\*Already ruled out for these three $H$\*\*** (do not redo): all tensor-product counterexamples up to very large search bounds; any $L^\infty$-small perturbation of any $T\_k$ (proven local stability); the near-complete regime ($1-p$ small, proven); the constant graphon $W\equiv p$ (satisfies the inequality strictly). A counterexample, if any, is non-tensor and at middle densities — e.g. a perturbation of $T\_2$ or $T\_3$ of small measure but order-one amplitude.

4\. **\*\*Verification standard.\*\*** A counterexample must be a step graphon: rational part sizes $\alpha\_i$, rational symmetric value matrix $M$, with

$$ t(H,W)=\sum\_{\varphi\:V(H)\to[k]}\prod\_{uv\in E(H)}M\_{\varphi(u)\varphi(v)}\prod\_u \alpha\_{\varphi(u)}, $$

and exact rational values showing $t(H,W)<\Phi\_H(p)$. A proof must be complete, with every step justified (standard results — Goodman, Moon–Moser, Kruskal–Katona, Reiher's clique density theorem, Cauchy–Schwarz/entropy — may be cited).

**## Output**

State which problem you resolve and in which direction, then give the full proof or the explicit certificate. If you cannot fully resolve one, give your best partial result with proven claims cleanly separated from heuristics.
```

*Note:* A second brief of the same form (three instances: Atlas 130, a K4-with-pages graph, the house), with the same untraced provenance as the brief above.

## Conversation `6a8697f6` — “Formulate Graph Deviations” (satellite)

- 2026-08-20 15:00:23 → 2026-08-20 16:16:47; models: gpt-5-6-pro×13; 15 messages on the final path
- large-deviation rate-function flag-algebra formulation (separate thread)

### E.8 — 2026-08-20 15:00:22 · `6a8697f6`

```text
Recently, we are studying the large deviation problems arising in graph problems, like 
min I_p(W) s.t. t(H, W) >= r^{e(H)}
where I_p(W) = int J_p(W(x, y)) dx dy, J_p(z) = z log z/p + (1-z) log (1-z)/(1-p). 

This is often not bad to be solved with analytic techniques, I'm interested in the more principled way. Like the flag algebra generalising the sum of square tactic. 
Can this be formulated with some modern combinatorics tool, like flag algebra, entropy method, etc?
```

## Conversation `6a871354` — “Prove Or Disprove Conjecture” (campaign)

- 2026-08-20 23:46:45 → 2026-08-23 11:26:09; models: gpt-5-6-pro×238; 252 messages on the final path
- the house-graph (Atlas 43) proving thread, 20-23 Aug; partial intervals only

### E.9 — 2026-08-20 23:46:44 · `6a871354`

```text
Consider a house graph, which has 5 vertices and 6 edges, that is constructed by gluing triangle and 4-cycle by an edge. 

Our conjecture is that this graph satisfies the following homomorphism density lower bound:
t(H, W) >= chi_H(1 / (1-p)) (1-p)^{v(H)} whenever p >= 1 - 1 / (chi(H) - 1)
where chi_H is the chromatic polynomial of H, v(H) is number of vertices in H, chi(H) is the chromatic number of H, and p is the edge density of W, t(K_2, W). 

This conjecture emerges from the turan graph optimality, if this conjecture is true, then the balanced complete k-partite graphons are minimisers of H-density under edge density constraints p = 1 - 1 / k. 

Work until you prove or disprove this conjecture.
```

### E.10 — 2026-08-21 13:29:11 · `6a871354`

```text
I see. I agree that this is not an easy problem, for instance, a slightly different variant C_3 U C_5 was also hard to prove, which we utilised flag algebra to prove it and it was quite hard. But I believe you can prove it. Try to make some breakthrough and prove it. You may even rely on some computational methodology, like lots of Bernstein polynomial certificate, SoS, etc.
```

### E.11 — 2026-08-21 17:52:21 · `6a871354`

```text
Please focus on the non-flag algebra approach. I am planning to verify these proofs, but including flag algebra proof makes it too hard. And you building all the flag algebra machinary and then trying to proof, is not very effective now. Try your best to prove the inequality.
```

### E.12 — 2026-08-21 21:25:55 · `6a871354`

```text
I see. Would you please work further to prove the conjectured inequality?
```

### E.13 — 2026-08-22 11:09:42 · `6a871354`

```text
Wow. This is definitely interesting direction. I haven't seen this kind of conditional argument. Would you please push forward to close for remaining edge density region?
```

### E.14 — 2026-08-22 15:16:53 · `6a871354`

```text
I see. Would you please push more to proce the remaining interval?
```

### E.15 — 2026-08-23 07:37:58 · `6a871354`

```text
Would you please resume working on to prove the conjectured inequality?
```

## Conversation `6a8961a4` — “Branch · Prove Or Disprove Conjecture” (campaign)

- 2026-08-22 17:46:05 → 2026-08-22 19:44:23; models: gpt-5-6-pro×112, gpt-5-6-thinking×5; 126 messages on the final path
- branch of the house thread; PRODUCED notes/house_partial.tex (p >= (1+1/sqrt3)/2 write-up)

### E.16 — 2026-08-22 17:46:01 · `6a8961a4`

```text
Would you please provide me your proof on the region p >= (1 + 1/sqrt(3)) / 2 in LaTeX code, complete, detailed, flawless?
```

*Note:* Branch point: the conversation is forked from the house thread after the 21 Aug 23:51 partial result; the earlier prompts are replayed from the parent and not repeated here.

*(4 earlier prompt(s) replayed from the parent conversation are listed there.)*

## Conversation `6a8aa259` — “Common Graphs Literature Status” (satellite)

- 2026-08-23 16:34:11 → 2026-08-23 17:03:08; models: gpt-5.6-sol-wm×33; 35 messages on the final path
- common-graphs literature status (with a self-correction on "odd girth")

### E.17 — 2026-08-23 16:34:09 · `6a8aa259`

```text
Would you please discuss the current status of common graphs literature?
```

### E.18 — 2026-08-23 17:01:52 · `6a8aa259`

```text
The 'strongly common graphs with odd girth are cycles', if the result is as written in the title, can there still be even girth nonbipartite graphs? Why is this completely classifying non-bipartite strongly common graphs?
```

## Conversation `6a8aaa3d` — “Check Edge Robustness” (campaign)

- 2026-08-23 17:07:26 → 2026-08-23 17:47:24; models: gpt-5-6-pro×9, gpt-5-6-thinking×4; 16 messages on the final path
- edge-robustness audit of the chordal-entropy theorem (GLLV comparison); insert not kept
- Delivered file: `[Patched LaTeX source](sandbox:/mnt/data/chordal_entropy_extension_with_robustness.tex)`
- Delivered file: `[Compiled PDF](sandbox:/mnt/data/chordal_entropy_extension_with_robustness.pdf)`
- Delivered file: `[Standalone LaTeX insertion](sandbox:/mnt/data/pendant_forest_robustness_insert.tex)`

### E.19 — 2026-08-23 17:07:23 · `6a8aaa3d` · attachments: chordal_entropy_extension(1).tex, on-tripartite-common-graphs.pdf

```text
In this article, we prove that some condition implies that the graph satisfies some Goodman-style lower bound on the homomorphism density. 
On the paper by Grzesik, Lee, Lidický, and Volec, they have some robustness result, not just exact condition, that when it is allowed to add edges. Would you please check their statement, and see if we can extend this proof by allowing some edge robustness?

For some context, this argument often fails on general chordal graph. For instance, adding 20 edges each vertex to triangle makes the graph still chordal, but creates counterexample for the conjectured lower bound. So this theory is not robust on the pendant edge. If we can give some bound on the number... we it would be much more strong result.
```

### E.20 — 2026-08-23 17:46:35 · `6a8aaa3d`

```text
If I'm understanding correctly, you didn't prove tighter result or something similar, but interpreted the existing result in terms of robustness, right? In other words, the graphs that can be proven to satisfy this Goodman style lower bound by entropic theorem is still same. Right?
```

## Conversation `6a8ab440` — “Count Graphs Satisfying Conditions” (campaign)

- 2026-08-23 17:51:14 → 2026-08-23 17:52:38; models: gpt-5.6-sol-wm×8; 9 messages on the final path
- count of catalogue rows covered by the chordal-entropy theorem (30, or 29 connected)

### E.21 — 2026-08-23 17:51:10 · `6a8ab440` · attachments: chordal_entropy_extension(2).tex

```text
Consider graphs with at most 6 vertices, no isolated edge or isolated vertex (they wouldn't affect the lower bound stated in the file), that are non-bipartite (which is target of the lower bound stated in the file). 
How many graphs satisfy the condition stated in the file among them?
```

## Conversation `6a8ab684` — “Analyze Extremal Ramsey Graphs” (satellite)

- 2026-08-23 18:01:16 → 2026-08-23 18:17:14; models: gpt-5.6-sol-wm×64; 65 messages on the final path
- extremal Ramsey graphs lookup (adjacent)

### E.22 — 2026-08-23 18:01:11 · `6a8ab684` · attachments: 2206.04036v3.pdf

```text
This paper describes some heuristic to build some extremal graphs for ramsey multiplicity. Would you please read this paper, and not just the result, try to find deep mathematical meaning of the graphs constructed, possibly supplying 'reason' such graphs are optimal (or possibly optimal)?
```

## Conversation `6a8afa8c` — “Prove Atlas Graph Inequality” (campaign)

- 2026-08-23 22:50:05 → 2026-08-24 15:58:40; models: gpt-5-6-pro×37, gpt-5-6-thinking×5; 47 messages on the final path
- the Codex-drafted CHORDAL_OPEN_CASES brief with 4 PDF attachments (Atlas 181/157/130); no closure

### E.23 — 2026-08-23 22:50:01 · `6a8afa8c` · attachments: atlas160_k4_paw_edge_supporting_plane.pdf, chordal_entropy_extension(1).pdf, atlas178_half_degree_weighted_k4.pdf, paw_triangle_edge_cones.pdf

```text
**# ChatGPT Pro proof task: three unresolved chordal Atlas graphs**

**## Instructions to the proof model**

Treat this entire document as a research request and begin the mathematical

work immediately. Do not merely summarize the prompt or return a list of

possible approaches.

Your primary task is to prove or refute at least one of the three

Goodman-style graphon inequalities below. Start with the concrete Atlas 181

lemma

\\[

t(H\_{181},W)\stackrel{?}{\geq}(2p-1)^2t(K\_4,W),

\qquad p=t(K\_2,W)\geq\frac23.

\\]

If it is true, give a complete proof for arbitrary graphons. If it is

false, give an explicit weighted finite-step graphon and verify the

violation exactly. If you cannot settle it, do not stop at saying that the

problem is difficult: prove the strongest correct intermediate lemma you

can, identify the exact remaining implication, and then try Atlas 157 or

Atlas 130.

**### PDFs supplied with this prompt**

Read the attached files before proving anything that depends on them.

You may cite a proved result from an attachment as a lemma, but identify

its precise statement and verify that all of its hypotheses apply here.

1\. **\*\*Required:\*\*** \<code>chordal\_entropy\_extension.pdf\</code>. This contains

   the proved common-\\(K\_r\\)-law entropy theorem, its deficit formulation,

   the Moon--Moser suffix inequalities, and the PAVA bound.

2\. **\*\*Recommended for Atlas 157:\*\***

   \<code>paw\_triangle\_edge\_cones.pdf\</code>. This is the accepted proof

   covering Atlas 49, obtained from Atlas 157 by deleting its leaf.

3\. **\*\*Optional supporting-plane references:\*\***

   \<code>atlas160\_k4\_paw\_edge\_supporting\_plane.pdf\</code> and

   \<code>atlas178\_half\_degree\_weighted\_k4.pdf\</code>. These show two

   successful weighted-\\(K\_4\\) arguments for nearby classified graphs.

The prompt itself contains the graph definitions, targets, and proposed

reductions, so no classification spreadsheet or Atlas software is needed.

If only one PDF can be attached, attach

\<code>chordal\_entropy\_extension.pdf\</code> and work on Atlas 181.

**## Purpose**

This note isolates the three chordal graphs still not fully classified for

\\[

t(H,W)\geq \Phi\_H(p)

:=(1-p)^{v(H)}\chi\_H\\!\left(\frac1{1-p}\right),

\qquad p=t(K\_2,W),

\\]

throughout the required Turán interval

\\[

p\geq 1-\frac1{\chi(H)-1}.

\\]

They are NetworkX Graph Atlas 130, 157, and 181. All statements sought

below are for arbitrary graphons and homomorphism densities.

A graphon is a symmetric measurable function

\\(W:[0,1]^2\to[0,1]\\). For a finite graph \\(F\\),

\\[

t(F,W)=

\int\_{[0,1]^{V(F)}}

\prod\_{uv\in E(F)}W(x\_u,x\_v)

\prod\_{u\in V(F)}dx\_u.

\\]

Thus all densities here are ordinary homomorphism densities, not

injective densities.

**## Notation and the existing theorem**

Put

\\[

c\_1=1,\qquad c\_2=p,\qquad c\_3=2p-1=\:r,\qquad c\_4=3p-2=\:s.

\\]

For a chordal graph, choose a clique tree and define

\\[

b\_j=

\\#\\{\text{maximal cliques of size at least }j\\}

-\\#\\{\text{clique-tree separators of size at least }j\\}.

\\]

Then

\\[

\Phi\_H(p)=\prod\_j c\_j^{b\_j}.

\\]

The current theorem proves this target whenever

\\[

b\_1\leq b\_2\leq\cdots\leq b\_{\omega(H)}.

\\]

For an arbitrary chordal graph, pool-adjacent-violators replaces \\(b\\) by

its nondecreasing pooling \\(\bar b\\) and proves only

\\[

t(H,W)\geq \Psi\_H(p):=\prod\_j c\_j^{\bar b\_j}

\leq \Phi\_H(p).

\\]

The loss caused by that pooling is the exact obstruction in all three cases.

**## Exact census**

\| Atlas | graph6 | Description | \\(\chi\_H(x)\\) | Required target |

\|---:|---|---|---|---|

\| 130 | \<code>E{CW\</code> | Two triangles joined by one bridge | \\(x(x-1)^3(x-2)^2\\) | \\(p^3r^2,\ p\geq1/2\\) |

\| 157 | \<code>E\~&#96;\_\</code> | A \\(K\_4\\), a triangle page on one clique edge, and a leaf at a clique vertex outside that edge | \\(x(x-1)^2(x-2)^2(x-3)\\) | \\(p^2r^2s,\ p\geq2/3\\) |

\| 181 | \<code>E^mG\</code> | A \\(K\_4\\) with triangle pages on two opposite clique edges | \\(x(x-1)(x-2)^3(x-3)\\) | \\(pr^3s,\ p\geq2/3\\) |

The respective edge counts are 7, 9, and 10.

For an explicit six-vertex input, the Atlas labelings have edge sets

\\[

\begin{aligned}

E(H\_{130})&=\\{01,02,03,12,34,35,45\\},\\\\

E(H\_{157})&=\\{01,02,03,04,12,13,15,23,25\\},\\\\

E(H\_{181})&=\\{02,03,04,05,12,13,23,24,34,45\\}.

\end{aligned}

\\]

**## Where the current entropy proof stops**

**### Atlas 130**

The maximal clique sizes are \\((3,3,2)\\); the two clique-tree separators

have size \\(1\\). Thus

\\[

b=(1,3,2).

\\]

The jump \\(3>2\\) violates monotonicity. Pooling gives

\\[

\bar b=(1,5/2,5/2)

\quad\Longrightarrow\quad

t(H\_{130},W)\geq p^{5/2}r^{5/2}.

\\]

The target exceeds this bound by

\\[

\frac{\Phi\_{130}}{\Psi\_{130}}=\sqrt{\frac p r}.

\\]

**### Atlas 157**

The maximal clique sizes are \\((4,3,2)\\). The \\(K\_3\\) page meets the

\\(K\_4\\) in an edge, and the maximal leaf edge meets it in a vertex. Hence

\\[

b=(1,2,2,1).

\\]

Pooling gives

\\[

\bar b=(1,5/3,5/3,5/3)

\quad\Longrightarrow\quad

t(H\_{157},W)\geq (prs)^{5/3}.

\\]

The missing factor is

\\[

\frac{\Phi\_{157}}{\Psi\_{157}}

\=\left(\frac{pr}{s^2}\right)^{1/3}.

\\]

It diverges as \\(p\downarrow2/3\\), so a uniform constant-factor

improvement of the pooled theorem cannot settle the threshold region.

**### Atlas 181**

The maximal clique sizes are \\((4,3,3)\\), and both separators have size

\\(2\\). Therefore

\\[

b=(1,1,3,1).

\\]

Pooling gives

\\[

\bar b=(1,1,2,2)

\quad\Longrightarrow\quad

t(H\_{181},W)\geq pr^2s^2.

\\]

The missing factor is

\\[

\frac{\Phi\_{181}}{\Psi\_{181}}=\frac r s,

\\]

which again diverges as \\(p\downarrow2/3\\).

**## Atlas 130: a surplus-controlled complement correlation**

Define the rooted triangle density

\\[

\tau(x)=\int W(x,a)W(x,b)W(a,b)\\,da\\,db,

\qquad

T=\int\tau(x)\\,dx=t(K\_3,W).

\\]

Then

\\[

t(H\_{130},W)

\=\int\tau(x)W(x,y)\tau(y)\\,dx\\,dy.

\\]

Goodman's inequality gives \\(T\geq pr\\). With \\(U=1-W\\), set

\\[

B:=\int U(x,y)\tau(x)\tau(y)\\,dx\\,dy.

\\]

We have the exact identity

\\[

t(H\_{130},W)=T^2-B.

\\]

Writing the Goodman surplus as

\\[

\delta:=T-pr\geq0,

\\]

the desired Atlas 130 bound follows from the concrete statement below.

\> **\*\*Atlas 130 target lemma.\*\*** For every graphon with \\(p\geq1/2\\),

\> \\[

\> B-(1-p)T^2\leq 2p^2r\delta+p\delta^2.

\> \\]

Indeed,

\\[

T^2-B

\geq pT^2-2p^2r\delta-p\delta^2

\=p^3r^2.

\\]

The tempting stronger claim \\(t(H\_{130},W)\geq pT^2\\) should not be

assumed: existing finite-step numerical diagnostics found violations.

The useful object is the Goodman surplus, not unconditional positive

correlation of the rooted triangle weights across an edge.

Possible routes:

1\. Express \\(\delta\\) through complement-degree variance and mixed

   triangles, then control the excess \\(B-(1-p)T^2\\) by those terms.

2\. Find a supporting plane for the rooted variables \\(d=T\_W1\\),

   \\(a=T\_Wd\\), and \\(\tau\\).

3\. Average quantitative certificates associated with the seven positive

   edge deletions of Atlas 130.

4\. Search directly for a flag-SOS certificate for the target lemma.

**## Atlas 157: retain the surplus from Atlas 49**

Label the \\(K\_4\\) vertices \\(a,b,c,d\\). Let the page vertex be adjacent

to \\(b,c\\), and attach the leaf at \\(a\\). Define

\\[

C(x,y)=\int W(x,z)W(y,z)\\,dz.

\\]

Writing \\(K\_4(a,b,c,d)\\) for the product of the six clique-edge factors,

integrating out the page and leaf gives

\\[

t(H\_{157},W)

\=\int K\_4(a,b,c,d)\\,C(b,c)d(a)\\,da\\,db\\,dc\\,dd.

\\]

Deleting the leaf gives Atlas 49. Put

\\[

J:=t(H\_{49},W)

\=\int K\_4(a,b,c,d)C(b,c)\\,da\\,db\\,dc\\,dd.

\\]

The accepted Atlas 49 bound is

\\[

J\geq pr^2s.

\\]

Let

\\[

\Gamma\_{49}:=J-pr^2s\geq0.

\\]

There is an exact gap decomposition

\\[

t(H\_{157},W)-p^2r^2s

\=p\Gamma\_{49}

+\int K\_4(a,b,c,d)C(b,c)\bigl(d(a)-p\bigr)\\,da\\,db\\,dc\\,dd.

\\]

Thus the following rooted strengthening of the Atlas 49 proof suffices.

\> **\*\*Atlas 157 target lemma.\*\*** For every graphon with \\(p\geq2/3\\),

\> \\[

\> \int K\_4(a,b,c,d)C(b,c)\bigl(d(a)-p\bigr)\\,da\\,db\\,dc\\,dd

\> \geq-p\Gamma\_{49}.

\> \\]

This is deliberately weaker than nonnegative covariance. Diagnostics

indicate that \\(t(H\_{157},W)\geq p\\,t(H\_{49},W)\\) is false, while the

Atlas 49 surplus appears capable of paying for the covariance deficit.

Possible routes:

1\. Reopen the Atlas 49 cone proof and retain its quantitative remainder.

2\. Root that proof at \\(a\\), seeking a supporting plane involving

   \\(d(a)\\), \\(T\_Wd(a)\\), and the rooted \\(K\_4\\) density.

3\. Adapt the weighted-\\(K\_4\\) supporting-plane arguments already used for

   Atlas 160 and 178.

**## Atlas 181: two pages on opposite clique edges**

Label the \\(K\_4\\) vertices \\(a,b,c,d\\), and put the two page vertices on

the opposite edges \\(ab\\) and \\(cd\\). Then

\\[

t(H\_{181},W)

\=\int K\_4(a,b,c,d)C(a,b)C(c,d)\\,da\\,db\\,dc\\,dd.

\\]

Let \\(t\_4=t(K\_4,W)\\). The clique-density bound gives

\\[

t\_4\geq prs.

\\]

Either of the next two statements would prove Atlas 181.

\> **\*\*Minimal Atlas 181 page lemma.\*\***

\> \\[

\> t(H\_{181},W)\geq r^2t\_4,\qquad p\geq2/3.

\> \\]

\> **\*\*Stronger opposite-page conjecture.\*\***

\> \\[

\> p^2t(H\_{181},W)\geq t(K\_4,W)t(K\_3,W)^2.

\> \\]

The stronger statement implies the minimal one by

\\(t(K\_3,W)\geq pr\\). Both have equality on balanced complete multipartite

graphons. Existing small random step-graphon diagnostics found no

violation, but this is not a proof.

Possible routes:

1\. Under the \\(K\_4\\)-weighted probability law, prove a positive-correlation

   or surplus-corrected correlation inequality for codegrees on opposite

   edges.

2\. Pair the opposite edges, apply Cauchy--Schwarz, and then use the

   graphon Moon--Moser recurrence.

3\. Find a two-coordinate supporting plane for \\(C(a,b)C(c,d)\\) under the

   \\(K\_4\\)-weighted law.

4\. Glue one \\(K\_4\\) law and two \\(K\_3\\) laws while retaining the mismatch

   of their edge marginals as a relative-entropy term.

Atlas 181 is the cleanest first target because of its symmetry and

one-line sufficient lemma.

**## Possible extensions of the chordal entropy method**

The existing proof assigns every clique bag a marginal of one uniform

\\(K\_{\omega(H)}\\)-homomorphism law. Separator consistency is then automatic,

but the argument sees only maximum-clique entropy deficits. A downward

jump in \\(b\\) leaves a coefficient with the wrong sign, and PAVA removes

exactly the factor displayed above.

Three related extensions may recover it.

**### 1. Several bag laws and a separator-mismatch penalty**

Use the natural uniform homomorphism law for each maximal clique size.

Their separator marginals differ, so seek a gluing inequality of the form

\\[

\log\operatorname{hom}(H,G)

\geq

\sum\_i H(\mu\_i)-\sum\_e H(\nu\_e)-\sum\_e\mathcal D\_e,

\\]

where \\(\mathcal D\_e\\) is a relative-entropy or transport cost measuring

the disagreement between the two separator laws. The needed new theorem

would upper-bound the total mismatch cost by a Moon--Moser-type deficit.

The mismatches are concrete:

\- Atlas 130: triangle vertex marginals versus endpoint marginals of a

  uniform edge;

\- Atlas 157: a \\(K\_4/K\_3\\) edge mismatch and a \\(K\_4/K\_2\\) vertex

  mismatch;

\- Atlas 181: two identical \\(K\_4/K\_3\\) edge mismatches on opposite edges.

The symmetry of Atlas 181 may let its two penalties combine.

**### 2. Interpolate between the common law and natural smaller-clique laws**

Mix the consistent marginal inherited from the uniform maximum-clique law

with the natural uniform law for each smaller clique. Optimize the mixing

parameter so that the gained clique ratio pays for separator

inconsistency. The exact gains required are

\\[

\sqrt{p/r},\qquad

(pr/s^2)^{1/3},\qquad

r/s

\\]

for Atlas 130, 157, and 181, respectively.

**### 3. Add one graph-specific deficit inequality before pooling**

Keep the common maximum-clique law, but supplement monotonicity and the

Moon--Moser suffix bounds with one inequality tailored to the single

downward jump:

\- compare the final two deficits for \\(b=(1,3,2)\\);

\- control the \\(K\_4/K\_3\\) jump for \\(b=(1,2,2,1)\\);

\- exploit the two opposite edge separators for \\(b=(1,1,3,1)\\).

A theorem for just these three clique-tree shapes would settle every

currently open chordal graph on at most six vertices.

**## Checks for any proposed proof**

1\. Use homomorphism densities, not injective densities.

2\. Cover arbitrary measurable graphons, including zero degree and zero

   clique-density cases.

3\. Handle \\(p=1/2\\), \\(p=2/3\\), and every division by \\(p,r,s\\)

   separately.

4\. Check equality on balanced complete multipartite graphons and on

   \\(W=1\\).

5\. Test every proposed correlation lemma on weighted two- and three-step

   graphons before relying on it.

6\. If the argument is first proved for finite graphs, include an explicit

   graphon approximation passage.

**## Suggested order of attack**

1\. Atlas 181: prove or refute

   \\(t(H\_{181},W)\geq(2p-1)^2t(K\_4,W)\\).

2\. Atlas 157: extract a quantitative rooted remainder from the Atlas 49

   proof and establish the covariance-with-slack lemma.

3\. Atlas 130: bound its complement correlation excess by the Goodman

   surplus using a supporting plane or exact flag-SOS certificate.

4\. Abstract the successful mechanism into a chordal entropy extension.

**## Required deliverable**

Work on the problem now, without asking preliminary questions. Organize the

response as follows.

1\. **\*\*Atlas 181 verdict.\*\*** State whether the minimal page lemma is proved,

   refuted, or still conditional.

2\. **\*\*Proof or counterexample.\*\*** Supply every substantive inequality. A

   counterexample must specify rational block masses and a rational

   symmetric edge-probability matrix, then compute both sides exactly.

3\. **\*\*Deduction of the original target.\*\*** If the page lemma is proved, show

   explicitly how \\(t(K\_4,W)\geq p(2p-1)(3p-2)\\) yields

   \\(t(H\_{181},W)\geq p(2p-1)^3(3p-2)\\).

4\. **\*\*Audit.\*\*** Treat \\(p=2/3\\), \\(p=1\\), zero clique density, and every

   division by \\(p,r,s\\). Identify all equality cases established by the

   proof.

5\. **\*\*Further progress.\*\*** Explain precisely whether the successful argument

   extends to the Atlas 157 covariance-with-slack lemma or the Atlas 130

   Goodman-surplus lemma. If Atlas 181 remains unresolved, attempt one of

   those two instead and report the strongest rigorous partial result.

Do not assume a general clique-tree product inequality, positive

correlation under a clique-weighted law, or a separator-mismatch entropy

bound without proving it. Computation may be used to discover a statement,

but the final proof must be analytic or an exact finite certificate.
```

*Note:* This is `CHORDAL_OPEN_CASES_RESEARCH_BRIEF.md`, drafted by Codex in session `01a02ea5` turn 1 (23 Aug 22:13–22:31, prompt D.77) together with its `chatgpt_pro_attachments/`; the user pasted it 19 minutes after the Codex turn finished, attaching the four PDFs the brief prescribes.

### E.24 — 2026-08-24 11:45:49 · `6a8afa8c`

```text
I see. Would you please push more to have arbitrary graphon proof?
```

### E.25 — 2026-08-24 15:56:51 · `6a8afa8c`

```text
Would you please discuss what results you got after my question, "I see. Would you please push more to have arbitrary graphon proof?"?
```

## Conversation `6a8c6dfb` — “Neural Optimization Bounds” (satellite)

- 2026-08-25 01:19:33 → 2026-08-25 03:55:55; models: gpt-5.6-sol-wm×123; 129 messages on the final path
- neural-extremal research prospectus, 22->26 pages (new-directions thread, night of the /goal run)
- Delivered file: `[Download neural_extremal_research_programs.tex](sandbox:/workspace/scratch/97b18c74085d/neural_extremal_research_programs.tex)`
- Delivered file: `- [LaTeX source](sandbox:/workspace/scratch/97b18c74085d/neural_extremal_research_programs.tex)`
- Delivered file: `- [Compiled PDF](sandbox:/workspace/scratch/97b18c74085d/build/neural_extremal_research_programs.pdf)`

### E.26 — 2026-08-25 01:19:28 · `6a8c6dfb`

```text
Recently, we are working on solving some discrete problem with continuous optimisation.
Simple instance we can think of for this is where Grothendieck inequality comes from: discrete problem is relaxed with continuous optimisation which is directly solved, and we somehow round them. 

What my approach worked is graphon. I parameterised graphon by neural network with some specific architecture, trained a lot, then see how its value is and how it looks like. This would naively generalise to digraphon / tournamenton / hypergraphon / permuton / etc...

I have these extensions in mind, actually, I have done some of them, and have some clear idea for them.
But this time, I have different question. Will there be some interesting problem that we can tackle with similar idea? One object is optimisation theory. In optimisation theory, we often ask via SDP to see what is the worst convex function that it can badly behave. Instead, we might design convex neural network (which is well-studied) and optimise it to match the given points / derivatives and minimise the performance, to obtain some kind of upper bound. 

Is there other problems that can work similarly? I'm not sure on this 'lower bound counterpart', somehow both flag algebra and PEP arises in these problem I'm thinking of, but it might not be necessary condition.
```

### E.27 — 2026-08-25 02:27:01 · `6a8c6dfb`

```text
1, 2, 3, 5: These seems quite specific problems. So given new instance, we solve, and get some approximate solution. In this case, if our methodology should work as if 'worst case algorithm', that works really well on most of the problem. This would require us to even prove correctness of this algorithm. I'm not sure if it would work well.

4, 6, 7, 8: Not very bad, but I think we need many problems to tackle with. I like 7 and 8 as you suggested some functional inequalities. I'm not sure what our exact goal is. In graphon (or extremal graph theory), there are tons of conjectures that is even unknown. For functional inequalities, it seems... our goal is narrowing some interval that contains specific constant?
```

### E.28 — 2026-08-25 03:19:30 · `6a8c6dfb`

```text
I see. Would you please write a latex document, one section per your suggested disciplines, concrete problems to be tackled? For functional inequality, consider more than only Strichartz. 
When discussing problems, write why such problems are also interesting, mostly by its mathematical usefulness, what kind of problems are solved with it.
```

### E.29 — 2026-08-25 03:43:38 · `6a8c6dfb`

```text
I also liked one paper that tried to find some... initial condition? for some system, that results in some singularity. Is that research also based on NN? If so, would you please add one section that considers similar, PDE condition etc learning for some specific case finding?
```

### E.30 — 2026-08-25 03:44:23 · `6a8c6dfb`

```text
I also liked one paper that tried to find some... initial condition? for some system, that results in some singularity. Is that research also based on NN? If so, would you please add one section that considers similar, PDE condition etc learning for some specific case finding? Also, please give me both tex and pdf.
```

## Conversation `6a8d6696` — “Flag Algebra Encoding” (satellite)

- 2026-08-25 18:57:42 → 2026-08-25 19:08:31; models: gpt-5.6-sol-wm×45; 46 messages on the final path
- flag-algebra encoding of partially integrated Sidorenko objects (C5/Moebius thread)

### E.31 — 2026-08-25 18:57:38 · `6a8d6696`

```text
Often in Sidorenko's inequality for Mobius ladder, we encode it as some kind of 3-input object that partially integrates the edge and use it to represent the integral. 
Q: Would you please discuss multiple such instances, and see if themselves can be encoded as if they are some combinatorial object, so that can be handled by flag algebra?

So Sidorenko's inequality on Mobius ladder has 15 edges. So encoding it would require us to make 30 vertex atlas, which is largely infeasible. 
Instead, if we somehow write 
t(M, W) = t(???, W')
where W'(x, y, z) gets three input, we can think of it as if it is kind of 3-graph (it is not). Then if we can build flag algebra only for it, we might be able to reduce the number of edges, size, etc, to make problem feasible. Can this work?
```

## Conversation `6a8e68cc` — “Check path Sidorenko citation” (satellite)

- 2026-08-26 13:18:32 → 2026-08-26 13:22:14; models: gpt-5.6-sol-wm×18; 19 messages on the final path
- path-Sidorenko (Blakley-Roy) citation check (C5 thread)

### E.32 — 2026-08-26 13:18:28 · `6a8e68cc`

```text
The paper by Mulholland and Smith proves that
for v a k dim vector, M be a k*k matrix, with all elements nonnegative, and u symmetric. 
Then, 
(v^T u^n v) (v^T v)^{n-1} >= v^T u v^n
with equality if and only if v is a latent vector of u.

Okay, I'm not sure what authors indicate by v^n... but according to some writing by AI, it was cited as a reference to the path sidorenko inequality. 
I am not sure if it is correct, for instance, Blakely-Roy is, in my opinion, is more general argument we use for the Path sidorenko. Would you please check if this is correct citation?
```


# Prehistory (before 2026-08-18, one line each)

These conversations precede the gap window; they are listed to locate the origin of the campaign's input documents and standing methods. They are not part of the addendum's session tables.

- `6a1d1004` — “Graph Conjecture Proof Request”, 2026-06-01 13:52 → 2026-06-04 15:41
- `6a1e0305` — “Graph Inequality Conjecture”, 2026-06-02 07:09 → 2026-06-04 14:29
- `6a212973` — “Turan graph non-optimality”, 2026-06-04 16:29 → 2026-06-15 19:05
- `6a263152` — “Inequality on Homomorphism Density”, 2026-06-08 12:04 → 2026-06-08 14:13
- `6a26317d` — “Inequality on Homomorphism Density”, 2026-06-08 12:05 → 2026-06-08 14:11
- `6a28a58d` — “Relaxing Proof Constraints”, 2026-06-10 08:45 → 2026-06-10 11:24
- `6a2a36d7` — “Graph Homomorphism Conjecture”, 2026-06-11 13:17 → 2026-06-12 16:43
- `6a2fb3c6` — “Graph Inequality Conjecture”, 2026-06-15 17:11 → 2026-06-25 15:38
- `6a43eec7` — “Research Direction for Homomorphism”, 2026-07-01 01:28 → 2026-07-02 16:27
- `6a46a2fc` — “Graph Conjecture Operations”, 2026-07-03 02:42 → 2026-07-03 22:19
- `6a51de48` — “Graph Homomorphism Inequality”, 2026-07-11 15:10 → 2026-07-14 18:25
- `6a58d671` — “Human Verifiable Proof”, 2026-07-16 22:02 → 2026-07-17 15:47
- `6a60e66f` — “Universal proof for odd cycles”, 2026-07-23 00:49 → 2026-07-23 12:09
- `6a62426a` — “Chordal Graph Proof”, 2026-07-24 01:33 → 2026-07-24 09:49
- `6a674743` — “Lower Bound Chordal Graph Edges”, 2026-07-27 20:55 → 2026-07-27 21:11
- `6a68c4d5` — “Chordal Graph Naming”, 2026-07-29 00:03 → 2026-07-29 00:09
- `6a6b9ee2` — “Unproven Conjecture in Graph Theory”, 2026-07-31 03:58 → 2026-07-31 16:31
- `6a795e31` — “Branch · Upper Bound Gap Analysis”, 2026-08-10 14:14 → 2026-08-11 10:41
- `6a7c38c7` — “Graph Bounds and Relaxation”, 2026-08-12 18:11 → 2026-08-13 10:37
- `6a7d5b2a` — “Branch · Graph Bounds and Relaxation”, 2026-08-13 14:50 → 2026-08-13 16:58
- `6a7c89c3` — “Fisher's theorem and generalization”, 2026-08-12 23:57 → 2026-08-17 20:08
