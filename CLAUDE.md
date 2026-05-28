# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repo is

A LaTeX-only research repository for the project *Deep Learning for Extremal Combinatorics*. There is **no source code** here — the neural-network implementation that produces the figures lives in a separate (unreferenced) codebase. This repo only tracks (1) the NeurIPS 2026 manuscript and (2) standalone mathematical progress notes that feed back into the paper.

Two top-level subtrees, each independent:

- [papers/neurips26/](papers/neurips26/) — the main submission [neurips2026.tex](papers/neurips26/neurips2026.tex) (~1550 lines, single-file with `\input{checklist.tex}` for the NeurIPS checklist). Bibliography is in [references.bib](papers/neurips26/references.bib). The repo bundles `neurips_2026.sty`, `algorithm.sty`, `algorithmic.sty`, `fancyhdr.sty` so the build is self-contained.
- [discussions/lower-bound-shape/](discussions/lower-bound-shape/) — [two_problems_progress_report.tex](discussions/lower-bound-shape/two_problems_progress_report.tex), an `amsart`-class working note that tracks the analytical state of two open problems (the six-vertex graph at edge density $1-1/k$, and the convex/concave classification of $f_F(x)=\min\{t(F,W):t(K_2,W)=x\}$). When experiments in the paper turn up a candidate construction, the mathematical analysis of that construction tends to land here first.

The two trees share concepts (graphons, homomorphism densities $t(H,W)$, the families **(P1)** generalised Turán and **(P2)** large-deviation variational problems) but no files — edits cross over only by hand.

## Figures and the figures/ vs new_figures/ split

[papers/neurips26/figures/](papers/neurips26/figures/) holds the older figure set (used by the prior ICML submission [icml26/icml26-submission.pdf](papers/neurips26/icml26/)). [papers/neurips26/new_figures/](papers/neurips26/new_figures/) holds the current NeurIPS 2026 figures. **`neurips2026.tex` references `new_figures/` for nearly every plot**; `figures/` is kept around for the shared `colorbar.png` and for figures not yet regenerated. When adding a new figure, place it in `new_figures/` unless you have a reason to mix sets. Figure filenames encode `<pattern>_<edge-density-as-percent>.png` (e.g. `k3_67.png` = $K_3$ at $p=2/3$, `c5_80.png` = $C_5$ at $p=4/5$).

## Building

The repo is configured for VS Code's LaTeX Workshop with `latexmk` and auto-build on save (see [papers/neurips26/.vscode/](papers/neurips26/.vscode/)). For manual builds from `papers/neurips26/`:

```sh
pdflatex -interaction=nonstopmode neurips2026.tex
bibtex neurips2026
pdflatex -interaction=nonstopmode neurips2026.tex
pdflatex -interaction=nonstopmode neurips2026.tex
```

`latexmk -pdf neurips2026.tex` is equivalent and is what the IDE recipe uses. All LaTeX auxiliary files (`*.aux`, `*.bbl`, `*.log`, `*.pdf`, etc.) are gitignored, so a stale committed `neurips2026.pdf` is not expected — if you see one locally it is your own build.

The progress note builds the same way from its own directory (`pdflatex two_problems_progress_report.tex`); it uses `amsart` and has no bibliography.

## Editing conventions to preserve

- **Authors are anonymised.** The `\author{}` block in `neurips2026.tex` is intentionally `Anonymous Authors` — do not fill it in. The NeurIPS style hides authors unless `[final]` is passed to `\usepackage{neurips_2026}`; do not switch to `[final]` or `[preprint]` without being asked.
- **Inline-comment macros for authors.** `\TODO{...}`, `\tk{...}` (olive), `\hy{...}` (blue), `\jb{...}` (orange), `\jl{...}` (purple) render coloured `[INITIALS: …]` notes inline. Leave existing ones alone unless asked; use the matching colour if you add one on behalf of a specific author. `\fix` / `\new` produce margin tags.
- **`todonotes` is enabled, not disabled** (the `[disable]` line is commented out). Margin tags will appear in builds; that is intentional for the working draft.
- **`cleveref` is configured with project-specific short forms.** Use `\Cref{...}` / `\cref{...}`, not `\ref{...}`. Sections render as `§N`, figures as `Fig.`, tables as `Tab.` — these are set in the preamble; don't override at the call site.
- **Notation.** $H$ is the pattern graph, $W$ a graphon, $t(H,W)$ the homomorphism density, $h_q(W)$ the integrated KL functional. The two problem families are referred to as **(P1)** and **(P2)** in bold throughout — keep that labelling consistent when adding cross-references. $K_n$, $K_{1,n}$, $C_n$ are defined in the Background section; reuse, don't redefine.
- **`\providecommand{\yrcite}`** in the preamble exists so source originally written for the ICML style still compiles under `neurips_2026.sty`. Don't remove it.

## When you change the paper

The introduction, abstract, and §3 (method) carry the load-bearing claims: the multi-scale sinusoidal residual architecture, the embedded constraint solver differentiated by implicit differentiation, the symmetry-aware Monte Carlo estimators, and the empirical claims that the method (a) rediscovers known optima for **(P1)**, (b) finds a new family of extremal structures for a six-vertex graph, and (c) improves on Lubetzky–Zhao for the $K_3$ upper tail in **(P2)**. Changes to any of these need to stay consistent across abstract, intro, and method section. The appendices ([sec:experimentdetails](papers/neurips26/neurips2026.tex#L881), [sec:oddcycleconjecture](papers/neurips26/neurips2026.tex#L962), ablation in [§F](papers/neurips26/neurips2026.tex#L1374)) are independent and can be edited in isolation.
