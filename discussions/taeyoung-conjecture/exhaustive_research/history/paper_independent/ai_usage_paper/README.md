# AI-usage companion paper

This directory contains the observational companion paper for the six-vertex
graphon classification.

Regenerate derived material from the repository root:

```powershell
python history/paper_independent/ai_usage_paper/scripts/generate_metrics.py
python history/paper_independent/ai_usage_paper/scripts/generate_excerpts.py
python history/paper_independent/plot_completion_curve.py
python history/paper_independent/ai_usage_paper/scripts/check_manuscript.py
```

Build from this directory:

```powershell
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The paper is observational.  It does not claim that effort settings, model
families, or workflow components caused the observed differences.  Appendix B
contains curated source quotations with stable labels; the main text uses
professional paraphrases.
