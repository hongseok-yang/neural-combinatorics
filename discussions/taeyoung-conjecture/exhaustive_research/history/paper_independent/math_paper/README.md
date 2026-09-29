# Mathematics paper

The manuscript is main.tex; the compiled draft is main.pdf.

Regenerate and check the appendices from this directory with:

    python scripts/generate_classification.py
    python scripts/verify_negative_witnesses.py
    python scripts/generate_verification_table.py
    latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
    python scripts/check_manuscript.py

The generators use project sources outside this directory but write only to
generated/. They do not invoke Lean or any certificate verifier.
