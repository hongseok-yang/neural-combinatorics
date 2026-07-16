#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

python3 -m py_compile \
  regionII_scalar_checker.py \
  zoneB_certifier.py \
  zoneC_certifier.py

python3 zoneB_certifier.py
python3 zoneC_certifier.py
python3 regionII_scalar_checker.py --scan

for _ in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error \
    regionII_corrected_solution.tex >/dev/null
done

echo "All exact certificates, regression checks, and LaTeX compilation passed."
